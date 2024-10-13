
# Our approach

In this document, we describe

1. A sound simplified abstraction (a **simplified model**) of the underlying architecture, which requires software to manage pagetables in a safe way.

2. Instrumentation we have written, as part of the pKVM sources, which can automatically check that the steps taken by pKVM are safe, according to the abstraction.

We build this as
a reification of the logical state of the page tables in the break-before-make protocol under assumptions of well-disciplined code.
This reification enables us to detect violations of the break-before-make protocol
and related invariants.

The core of our approach is that:

1. We formally represent the progress of a location through the break-before-make protocol via an automaton.

2. In the code of pKVM, we associate, to each physical location that is being used as a page table entry,
its logical automaton state, reified in C.

3. We instrument the code of pKVM: for each instruction that could affect the state of the page tables,
we add a call to the corresponding transition on the reified logical state.

Our automaton is designed to refine the "axiomatic" model
of the Arm-A virtual memory systems architecture (VMSA)
as described in *Relaxed virtual memory in Armv8-A* (published at ESOP 2022).

## Automaton

The page table entry automaton is written as a hierarchical automaton
which keeps track of how far into break-before-make its page table entry is.
At its toplevel, it keeps track whether a page table entry is:

1. `STATE_PTE_VALID`, meaning it contains a valid descriptor.

2. `STATE_PTE_INVALID`, meaning it contains an invalid descriptor and is propagated to all cores.

3. `STATE_PTE_INVALID_UNCLEAN`, meaning it contains an invalid descriptor, but some cores might still see
the old, overwritten valid descriptor.

The point of the automaton is that, for example,
if a page table entry is in the `STATE_PTE_VALID` state of the automaton,
writing a valid descriptor to it (with a different output address)
is a violation of break-before-make.
The instrumentation keeps track of these writes (among other instructions),
and flags such a violation as a <span style="color: white; background-color: red;">`BBM valid->valid`</span>.

On the other hand, following break-before-make by
writing an *invalid* descriptor starts the "break",
and transitions to the `STATE_PTE_INVALID_UNCLEAN` state of the automaton.

The rest of the automaton follows the same overall structure:

![Sketch of the page table entry automaton toplevel structure. Each box is a subautomaton. Dashed edges are implicit transitions caused by transitions of other automata.](built_doc/toplevelautomaton.png)

The `STATE_PTE_INVALID_UNCLEAN` state of the automaton
(like the `STATE_PTE_VALID` and `STATE_PTE_INVALID` states) is itself a subautomaton.
Its substructure has two purposes:
it keeps track of how much the invalid descriptor has been pushed to other cores,
and it remembers the old valid descriptor.
In the simplest case, the automaton tracks that the
write of the invalid descriptor is pushed to the MMUs of all cores
by the sequence of a `DSB`, followed by a `TLBI VAE2IS`, and finally another `DSB`
which takes the entry to the `STATE_PTE_INVALID` state.

![Sketch of the invalid-unclean subautomata structure. Each box is a state. Dashed edges correspond to inter-automata transitions in top-level automata.](built_doc/subautomaton.png)

The old valid descriptor is kept because, if it is a table descriptor,
the old page table that it points to remains visible by the MMUs until the "break" is finished.
This is a key way in which the automaton account for the observable relaxed behaviour
of page tables.

Unlike the write of the descriptor, the `DSB`s do not explicitly carry
the information of which addresses they are meant to affect,
so the automata of all the page table entries are affected.

In addition, invalidating a "table" page table entry makes the sub-page table it used to point to
not visible to the MMUs anymore (once the invalidation has been pushed through).
In the automaton, this is modelled as the "implicit" transitions of the figure:
a write to a page table entry changes not only its automaton,
but also, if it is a "table" descriptor, the automata of the page table entries reachable from it.

## Reified state

The toplevel automaton is reified as a C `struct` with an `enum` tag indicating which subautomaton
it is in, with a `union` member for the subautomaton state:
```C
enum automaton_state_kind {
  STATE_PTE_VALID,
  STATE_PTE_INVALID_UNCLEAN,
  STATE_PTE_INVALID,
};
struct sm_pte_state {
  enum automaton_state_kind kind;
  union {
    struct aut_valid valid_state;
    struct aut_invalid invalid_unclean_state;
    struct aut_invalid_clean invalid_clean_state;
  };
};
```

The map from page table location to `sm_pte_state` is kept in the private address space of pKVM.

## Instrumentation

Our instrumentation adds, for each instruction which affects a page table entry
(for example a `WRITE_ONCE(...)`),
a function call that performs the corresponding transition on the automata
(for example `ghost_simplified_model_step_write( ...)`).
This instrumentation is guarded by `#ifdef`s, so that it does not affect the logic of pKVM itself.

For example, part of the instrumentation of `stage2_map_walker_try_leaf`
in [`arch/arm64/kvm/hyp/pgtable.c`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/pgtable.c)
looks as follows:

```C
/* If we're only changing software bits, then store them and go! */
if (!kvm_pgtable_walk_shared(ctx) && !((ctx->old ^ new) & ~KVM_PTE_LEAF_ATTR_HI_SW)) {
  WRITE_ONCE(*ctx->ptep, new);
#if defined(__KVM_NVHE_HYPERVISOR__) && defined(CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL)
  ghost_simplified_model_step_write(WMO_plain, hyp_virt_to_phys(ctx->ptep), new);
#endif
  return 0;
}
```

We similarly instrument `DSB`s, `TLBI`s, as well as operations to relevant special registers via `MSR`/`MRS`, etc.
The transition functions also collect information like the CPU number
and the state of various registers.

The transition functions pushes the automata of all the affected page table entries.
For example, a `DSB` affects all automata:
```C
static void step_dsb(struct ghost_simplified_model_transition trans)
{
	// annoyingly, DSBs aren't annotated with their addresses.
	// so we do the really dumb thing: we go through every pagetable that we know about
	// and step any we find in the right state.
	traverse_all_pgtables(dsb_visitor, &trans.dsb_data);
}
```
where the visitor for a `DSB`,
if said `DSB` is performed by the core that wrote the invalid descriptor,
pushes the `STATE_PTE_INVALID_UNCLEAN` subautomaton from `LIS_unguarded` to `LIS_dsbed`,
and from `LIS_dsb_tlbi_all` out to the `STATE_PTE_INVALID` subautomaton
(and leaves other states unchanged):
```C
void dsb_visitor(struct pgtable_traverse_context *ctxt)
{
	thread_identifier this_cpu = cpu_id();
	struct sm_location *loc = ctxt->loc;

  ...

	// we just did a DSB:
	switch (loc->state.kind) {
	case STATE_PTE_INVALID_UNCLEAN:
		// if the invalid pte wasn't written by this cpu, skip.
		if (! (loc->state.invalid_unclean_state.invalidator_tid == this_cpu)) {
			break;
		}

		if (loc->state.invalid_unclean_state.lis == LIS_unguarded) {
			// if not yet DSBd, then tick it forward
			loc->state.invalid_unclean_state.lis = LIS_dsbed;
		} else if (loc->state.invalid_unclean_state.lis == LIS_dsb_tlbi_all) {
			// if DSB+TLBI'd already, this DSB then propagates that TLBI everywhere,
			// but only if it's the right kind of DSB
			if (dsb_kind == DSB_ish) {
				loc->state.kind = STATE_PTE_INVALID;
				loc->state.invalid_clean_state.invalidator_tid = this_cpu;
			}
		}

		break;
	default:
		;
	}
}
```

## Atomicity and ownership

For each pagetable location, the simplified model tracks a single automata:
capturing the current state of the pagetable entry which corresponds to that location.

In order for this approach to be valid, accesses to pagetable locations must be synchronised,
so that therefore at each update to a pagetable location we can assert a 'current state' exists at all;
additionaly, we require that this location appears in at most one tree of translation tables, in at most one branch, for the same reasons as previously given.
This, in effect, requires trees rather than DAGs more generally for the translation tables,
and prevents sharing of translation table entries between different pagetables.

Furthermore, writes to pagetable entries in a tree may require inspecting or updating the automata of entries below it in the tree,
so in those cases we must ensure synchronisation between the different levels in the same tree.

The simplified model enforces both of these concerns by explicitly encoding a locking discipline:
each entry is associated with a tree (a root),
each root is associated with a lock,
accesses to pagetables must be done while holding the lock for that tree's root,
entries may only be disassociated with a root once properly invalidated and cleaned.

# Connection to the axiomatic model

Our simplified model is designed to refine the axiomatic model,
but to have the shape of an incremental operational model,
so that it can check the validity of an execution run on the fly.
For this to be possible, the simplified model makes some assumptions about the behaviour of the code,
of two types:

1. It assumes that the code of pKVM is disciplined and does not rely
on corners of the architecture that exist to support legacy hypervisor designs.

2. It assumes that the code of pKVM is synchronised enough; in particular,
for now, we assume that accesses to page tables are well-locked
(see limitations).

We have architected the simplified model so that it can work
as a checking model that flags violations
of its simplifying assumptions.
Currently, we only track some of these assumptions,
and ignore others silently.

Given these simplifying assumptions,
we have designed the automaton to keep track of just enough information to cover the remaining relaxed behaviour
so that it is sound with respect to the axiomatic model.
In particular, as described above, it accounts for some lag
by keeping the old valid descriptor of a page table entry
in the process of being "broken".

# Current status and limitations

The simplified model is able to run alongside pKVM
during a Linux boot, and during part of the loading a VM with `lkvm`.

## Testing

To test our simplified model, we inject bugs in the code of pKVM.

We do this through a series of Kconfig options which each conditionally compile bugs in
(or conditionally remove critical code from)
the source code.

For example, when the `NVHE_GHOST_SPEC_INJECT_ERROR_stage2_try_break_pte_MISSING_TLBI` config option is enabled,
the calls to the `__kvm_tlb_flush` functions are removed from `stage2_try_break_pte`:

```C
	#if !defined(__KVM_NVHE_HYPERVISOR__) || !defined(CONFIG_NVHE_GHOST_SPEC_INJECT_ERROR_stage2_try_break_pte_MISSING_TLBI)
	if (kvm_pte_table(ctx->old, ctx->level))
		kvm_call_hyp(__kvm_tlb_flush_vmid, mmu);
	else if (kvm_pte_valid(ctx->old))
		kvm_call_hyp(__kvm_tlb_flush_vmid_ipa, mmu, ctx->addr, ctx->level);
	#endif /* CONFIG_NVHE_GHOST_SPEC_INJECT_ERROR_stage2_try_break_pte_MISSING_TLBI */
```

This causes the code to fail to perform a TLBI at the critical moment,
and on the subsequent write to the pagetable to make the new entry the simplified model flags
the execution as containing a break-before-make violation.

Below is an example trace from the instrumented pKVM sources,
which prints out on each hypercall from the base ghost machinery (in <span style="color: white; background-color: royalblue;">blue</span>, the first three lines)
and on each simplified model step (in <span style="color: black; background-color: aqua;">cyan</span>).

<pre>
<code>
<span style="color: white; background-color: royalblue;">****** TRAP (from  host) *****************************************************</span>
<span style="color: white; background-color: royalblue;">__pkvm_host_share_hyp</span>
<span style="color: white; background-color: royalblue;">[r1] pfn: 0x..........1372e2</span>
<span style="color: black; background-color: aqua;">W 0x........eabf9000 0x...............0 at arch/arm64/kvm/hyp/nvhe/page_alloc.c:84 in page_remove_from_list</span>
<span style="color: black; background-color: aqua;">W 0x........eabf9008 0x...............0 at arch/arm64/kvm/hyp/nvhe/page_alloc.c:84 in page_remove_from_list</span>
<span style="color: black; background-color: aqua;">W 0x........eaa8edc8 0x.............400 at arch/arm64/kvm/hyp/nvhe/../pgtable.c:968 in stage2_try_set_pte</span>
<span style="color: black; background-color: aqua;">Wrel 0x........eaa8edc8 0x........eabf9003 at arch/arm64/kvm/hyp/nvhe/../pgtable.c:1040 in stage2_make_pte</span>
! BBM invalid unclean->valid
[  162.133816] kvm [241]: nVHE hyp BUG at: arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c:1045!
```
</code>
</pre>

When enabling the verbose printing, we can see diffs of the simplified model state,
showing that the write to `0xeaa8edc8` (which here is an entry in the host pagetable),
turns the ghost state from valid (`V`) to invalid-unclean (`IU`) awaiting a barrier (`n`) on thread `0`.

<pre>
<code>
<span style="color: white; background-color: royalblue;">****** TRAP (from  host) *****************************************************</span>
<span style="color: white; background-color: royalblue;">__pkvm_host_share_hyp</span>
<span style="color: white; background-color: royalblue;">[r1] pfn: 0x..........1372e2</span>
<span style="color: black; background-color: aqua;">W 0x........eabf9000 0x...............0 at arch/arm64/kvm/hyp/nvhe/page_alloc.c:84 in page_remove_from_list</span>
<span style="color: black; background-color: aqua;">W 0x........eabf9008 0x...............0 at arch/arm64/kvm/hyp/nvhe/page_alloc.c:84 in page_remove_from_list</span>
<span style="color: black; background-color: aqua;">W 0x........eaa8edc8 0x.............400 at arch/arm64/kvm/hyp/nvhe/../pgtable.c:968 in stage2_try_set_pte</span>
transition simplified model state diff:
mem:
<span style="background-color: indianred;">-    *[0x........eaa8edc8]=0x.......<span style="color: black; background-color: red;">1372007fd</span> (<span style="color: black; background-color: red">pte_st:V</span>      root:0x........eaa1b000)</span>
<span style="background-color: darkseagreen;">+    *[0x........eaa8edc8]=0x.......<span style="color: white; background-color: green;">......400</span> (<span style="color: white; background-color: green;">pte_st:IU n 0</span> root:0x........eaa1b000)</span>
<span style="color: black; background-color: aqua;">Wrel 0x........eaa8edc8 0x........eabf9003 at arch/arm64/kvm/hyp/nvhe/../pgtable.c:1040 in stage2_make_pte</span>
<span style="color: white; background-color: red;">! BBM invalid unclean->valid</span>
[  162.133816] kvm [241]: nVHE hyp BUG at: arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c:1045!
</code>
</pre>

All output shown is from our ghost machinery.

## Limitations

As a compromise between simplicity and generality,
the simplified model currently assumes that code that manipulates the page tables is well-locked.
pKVM is moving away from that assumption, which means that our simplified model can fail to notice
synchronisation bugs when its internal synchronisation masks them.

Currently, the subautomata are very simple.
In particular, the `STATE_PTE_INVALID_UNCLEAN` subautomaton only has one path,
which models the coarsest form of TLB invalidation, namely using `TLBI VAE2IS`.
However, we architected the simplified model so that it can be extended to handle other `TLBI`s
by adding other paths to the automaton.

The simplified model is designed to be a checking model, flagging violations of its assumptions,
but only does so partially for now.

# Code structure
The definition of the simplified model itself is in

| [`arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h)
| [`arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c)

The instrumentation to drive it is spread over files that perform actions on page tables relevant to the simplified model:

| [`arch/arm64/include/asm/kvm_mmu.h`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/include/asm/kvm_mmu.h)
| [`arch/arm64/kvm/hyp/nvhe/mem_protect.c`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/nvhe/mem_protect.c)
| [`arch/arm64/kvm/hyp/nvhe/mm.c`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/nvhe/mm.c)
| [`arch/arm64/kvm/hyp/nvhe/page_alloc.c`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/nvhe/page_alloc.c)
| [`arch/arm64/kvm/hyp/nvhe/tlb.c`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/nvhe/tlb.c)
| [`arch/arm64/kvm/hyp/pgtable.c`](https://github.com/rems-project/linux-pkvm-verif-2/blob/pkvm-verif-6.4-sketch/arch/arm64/kvm/hyp/pgtable.c)
