<h1>
<img src="doc/logo/casemate_logo.png" align="left" width="75" height="75"/>
Casemate: Concurrent Architectural System-level <br/> Monitoring and Testing
</h1>

Casemate is a dynamic monitoring tool for checking architecture-level protocols in systems code.

Description
---

The primary protocol casemate looks for is **break-before-make**.

Kernels and hypervisors enforce isolation between VMs
by leveraging the *virtual memory* mechanism of the hardware.
Concretely, they dictate how hardware *memory management units* (MMUs)
in hardware translate *virtual addresses* manipulated by those VMs into the *physical addresses* of the system.
They do so by maintaining *page tables*, the in-memory data structures that the MMUs read.

Page tables are looked up by the MMUs, which use specialised caches, called Translation Lookaside Buffers (TLBs),
and on Arm those TLBs must be manually cleared by software.
Arm require software follow a specific protocol called **break-before-make**,
and failure to follow this protocol will break any isolation guarantees that the software tries to enforce.

Overview
---

There are two ways to use casemate:
1. Offline, with `casemate-check`, passing log files generated at runtime.
2. At runtime, with a library version of the checker linked into the program to test.

The offline checker takes log files containing traces,
in a format described in [doc/trace-format.md](./doc/trace-format.md),
and checks that the trace does not violate the protocols being checked.

One can also bake the checker into the kernel using the library directly, linking the generated object file into the build.
Hooks can then be added into the kernel to initialise the model and step the transitions.
The model performs trace checking dynamically, and notifies a failure when a violation of the protocol is detected.
The online checker can also be integrated with tracing infrastructure to generate logs suitable for offline checking later.

Examples of baking the checker into an executable can be found in the [examples](./examples/) directory,
which contains small C programs which drive the model and write the trace and final state to stdout.

Build and usage
---

All of the parts can be built by running `configure` and `make`:

```
$ ./configure
$ make
```

The small example programs can be run:
```
$ ./examples/good_write
(mem-init (id 0) (tid 0) (address 0xaaaac6de3000) (size 0x1000) (src "examples/tests/good_write.c:23"))
(hint (id 1) (tid 0) (kind set_root_lock) (location 0xaaaac6de3000) (value 0xaaaac6de4000) (src "examples/tests/good_write.c:24"))
(sysreg-write (id 2) (tid 0) (sysreg vttbr_el2) (value 0xaaaac6de3000) (src "examples/tests/good_write.c:27"))
(lock (id 3) (tid 0) (address 0xaaaac6de4000) (src "examples/tests/good_write.c:29"))
(mem-write (id 4) (tid 0) (mem-order plain) (address 0xaaaac6de3000) (value 0x0) (src "examples/tests/good_write.c:30"))
(unlock (id 5) (tid 0) (address 0xaaaac6de4000) (src "examples/tests/good_write.c:31"))
```

Such traces can be saved to a log and checked with `casemate-check`:
```
$ ./examples/good_write -a > good_write.log  # Note `-a` to suppress fancy formatting
$ ./casemate-check good_write.log
[...]
casemate-check: log checked successfully.
```

Runtime annotation
---

Programs can be annotated for checking at runtime (as in the [examples](./examples/)),
which involves initialisation and annotation of the key accesses in the program.

At some point, the model can be initialised, e.g.:
```
void initialise_casemate(u64 phys_memory_start, u64 phys_memory_size)
{
	struct casemate_options opts = CASEMATE_DEFAULT_OPTS;
	void *state_addr = malloc(sizeof(struct casemate_model_state)); // or 2x that if enabling diffing.
	initialise_casemate_model(&opts, phys_memory_start, phys_memory_size, state_addr, sizeof(struct casemate_model_state));

	struct ghost_driver sm_driver = {
		.read_physmem = NULL,
		.read_sysreg = read_sysreg_callback,
		...
	};
	initialise_ghost_driver(&sm_driver);

	u64 pgtable_root = EXTRACT_ROOT(read_sysreg(ttbr0_el2));

	/* Initialise the currently loaded pagetable's memory */
	FOREACH_PGTABLE_NODE(table, pgtable_root) {
		casemate_model_step_init(table, 4096);
		FOREACH_ENTRY(entry, table) {
			casemate_model_step_write(WMO_plain, virt_to_phys(entry), *entry);
		}
	}

	/* tell the model it's owned by this lock and currently loaded */
	casemate_model_step_hint(GHOST_HINT_SET_ROOT_LOCK, pgtable_root, virt_to_phys(pgtable_lock));
	casemate_model_step_msr(SYSREG_TTBR_EL2, pgtable_root);
}
```

Then annotate the accesses, e.g. at barriers, TLBIs, and, writes:

```
void vmm_flush_tlb_vaddr(u64 va)
{
	dsb(sy);
	casemate_model_step_dsb(DxB_sy);
	tlbi_va(va);
	casemate_model_step_tlbi3(TLBI_vae1is, va, 0);
	dsb(sy);
	casemate_model_step_dsb(sy);
	isb();
	casemate_model_step_isb();
}
```

Examples
---

See the [examples](./examples/) directory.

Documentation
---

See [doc/overview.md](./doc/overview.md) for explanation of how the checker works.
See [doc/trace-format.md](./doc/trace-format.md) for information about the format the offline checker accepts.

Acknowledgements
---

See [ACKNOWLEDGEMENTS](./ACKNOWLEDGEMENTS).