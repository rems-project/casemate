#include <linux/kvm_host.h>
#include <linux/types.h>

#include <asm/kvm.h>
#include <asm/kvm_pkvm.h>

#include <nvhe/spinlock.h>
#include <nvhe/memory.h>

#include <hyp/ghost_extra_debug-pl011.h>
#include <nvhe/ghost_asserts.h>
#include <nvhe/ghost_simplified_model.h>

/*
 * the actual state
 */
struct ghost_simplified_model_state the_ghost_state;
struct ghost_simplified_model_transition current_transition;
bool is_initialised = false;

#define GHOST_SIMPLIFIED_MODEL_CATCH_FIRE(msg) { \
	GHOST_WARN(msg); \
	ghost_assert(false); \
}

thread_identifier cpu_id(void)
{
	// TODO: can't seem to use hyp_smp_processor_id() due to linking issues
	return read_sysreg(tpidr_el1);
}

///////////
// locking

DEFINE_HYP_SPINLOCK(ghost_sm_lock);

static void lock_sm(void)
{
	hyp_spin_lock(&ghost_sm_lock);
}

static void unlock_sm(void)
{
	hyp_spin_unlock(&ghost_sm_lock);
}


static bool in_simplified_memory(u64 phys)
{
	return ((the_ghost_state.base_addr <= phys) && (phys <= the_ghost_state.base_addr + the_ghost_state.size));
}

static void ensure_blob(u64 phys)
{
	u64 blob_phys = ALIGN_DOWN_TO_BLOB(phys);
	struct ghost_memory_blob *first_free = NULL;

	// just iterate, try find the blob
	for (int i = 0; i < MAX_BLOBS; i++) {
		struct ghost_memory_blob *this = &the_ghost_state.memory.blobs[i];
		if (!this->valid) {
			if (first_free == NULL) {
				first_free = this;
			}
		} else if (this->phys == blob_phys) {
			// found it
			return;
		}
	}

	// have to grab a new blob
	if (first_free == NULL) {
		GHOST_WARN("simplified model ran out of free blobs");
		ghost_assert(false);
	}

	first_free->valid = true;
	first_free->phys = blob_phys;

	// the slots are intentionally uninitialised;
	// as of yet, they haven't been "seen" by the simplified model
	// so let the first-seen checks initialise them.
	for (int i = 0; i < SLOTS_PER_PAGE*PAGES_PER_BLOB; i++) {
		first_free->slots[i].initialised = false;
		first_free->slots[i].phys_addr = blob_phys + i*sizeof(u64);
	}
}

/**
 * location() - Read an address from the simplified model state.
 * @phys: the physical address.
 */
struct sm_location *location(u64 phys)
{
	u64 blob_phys = ALIGN_DOWN_TO_BLOB(phys);
	ensure_blob(phys);

	// just iterate, try to find the blob
	for (int i = 0; i < MAX_BLOBS; i++) {
		struct ghost_memory_blob *blob = &the_ghost_state.memory.blobs[i];
		if (blob->valid && blob->phys == blob_phys) {
			struct sm_location *loc = &blob->slots[OFFSET_IN_BLOB(phys) >> SLOT_SHIFT];
			return loc;
		}
	}

	// we ensured there was a blob, so we must have found it.
	unreachable();
}

/**
 * read_phys() - Read a location from the simplified model memory.
 * @pre: if true, read-from the memory before the transition.
 *
 * for reading the location this transition is writing,
 * `pre` selects reading the 'old' value of the location.
 */
static u64 __read_phys(u64 addr, bool pre)
{
	struct sm_location *loc;
	u64 value;
	u64 *hyp_va = (u64*)hyp_phys_to_virt((phys_addr_t)addr);
	u64 hyp_val = *hyp_va;

	// if it's not a location being tracked by the simplified model,
	// then this is probably a mistake
	if (! in_simplified_memory(addr)) {
		ghost_assert(false);
	}

	// otherwise, convert to index in memory and get the val
	loc = location(addr);

	if (! loc->initialised) {
		// if not yet initialised
		// assume the program was well-behaved up until now
		// and just return the current concrete value
		return hyp_val;
	}

	value = loc->val;

	// EDGE CASE: if `addr` is the address this transition is writing to
	// then the current value in the model memory will be old.
	if (current_transition.kind == TRANS_MEM_WRITE && addr == current_transition.write_data.phys_addr) {
		if (pre) {
			// if want the old value, return it.
			return value;
		} else {
			// otherwise, secretly return the value we are about to write.
			// then continue with checks.
			value = current_transition.write_data.val;
		}
	}

	// santity check:
	// if the model thinks the value is that, make sure the real location has that too
	if (hyp_val != value) {
		GHOST_WARN("the simplified model detected a PTE that changed under it");
		GHOST_LOG(hyp_va, u64);
		GHOST_LOG(value, u64);
		GHOST_LOG(hyp_val, u64);
		ghost_assert(false);
	}

	return value;
}

/**
 * read_phys_pre() - Read a physical address from the simplified model memory.
 *
 * This reads from the state just before the transition.
 * i.e. if this transition is a write to a location,
 * then this returns the previous value for that location.
 */
static u64 read_phys_pre(u64 addr)
{
	return __read_phys(addr, true);
}

/**
 * read_phys() - Read a physical address from the simplified model memory.
 */
static u64 read_phys(u64 addr)
{
	return __read_phys(addr, false);
}

//////////////////////
// pagetable traversal

#define PTE_BIT_VALID BIT(0)
#define PTE_BIT_TABLE BIT(1)
#define PTE_BITS_TABLE_POINTER GENMASK(47, 12)
#define PTE_BIT_OA_MSB 47

#define KiB_SHIFT 10ULL
#define MiB_SHIFT 20ULL
#define GiB_SHIFT 30ULL

#define KiB(n) ((n) << KiB_SHIFT)
#define MiB(n) ((n) << MiB_SHIFT)
#define GiB(n) ((n) << GiB_SHIFT)

// how much memory a map at level [N] maps
static const u64 MAP_SIZES[] = {
	[0] = GiB(512),
	[1] = GiB(1),
	[2] = MiB(2),
	[3] = KiB(4),
};

static const u64 OA_shift[] = {
	[1] = 12+9+9,
	[2] = 12+9,
	[3] = 12,
};


#define TCR_EL2_T0SZ_SHIFT	0
static u64 read_start_level(u64 tcr)
{
	u64 t0sz = (tcr & TCR_EL2_T0SZ_MASK) >> TCR_EL2_T0SZ_SHIFT;
	// input address = (64 - t0sz) bits
	// max = 48
	// min = 21 (only level 3 table)
	// each 9 bits in-between increases start by 1 level
	u64 ia_bits = 64 - t0sz;
	return (48 - ia_bits) / 9;
}

static u64 discover_start_level(bool s2)
{
	if (s2) {
		u64 vtcr = read_sysreg(vtcr_el2);
		return read_start_level(vtcr);
	} else {
		u64 tcr = read_sysreg(tcr_el2);
		return read_start_level(tcr);
	}
}


enum pte_kind {
	PTE_KIND_TABLE,
	PTE_KIND_MAP,  /* BLOCK,PAGE */
	PTE_KIND_INVALID,
};

struct pte_deconstructed {
	enum pte_kind kind;
	union {
		struct {
			u64 next_level_table_addr;
		} table_data;

		struct {
			u64 region_start;
			u64 region_size;
		} map_data;
	};
};

static bool is_desc_valid(u64 descriptor)
{
	return (descriptor & PTE_BIT_VALID) == PTE_BIT_VALID;
}

static bool is_desc_table(u64 descriptor, u64 level, bool s2)
{
	if (level == 3)
		return false;

	return (descriptor & PTE_BIT_TABLE) == PTE_BIT_TABLE;
}

static u64 extract_output_address(u64 desc, u64 level)
{
	u64 OA_mask = GENMASK(PTE_BIT_OA_MSB, OA_shift[level]);
	return (desc & OA_mask);
}

static u64 extract_table_address(u64 desc)
{
	return desc & PTE_BITS_TABLE_POINTER;
}

struct pte_deconstructed deconstruct_pte(u64 desc, u64 level, bool s2)
{
	struct pte_deconstructed deconstructed;

	if (! is_desc_valid(desc)) {
		deconstructed.kind = PTE_KIND_INVALID;
		return deconstructed;
	} else if (is_desc_table(desc, level, s2)) {
		deconstructed.kind = PTE_KIND_TABLE;
		deconstructed.table_data.next_level_table_addr = extract_table_address(desc);
		return deconstructed;
	} else {
		deconstructed.kind = PTE_KIND_MAP;
		deconstructed.map_data.region_start = extract_output_address(desc, level);
		deconstructed.map_data.region_size = MAP_SIZES[level];
		return deconstructed;
	}
}

struct pgtable_traverse_context {
	u64 pte_phys_addr;
	struct sm_location *loc;

	u64 descriptor;
	u64 level;
	bool leaf;

	u64 partial_ia;
	u64 ia_region_size;
	struct pte_deconstructed deconstructed;

	u64 root;
	bool s2;

	void* data;
};

typedef void (*pgtable_traverse_cb)(struct pgtable_traverse_context *ctxt);

static void traverse_pgtable_from(u64 root, u64 table_start, u64 partial_ia, u64 level, bool s2, pgtable_traverse_cb visitor_cb, void *data)
{
	struct pgtable_traverse_context ctxt;

	GHOST_LOG_CONTEXT_ENTER();
	ctxt.root = root;
	ctxt.s2 = s2;
	ctxt.data = data;
	ctxt.level = level;

	ghost_assert(IS_PAGE_ALIGNED(table_start));

	for (int i = 0; i < 512; i++) {
		u64 pte_phys;
		u64 desc;
		struct sm_location *loc;

		GHOST_LOG_CONTEXT_ENTER_INNER("loop");
		GHOST_LOG(i, u32);

		pte_phys = table_start + i*sizeof(u64);
		GHOST_LOG(pte_phys, u64);

		desc = read_phys(pte_phys);
		GHOST_LOG(desc, u64);

		loc = location(pte_phys);

		ctxt.pte_phys_addr = pte_phys;
		ctxt.loc = loc;
		ctxt.descriptor = desc;
		ctxt.deconstructed = deconstruct_pte(desc, level, s2);
		ctxt.leaf = ctxt.deconstructed.kind != PTE_KIND_TABLE;
		ctxt.ia_region_size = MAP_SIZES[level];
		ctxt.partial_ia = partial_ia + i*ctxt.ia_region_size;
		visitor_cb(&ctxt);

		switch (ctxt.deconstructed.kind) {
		case PTE_KIND_TABLE:
			traverse_pgtable_from(root, ctxt.deconstructed.table_data.next_level_table_addr, ctxt.partial_ia, level+1, s2, visitor_cb, data);
			break;
		case PTE_KIND_MAP:
		case PTE_KIND_INVALID:
		default:
			;
		}
		GHOST_LOG_CONTEXT_EXIT();
	}
	GHOST_LOG_CONTEXT_EXIT();
}

static void traverse_pgtable(u64 root, bool s2, pgtable_traverse_cb visitor_cb, void *data)
{
	// TODO: concatenated s2 pagetables
	u64 start_level = discover_start_level(s2);
	GHOST_LOG(root, u64);
	GHOST_LOG(start_level, u64);
	traverse_pgtable_from(root, root, 0, start_level, s2, visitor_cb, data);
}

static void traverse_all_s1_pgtables(pgtable_traverse_cb visitor_cb, void *data)
{
	for (int i = 0; i < the_ghost_state.nr_s1_roots; i++) {
		traverse_pgtable(the_ghost_state.s1_roots[i], false, visitor_cb, data);
	}
}

static void traverse_all_s2_pgtables(pgtable_traverse_cb visitor_cb, void *data)
{
	for (int i = 0; i < the_ghost_state.nr_s2_roots; i++) {
		traverse_pgtable(the_ghost_state.s2_roots[i], true, visitor_cb, data);
	}
}

static void traverse_all_pgtables(pgtable_traverse_cb visitor_cb, void *data)
{
	traverse_all_s1_pgtables(visitor_cb, data);
	traverse_all_s2_pgtables(visitor_cb, data);
}


struct pgtable_walk_result {
	u64 requested_pte;
	bool found;

	struct pte_deconstructed deconstructed;

	u64 root;
	bool s2;

	u64 level;
};

void finder_cb(struct pgtable_traverse_context *ctxt)
{
	struct pgtable_walk_result *result = (struct pgtable_walk_result*)ctxt->data;
	if (ctxt->pte_phys_addr == result->requested_pte) {
		result->found = true;
		result->root = ctxt->root;
		result->deconstructed = ctxt->deconstructed;
		result->s2 = ctxt->s2;
		result->level = ctxt->level;
	}
}

struct pgtable_walk_result find_pte(u64 pte)
{
	struct pgtable_walk_result result;
	result.found = false;
	result.requested_pte = pte;

	traverse_all_pgtables(finder_cb, &result);

	return result;
}

/**
 * initial_state() - Construct an initial sm_pte_state for a clean descriptor.
 */
struct sm_pte_state initial_state(u64 desc, u64 level, bool s2)
{
	struct sm_pte_state state;
	struct pte_deconstructed deconstructed = deconstruct_pte(desc, level, s2);
	switch (deconstructed.kind) {
	case PTE_KIND_INVALID:
		state.kind = STATE_PTE_INVALID;
		state.invalid_clean_state.invalidator_tid = cpu_id();
		break;
	case PTE_KIND_MAP:
	case PTE_KIND_TABLE:
		state.kind = STATE_PTE_VALID;
		for (int i = 0; i < MAX_CPU; i++) {
			state.valid_state.lvs[i] = LVS_unguarded;
		}
		break;
	default:
		unreachable();
	}

	return state;
}


////////////////////
// Reachability

static void clean_reachability_checker_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised)
		return;

	if (loc->state.kind == STATE_PTE_INVALID_UNCLEAN) {
		bool *data = (bool *)ctxt->data;
		*data = false;
	}
}

/*
 * if mem (was) a table entry, traverse the old children
 * and check they were all clean (VALID or INVALID, but not INVALID_UNCLEAN).
 */
static bool pre_all_reachable_clean(struct sm_location *loc)
{
	struct pgtable_walk_result pte;
	struct pte_deconstructed desc;
	bool all_clean;

	if (! loc->is_pte)
		return true;

	// if we have a pte, find it in the parent tree
	pte = find_pte(loc->phys_addr);
	if (! pte.found) {
		// TODO: BS: probably on invalidating with children need to un-is_pte them.
		GHOST_WARN("loc.is_pte should imply existence in pgtable");
		ghost_assert(false);
	}

	desc = deconstruct_pte(read_phys_pre(loc->phys_addr), pte.level, pte.s2);
	if (desc.kind != PTE_KIND_TABLE) {
		return true;
	}

	// if the old value was a table, then traverse it from here.
	all_clean = true;
	traverse_pgtable_from(pte.root, desc.table_data.next_level_table_addr, 0, pte.level + 1, pte.s2, clean_reachability_checker_cb, &all_clean);

	// NOTE: the traversal may have unset all_clean.
	return all_clean;
}

////////////////////
// Step write sysreg

void marker_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised) {
		// if this was the first time we saw it
		// initialise it and copy in the value
		loc->initialised = true;
		loc->val = ctxt->descriptor;
	} else if (loc->is_pte) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("double-use pte");
	}

	// mark that this location is now an active pte
	// and start following the automata
	loc->is_pte = true;
	loc->owner_root = ctxt->root;
	loc->state = initial_state(ctxt->descriptor, ctxt->level, ctxt->s2);
}

static void register_s2_root(phys_addr_t root)
{
	GHOST_LOG_CONTEXT_ENTER();
	// TODO: VMIDs
	the_ghost_state.s2_roots[the_ghost_state.nr_s2_roots++] = root;
	traverse_pgtable(root, true, marker_cb, NULL);
	GHOST_LOG_CONTEXT_EXIT();
}

static void register_s1_root(phys_addr_t root)
{
	GHOST_LOG_CONTEXT_ENTER();
	the_ghost_state.s1_roots[the_ghost_state.nr_s1_roots++] = root;
	traverse_pgtable(root, false, marker_cb, NULL);
	GHOST_LOG_CONTEXT_EXIT();
}

#define VTTBR_EL2_BADDR_MASK	(GENMASK(47, 1))
#define TTBR0_EL2_BADDR_MASK	(GENMASK(47, 1))

static phys_addr_t extract_s2_root(u64 vttb)
{
	return vttb & VTTBR_EL2_BADDR_MASK;
}

static phys_addr_t extract_s1_root(u64 ttb)
{
	return ttb & TTBR0_EL2_BADDR_MASK;
}

static void step_msr(struct ghost_simplified_model_transition trans)
{
	switch (trans.msr_data.sysreg) {
	case SYSREG_TTBR_EL2:
		register_s1_root(extract_s1_root(trans.msr_data.val));
		break;
	case SYSREG_VTTBR:
		register_s2_root(extract_s2_root(trans.msr_data.val));
		break;
	}

}

////////////////////////
// Step on memory write

static void step_write_on_invalid(enum memory_order_t mo, struct sm_location *loc, u64 val)
{
	if (! is_desc_valid(val)) {
		// overwrite invalid with another invalid is identity
		return;
	}

	// invalid -> valid
	loc->state.kind = STATE_PTE_VALID;

	// globally all cores see a valid value now
	// (because of the lack of unsychronised races on ptes)
	for (int i = 0; i < MAX_CPU; i++) {
		loc->state.valid_state.lvs[i] = LVS_unguarded;
	}
}

static void step_write_on_invalid_unclean(enum memory_order_t mo, struct sm_location *loc, u64 val)
{
	if (is_desc_valid(val)) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("BBM invalid unclean->valid");
		return;
	} else {
		// can overwrite invalid with another invalid (even if not DSB+TLBI'd yet).
		// this doesn't affect the local state, so just the identity.
		return;
	}
}

static void step_write_on_valid(enum memory_order_t mo, struct sm_location *loc, u64 val)
{
	if (is_desc_valid(val)) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("BBM valid->valid");
		return;
	}

  // TODO:JP: maybe this is too strong, and keeping the old "valid" value
	// can only write 0 at level~N if level~N+1 children are clean
	if (! pre_all_reachable_clean(loc)) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("BBM valid->invalid with unclean children");
		return;
	}

	loc->state.kind = STATE_PTE_INVALID_UNCLEAN;
	loc->state.invalid_unclean_state = (struct aut_invalid) {
		.invalidator_tid = cpu_id(),
		.old_valid_desc = read_phys_pre(loc->phys_addr),
	};

	// TODO: BS: this really can't be written in the compound literal above?
	for (int i = 0; i < MAX_CPU; i++) {
		loc->state.invalid_unclean_state.lis[i] = LIS_unguarded;
	}
}

static void step_write(struct ghost_simplified_model_transition trans)
{
	enum memory_order_t mo = trans.write_data.mo;
	u64 val = trans.write_data.val;

	// look inside memory at `addr`
	struct sm_location *loc = location(trans.write_data.phys_addr);

	if (!loc->is_pte) {
		goto done;
	}

	// actually is a pte, so have to do some checks...
	switch (loc->state.kind) {
	case STATE_PTE_VALID:
		step_write_on_valid(mo, loc, val);
		break;
	case STATE_PTE_INVALID_UNCLEAN:
		step_write_on_invalid_unclean(mo, loc, val);
		break;
	case STATE_PTE_INVALID:
		step_write_on_invalid(mo, loc, val);
		break;
	default:
		unreachable();
	}

done:
	loc->val = val;
	return;
}

////////////////////////
// Step on memory read

static void step_read(struct ghost_simplified_model_transition trans)
{
	struct sm_location *loc = location(trans.write_data.phys_addr);

	// read doesn't have any real behaviour, except to return the value stored in memory.
	// so we just assert that the value in the real concrete memory is what we are tracking.
	// (the read_phys already does this check, but it's never bad to double check).
	ghost_assert(read_phys(loc->phys_addr) != loc->val);
}

/////////////////
// Step on a DSB

void dsb_visitor(struct pgtable_traverse_context *ctxt)
{
	thread_identifier this_cpu = cpu_id();
	struct sm_location *loc = ctxt->loc;
	enum dsb_kind dsb_kind = *(enum dsb_kind *)ctxt->data;

	if (dsb_kind == DSB_nsh) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("DSB NSH not supported");
	}

	// we just did a DSB:
	switch (loc->state.kind) {
	case STATE_PTE_INVALID_UNCLEAN:
		// if the invalid pte wasn't written by this cpu, skip.
		if (! (loc->state.invalid_unclean_state.invalidator_tid == this_cpu)) {
			break;
		}

		if (loc->state.invalid_unclean_state.lis[this_cpu] == LIS_unguarded) {
			// if not yet DSBd, then tick it forward for this cpu
			loc->state.invalid_unclean_state.lis[this_cpu] = LIS_dsbed;
		} else if (loc->state.invalid_unclean_state.lis[this_cpu] == LIS_dsb_tlbi_all) {
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

static void step_dsb(struct ghost_simplified_model_transition trans)
{
	// annoyingly, DSBs aren't annotated with their addresses.
	// so we do the really dumb thing: we go through every pagetable that we know about
	// and step any we find in the right state.
	traverse_all_pgtables(dsb_visitor, &trans.dsb_data);
}

///////////////////
// Step on a TLBI

static void step_pte_on_tlbi(struct sm_location *loc)
{
	thread_identifier this_cpu = cpu_id();

	switch (loc->state.kind) {
	case STATE_PTE_INVALID_UNCLEAN:
		if (
			   (loc->state.invalid_unclean_state.invalidator_tid == this_cpu)
			&& (loc->state.invalid_unclean_state.lis[this_cpu] == LIS_dsbed)
		) {
			loc->state.invalid_unclean_state.lis[this_cpu] = LIS_dsb_tlbi_all;
		}
		break;
	default:
		;
	}
}

static void tlbi_visitor(struct pgtable_traverse_context *ctxt)
{
	u64 tlbi_addr;
	struct sm_location *loc = ctxt->loc;
	struct trans_tlbi_data *tlbi_data = (struct trans_tlbi_data*)ctxt->data;


	switch (tlbi_data->tlbi_kind) {
	// if by VA
	case TLBI_vae2is:
		tlbi_addr = tlbi_data->page << PAGE_SHIFT;

		/*
		 * if this pte is not a leaf which maps the page the TLBI asked for
		 * then don't try step the pte.
		 */
		if (! (ctxt->leaf && (ctxt->partial_ia <= tlbi_addr) && (tlbi_addr < ctxt->partial_ia + ctxt->ia_region_size))) {
			return;
		}

		break;
	// TODO: multi-step TLBIs
	default:
		;
	}

	step_pte_on_tlbi(loc);

}

static void step_tlbi(struct ghost_simplified_model_transition trans)
{
	switch (trans.tlbi_data.tlbi_kind) {
	// if TLBI_ALL, have to hit all the ptes
	case TLBI_vmalls12e1is:
		traverse_all_s2_pgtables(tlbi_visitor, &trans.tlbi_data);
		break;
	case TLBI_vae2is:
		traverse_all_s1_pgtables(tlbi_visitor, &trans.tlbi_data);
		break;
	// TODO: other TLBIs
	default:
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("unsupported TLBI");
	}
}

/////////////////////
// ISB

static void step_isb(struct ghost_simplified_model_transition trans)
{
	// ISB is a NOP?
}


///////////////////////////
/// Generic Step

void ghost_simplified_model_step(struct ghost_simplified_model_transition trans)
{
	lock_sm();

	if (! is_initialised) {
		goto unlock;
	}

	GHOST_LOG_CONTEXT_ENTER();
	GHOST_LOG(trans, trans);

	current_transition = trans;

	switch (trans.kind) {
	case TRANS_MEM_WRITE:
		step_write(trans);
		break;
	case TRANS_MEM_READ:
		step_read(trans);
		break;
	case TRANS_DSB:
		step_dsb(trans);
		break;
	case TRANS_ISB:
		step_isb(trans);
		break;
	case TRANS_TLBI:
		step_tlbi(trans);
		break;
	case TRANS_MSR:
		step_msr(trans);
		break;
	};

	GHOST_LOG_CONTEXT_EXIT();

unlock:
	unlock_sm();
}


//////////////////////////
// Initialisation

void initialise_ghost_ptes_memory(phys_addr_t phys, u64 size) {
	lock_sm();
	GHOST_LOG_CONTEXT_ENTER();
	the_ghost_state.base_addr = phys;
	the_ghost_state.size = size;
	for (int i = 0; i < MAX_BLOBS; i++) {
		the_ghost_state.memory.blobs[i].valid = false;
	}
	register_s1_root(extract_s1_root(read_sysreg(ttbr0_el2)));
	is_initialised = true;
	GHOST_LOG_CONTEXT_EXIT();
	unlock_sm();
}



//////////////////////////////
//// MISC

void print_write_trans(struct trans_write_data *write_data)
{
	hyp_putsp("W");
	if (write_data->mo == WMO_release) {
		hyp_putsp("rel");
	}
	hyp_putsp(" ");
	hyp_putx64((u64)write_data->phys_addr);
	hyp_putsp(" ");
	hyp_putx64(write_data->val);
}

void print_read_trans(struct trans_read_data *read_data)
{
	hyp_putsp("R");
	hyp_putsp(" ");
	hyp_putx64((u64)read_data->phys_addr);
	hyp_putsp(" (=");
	hyp_putx64(read_data->val);
	hyp_putsp(")");
}

void print_dsb_trans(enum dsb_kind *dsb_data)
{
	hyp_putsp((char *)dsb_kind_names[*dsb_data]);
}

void print_tlbi_trans(struct trans_tlbi_data *tlbi_data)
{
	hyp_putsp((char *)tlbi_kind_names[tlbi_data->tlbi_kind]);
	hyp_putsp(" ");
	switch (tlbi_data->tlbi_kind) {
		case TLBI_vale2is:
		case TLBI_vae2is:
		case TLBI_ipas2e1is:
			hyp_putsp("pfn=");
			hyp_putx64(tlbi_data->page);
			hyp_putsp("level=");
			hyp_putx64(tlbi_data->level);
			break;
		default:
			;
	}
}

void print_msr_trans(struct trans_msr_data *msr_data)
{
	hyp_putsp("MSR");
	hyp_putsp(" ");
	hyp_putsp((char *)sysreg_names[msr_data->sysreg]);
	hyp_putsp(" ");
	hyp_putx64(msr_data->val);
}

// A helper for the GHOST_LOG and GHOST_WARN macros
// to print out a whole simplified model transition
void GHOST_transprinter(void *data)
{
	struct ghost_simplified_model_transition *trans = (struct ghost_simplified_model_transition *)data;
	switch (trans->kind) {
	case TRANS_MEM_WRITE:
		print_write_trans(&trans->write_data);
		break;
	case TRANS_MEM_READ:
		print_read_trans(&trans->read_data);
		break;
	case TRANS_DSB:
		print_dsb_trans(&trans->dsb_data);
		break;
	case TRANS_ISB:
		hyp_putsp("ISB");
		break;
	case TRANS_TLBI:
		print_tlbi_trans(&trans->tlbi_data);
		break;
	case TRANS_MSR:
		print_msr_trans(&trans->msr_data);
		break;
	};
}