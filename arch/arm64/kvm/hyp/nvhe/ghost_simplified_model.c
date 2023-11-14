#include <linux/kvm_host.h>
#include <linux/types.h>

#include <asm/kvm.h>
#include <asm/kvm_pkvm.h>

#include <nvhe/spinlock.h>
#include <nvhe/memory.h>
#include <nvhe/mem_protect.h>
#include <nvhe/pkvm.h>

#include <nvhe/ghost_control.h>
#include <nvhe/ghost_asserts.h>
#include <hyp/ghost_extra_debug-pl011.h>
#include <nvhe/ghost_printer.h>
#include <nvhe/ghost_abstraction_diff.h>
#include <nvhe/ghost_simplified_model.h>


/*
 * the actual state
 *
 * We keep two, for diffing and debugging purposes.
 */
struct ghost_simplified_model_state *the_ghost_state;
struct ghost_simplified_model_state *the_ghost_state_pre;

struct ghost_simplified_model_options ghost_sm_options;
struct ghost_simplified_model_transition current_transition;
bool is_initialised = false;

#define GHOST_SIMPLIFIED_MODEL_CATCH_FIRE(msg) { \
	GHOST_WARN(msg); \
	ghost_assert(false); \
}

thread_identifier cpu_id(void)
{
	return hyp_smp_processor_id();
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

/*
 * Each simplified model transition should be atomic,
 * that means that all the locks of pKVM must be taken
 * ensuring that the simplified model has total ownership.
 *
 * In practice this isn't what we want:
 * pKVM assumes a partial lock order:
 * - host (on its own)
 * - host->hyp
 * - host->vm
 * - vm_table->vm
 *
 * We can linearise this to vm_table->host->hyp->vm
 *
 * In future we will want a global reentrant (reader-writer?) lock,
 * where all other threads can interleave freely up until a simplified model step,
 * at which point all other threads must wait for the simplified model step to finish.
 * Doing this without the minor possibility of deadlocks seems difficult...
 */
extern hyp_spinlock_t pkvm_pgd_lock;
extern struct host_mmu host_mmu;
extern hyp_spinlock_t vm_table_lock;
extern struct pkvm_hyp_vm **vm_table;

bool pkvm_locked;
bool host_locked;
bool vm_table_locked;
bool vms_locked[KVM_MAX_PVMS];

static bool try_lock(hyp_spinlock_t *lock)
{
	if (! hyp_spin_is_locked(lock)) {
		hyp_spin_lock(lock);
		return true;
	} else {
		return false;
	}
}

static void ensure_atomic_lock(void)
{
	vm_table_locked = try_lock(&vm_table_lock);
	host_locked = try_lock(&host_mmu.lock);
	pkvm_locked = try_lock(&pkvm_pgd_lock);

	if (! vm_table)
		return;

	// Note: no lock order between VMs (?)
	// so we impose one going in order of vm_table index
	for (u64 i=0; i < KVM_MAX_PVMS; i++) {
		struct pkvm_hyp_vm *vm = vm_table[i];
		if (vm)
			vms_locked[i] = try_lock(&vm->lock);
	}
}

static void ensure_atomic_unlock(void)
{
	/* undo all the locks we took earlier */

	if (! vm_table)
		goto unlock_pkvm;

	for (u64 i = KVM_MAX_PVMS; i > 0; i--) {
		struct pkvm_hyp_vm *vm = vm_table[i - 1];
		if (vm && vms_locked[i - 1]) {
			hyp_spin_unlock(&vm->lock);
		}
	}

unlock_pkvm:
	if (pkvm_locked)
		hyp_spin_unlock(&pkvm_pgd_lock);

	if (host_locked)
		hyp_spin_unlock(&host_mmu.lock);

	if (vm_table_locked)
		hyp_spin_unlock(&vm_table_lock);
}

///////////
// Memory

void copy_sm_state_into(struct ghost_simplified_model_state *out);


static bool in_simplified_memory(u64 phys)
{
	return ((the_ghost_state->base_addr <= phys) && (phys <= the_ghost_state->base_addr + the_ghost_state->size));
}

static void ensure_blob(u64 phys)
{
	u64 blob_phys = ALIGN_DOWN_TO_BLOB(phys);
	struct ghost_memory_blob *first_free = NULL;

	// just iterate, try find the blob
	for (int i = 0; i < MAX_BLOBS; i++) {
		struct ghost_memory_blob *this = &the_ghost_state->memory.blobs[i];
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
		struct sm_location *slot = &first_free->slots[i];
		slot->initialised = false;
		slot->phys_addr = blob_phys + i*sizeof(u64);
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
		struct ghost_memory_blob *blob = &the_ghost_state->memory.blobs[i];
		if (blob->valid && blob->phys == blob_phys) {
			struct sm_location *loc = &blob->slots[SLOT_OFFSET_IN_BLOB(phys)];
			return loc;
		}
	}

	// we ensured there was a blob, so we must have found it.
	GHOST_WARN("tried to access location that wasn't in a blob");
	ghost_assert(false);
	unreachable();
	return NULL;
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
		GHOST_LOG_CONTEXT_ENTER();
		GHOST_WARN("the simplified model detected a PTE that changed under it");
		GHOST_LOG(hyp_va, u64);
		GHOST_LOG(value, u64);
		GHOST_LOG(hyp_val, u64);
		ghost_assert(false);
		GHOST_LOG_CONTEXT_EXIT();
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
	[0] = GiB(512ULL),
	[1] = GiB(1ULL),
	[2] = MiB(2ULL),
	[3] = KiB(4ULL),
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

struct ghost_exploded_descriptor deconstruct_pte(u64 partial_ia, u64 desc, u64 level, bool s2)
{
	struct ghost_exploded_descriptor deconstructed;

	deconstructed.ia_region = (struct ghost_addr_range){
		.range_start = partial_ia,
		.range_size = MAP_SIZES[level],
	};
	deconstructed.level = level;
	deconstructed.s2 = s2;


	if (! is_desc_valid(desc)) {
		deconstructed.kind = PTE_KIND_INVALID;
		return deconstructed;
	} else if (is_desc_table(desc, level, s2)) {
		deconstructed.kind = PTE_KIND_TABLE;
		deconstructed.table_data.next_level_table_addr = extract_table_address(desc);
		return deconstructed;
	} else {
		deconstructed.kind = PTE_KIND_MAP;
		deconstructed.map_data.oa_region = (struct ghost_addr_range){
			.range_start = extract_output_address(desc, level),
			.range_size = MAP_SIZES[level],
		};
		return deconstructed;
	}
}

struct pgtable_traverse_context {
	struct sm_location *loc;

	u64 descriptor;
	u64 level;
	bool leaf;

	struct ghost_exploded_descriptor exploded_descriptor;

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
		GHOST_LOG_INNER("loop", i, u32);

		pte_phys = table_start + i*sizeof(u64);
		GHOST_LOG_INNER("loop", pte_phys, u64);

		desc = read_phys(pte_phys);
		GHOST_LOG_INNER("loop", desc, u64);

		loc = location(pte_phys);

		ctxt.loc = loc;
		ctxt.descriptor = desc;
		ctxt.exploded_descriptor = deconstruct_pte(partial_ia, desc, level, s2);
		ctxt.leaf = ctxt.exploded_descriptor.kind != PTE_KIND_TABLE;
		visitor_cb(&ctxt);

		switch (ctxt.exploded_descriptor.kind) {
		case PTE_KIND_TABLE:
			traverse_pgtable_from(root, ctxt.exploded_descriptor.table_data.next_level_table_addr, ctxt.exploded_descriptor.ia_region.range_size, level+1, s2, visitor_cb, data);
			break;
		case PTE_KIND_MAP:
		case PTE_KIND_INVALID:
		default:
			;
		}
		GHOST_LOG_CONTEXT_EXIT_INNER("loop");
	}
	GHOST_LOG_CONTEXT_EXIT();
}

static void traverse_pgtable(u64 root, bool s2, pgtable_traverse_cb visitor_cb, void *data)
{
	u64 start_level;
	GHOST_LOG_CONTEXT_ENTER();
	// TODO: concatenated s2 pagetables
	start_level = discover_start_level(s2);
	GHOST_LOG(root, u64);
	GHOST_LOG(start_level, u64);
	traverse_pgtable_from(root, root, 0, start_level, s2, visitor_cb, data);
	GHOST_LOG_CONTEXT_EXIT();
}

static void traverse_all_s1_pgtables(pgtable_traverse_cb visitor_cb, void *data)
{
	for (int i = 0; i < the_ghost_state->nr_s1_roots; i++) {
		traverse_pgtable(the_ghost_state->s1_roots[i], false, visitor_cb, data);
	}
}

static void traverse_all_s2_pgtables(pgtable_traverse_cb visitor_cb, void *data)
{
	for (int i = 0; i < the_ghost_state->nr_s2_roots; i++) {
		traverse_pgtable(the_ghost_state->s2_roots[i], true, visitor_cb, data);
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

	struct ghost_exploded_descriptor descriptor;

	u64 root;
	bool s2;

	u64 level;
};

void finder_cb(struct pgtable_traverse_context *ctxt)
{
	struct pgtable_walk_result *result = (struct pgtable_walk_result*)ctxt->data;
	if (ctxt->loc->phys_addr == result->requested_pte) {
		result->found = true;
		result->root = ctxt->root;
		result->descriptor = ctxt->exploded_descriptor;
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
struct sm_pte_state initial_state(u64 partial_ia, u64 desc, u64 level, bool s2)
{
	struct sm_pte_state state;
	struct ghost_exploded_descriptor deconstructed = deconstruct_pte(partial_ia, desc, level, s2);
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
// Locks

hyp_spinlock_t *owner_lock(sm_owner_t owner_id)
{
	for (int i = 0; i < the_ghost_state->locks.len; i++) {
		if (the_ghost_state->locks.owner_ids[i] == owner_id) {
			return the_ghost_state->locks.locks[i];
		}
	}

	return NULL;
}

static void swap_lock(sm_owner_t root, hyp_spinlock_t *lock)
{
	struct owner_locks *locks = &the_ghost_state->locks;

	if (! owner_lock(root)) {
		ghost_assert(false);
	}

	for (int i = 0; i < the_ghost_state->locks.len; i++) {
		if (locks->owner_ids[i] == root) {
			locks->locks[i] = lock;
			return;
		}
	}

	GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("can't change lock on unlocked location");
}

static void append_lock(sm_owner_t root, hyp_spinlock_t *lock)
{
	u64 i;

	if (owner_lock(root)) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("can't append lock on already locked location");
		unreachable();
	}

	i = the_ghost_state->locks.len++;
	the_ghost_state->locks.owner_ids[i] = root;
	the_ghost_state->locks.locks[i] = lock;
}

static void associate_lock(sm_owner_t root, hyp_spinlock_t *lock)
{
	if (owner_lock(root)) {
		swap_lock(root, lock);
	} else {
		append_lock(root, lock);
	}
}

/**
 * assert_owner_locked() - Validates that the owner of a pte is locked by its lock.
 */
void assert_owner_locked(struct sm_location *loc)
{
	sm_owner_t owner_id = loc->owner;
	hyp_spinlock_t *lock = owner_lock(owner_id);
	ghost_assert(lock);  // can't have written without associating the owner.
	if (!hyp_spin_is_locked(lock))
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("must write to pte while holding owner lock");
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
	bool all_clean;

	if (! loc->is_pte)
		return true;

	// sanity check: it's actually in a tree somewhere...
	{
		struct pgtable_walk_result pte = find_pte(loc->phys_addr);
		if (! pte.found) {
			GHOST_WARN("loc.is_pte should imply existence in pgtable");
			ghost_assert(false);
		}
	}

	if (loc->descriptor.kind != PTE_KIND_TABLE) {
		return true;
	}

	// if the old value was a table, then traverse it from here.
	all_clean = true;
	traverse_pgtable_from(
		loc->owner,
		loc->descriptor.table_data.next_level_table_addr,
		loc->descriptor.ia_region.range_start,
		loc->descriptor.level + 1,
		loc->descriptor.s2,
		clean_reachability_checker_cb,
		&all_clean
	);

	// NOTE: the traversal may have unset all_clean.
	return all_clean;
}


void mark_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised) {
		// if this was the first time we saw it
		// initialise it and copy in the value
		loc->initialised = true;

		// we didn't see a previous write transition for this location
		// (otherwise it'd have been marked as initialised)
		// so attach the value now.

		// sanity check: we really aren't writing to it ...
		if (current_transition.kind == TRANS_MEM_WRITE && current_transition.write_data.phys_addr == loc->phys_addr)
			ghost_assert(false);


		loc->val = ctxt->descriptor;
	} else if (loc->is_pte) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("double-use pte");
	}

	// mark that this location is now an active pte
	// and start following the automata
	loc->is_pte = true;
	loc->owner = ctxt->root;
	loc->descriptor = ctxt->exploded_descriptor;
	loc->state = initial_state(ctxt->exploded_descriptor.ia_region.range_start, ctxt->descriptor, ctxt->level, ctxt->s2);
}

void unmark_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised) {
		// if this was the first time we saw it
		// initialise it and copy in the value
		loc->initialised = true;
	} else if (! loc->is_pte) {
		// TODO: BS: is this catch-fire or simply unreachable?
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("unmark non-PTE");
	}

	// mark that this location is no longer an active pte
	// and stop following the automata
	loc->is_pte = false;
}

////////////////////
// Step write sysreg

static bool s1_root_exists(phys_addr_t root)
{
	for (int i = 0; i < the_ghost_state->nr_s1_roots; i++) {
		if (the_ghost_state->s1_roots[i] == root)
			return true;
	}

	return false;
}

static bool s2_root_exists(phys_addr_t root)
{
	for (int i = 0; i < the_ghost_state->nr_s2_roots; i++) {
		if (the_ghost_state->s2_roots[i] == root)
			return true;
	}

	return false;
}

static void register_s2_root(phys_addr_t root)
{
	GHOST_LOG_CONTEXT_ENTER();
	if (s1_root_exists(root) || s2_root_exists(root))
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("root already exists");

	// TODO: VMIDs
	the_ghost_state->s2_roots[the_ghost_state->nr_s2_roots++] = root;
	traverse_pgtable(root, true, mark_cb, NULL);
	GHOST_LOG_CONTEXT_EXIT();
}

static void register_s1_root(phys_addr_t root)
{
	GHOST_LOG_CONTEXT_ENTER();
	if (s1_root_exists(root) || s2_root_exists(root))
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("root already exists");

	the_ghost_state->s1_roots[the_ghost_state->nr_s1_roots++] = root;
	traverse_pgtable(root, false, mark_cb, NULL);
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
	u64 root;
	switch (trans.msr_data.sysreg) {
	case SYSREG_TTBR_EL2:
		root = extract_s1_root(trans.msr_data.val);

		if (!s1_root_exists(root))
			register_s1_root(root);

		break;
	case SYSREG_VTTBR:
		root = extract_s2_root(trans.msr_data.val);

		if (!s2_root_exists(root))
			register_s2_root(root);

		break;
	}
}

////////////////////////
// Step on memory write

/*
 * when writing a new table entry
 * must ensure that the child table(s) are all clean
 * and not owned by another pgtable
 * then mark them as owned
 */
static void step_write_table_mark_children(struct sm_location *loc)
{
	if (loc->descriptor.kind == PTE_KIND_TABLE) {
		if (! pre_all_reachable_clean(loc)) {
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("BBM write table descriptor with unclean children");
		}

		traverse_pgtable_from(
			loc->owner,
			loc->descriptor.table_data.next_level_table_addr,
			loc->descriptor.ia_region.range_start,
			loc->descriptor.level + 1,
			loc->descriptor.s2,
			mark_cb,
			NULL
		);
	}
}


static void step_write_on_invalid(enum memory_order_t mo, struct sm_location *loc, u64 val)
{
	if (! is_desc_valid(val)) {
		// overwrite invalid with another invalid is identity
		return;
	}

	// check that if we're writing a TABLE entry
	// that the new tables are all 'good'
	step_write_table_mark_children(loc);

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

	// must own the lock on the pgtable this pte is in.
	assert_owner_locked(loc);

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
		if (ghost_sm_options.promote_DSB_nsh) {
			// silence noisy warning...
			// GHOST_WARN("DSB NSH not supported -- Assuming DSB ISH");
			dsb_kind = DSB_ish;
		} else {
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Unsupported DSB NSH");
		}
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

/*
 * when invalidating a zeroed table entry
 * unmark them as now no longer owned by the parent
 *
 * TODO: BS: is this correct?
 */
static void step_tlbi_invalid_unclean_unmark_children(struct sm_location *loc)
{
	u64 old;
	struct aut_invalid aut;
	struct ghost_exploded_descriptor old_desc;

	if (loc->state.kind != STATE_PTE_INVALID_UNCLEAN) {
		return;
	}

	GHOST_LOG_CONTEXT_ENTER();

	aut = loc->state.invalid_unclean_state;
	old = aut.old_valid_desc;
	old_desc = deconstruct_pte(loc->descriptor.ia_region.range_start, old, loc->descriptor.level, loc->descriptor.s2);


	// look at the old entry, and see if it was a table.
	if (old_desc.kind == PTE_KIND_TABLE) {
		// if we zero child entry, then zero the table entry
		// require that the child entries were TLBI'd first.
		// this means we don't have to recursively check the olds all the way down...
		// TODO: BS: is this too strong?
		if (! pre_all_reachable_clean(loc)) {
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("BBM write table descriptor with unclean children");
		}

		traverse_pgtable_from(loc->owner, old_desc.table_data.next_level_table_addr, loc->descriptor.ia_region.range_start, loc->descriptor.level, loc->descriptor.s2, unmark_cb, NULL);
	}

	GHOST_LOG_CONTEXT_EXIT();
}


static void step_pte_on_tlbi(struct sm_location *loc)
{
	thread_identifier this_cpu = cpu_id();

	// sanity check: if doing a TLBI on a tree with a root we know about
	// then all the children in that tree must have been marked by the (V)TTBR registration
	// or the writes of table entries...
	ghost_assert(loc->initialised);

	// if this was a table entry
	// there may have been children that we were still tracking
	// so go clear those.
	step_tlbi_invalid_unclean_unmark_children(loc);

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

static bool should_perform_tlbi(struct pgtable_traverse_context *ctxt)
{
	u64 tlbi_addr;
	struct trans_tlbi_data *tlbi_data = (struct trans_tlbi_data*)ctxt->data;

	// input-address range of the PTE we're visiting
	u64 ia_start = ctxt->exploded_descriptor.ia_region.range_start;
	u64 ia_end = ia_start + ctxt->exploded_descriptor.ia_region.range_size;

	switch (tlbi_data->tlbi_kind) {
	// if by VA
	case TLBI_vae2is:
		tlbi_addr = tlbi_data->page << PAGE_SHIFT;

		/*
		 * if this pte is not a leaf which maps the page the TLBI asked for
		 * then don't try step the pte.
		 */
		if (! (ctxt->leaf && (ia_start <= tlbi_addr) && (tlbi_addr < ia_end))) {
			return false;
		}

		break;
	// TODO: multi-step TLBIs
	default:
		;
	}

	return true;
}

static void tlbi_visitor(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	GHOST_LOG_CONTEXT_ENTER();

	if (should_perform_tlbi(ctxt)) {
		step_pte_on_tlbi(loc);
	}

	GHOST_LOG_CONTEXT_EXIT();
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
		GHOST_WARN("unsupported TLBI -- Defaulting to TLBI VMALLS12E1IS;TLBI ALLE2");
		traverse_all_s1_pgtables(tlbi_visitor, &trans.tlbi_data);
		traverse_all_s2_pgtables(tlbi_visitor, &trans.tlbi_data);
		break;
	}
}

/////////////////////
// ISB

static void step_isb(struct ghost_simplified_model_transition trans)
{
	// ISB is a NOP?
}


//////////////////////
// HINT

static void step_hint_set_root_lock(u64 root, hyp_spinlock_t *lock)
{
	// TODO: BS: on teardown a VM's lock might get disassociated,
	// then re-associated later with a different lock.
	//
	// currently this just swaps the lock over without any safety checks.
	associate_lock(root, lock);
}

static void step_hint_set_owner_root(u64 phys, sm_owner_t root)
{
	struct sm_location *loc = location(phys);

	// TODO: BS: before letting us disassociate a pte with a given VM/tree,
	// first we need to check that it's clean enough to forget about
	// the association with the old VM
	loc->owner = root;
}

static void step_hint(struct ghost_simplified_model_transition trans)
{
	switch (trans.hint_data.hint_kind) {
	case GHOST_HINT_SET_ROOT_LOCK:
		step_hint_set_root_lock(trans.hint_data.location, (hyp_spinlock_t *)trans.hint_data.value);
		break;
	case GHOST_HINT_SET_OWNER_ROOT:
		step_hint_set_owner_root(trans.hint_data.location, (sm_owner_t)trans.hint_data.value);
		break;
	default:
		;
	}
}

///////////////////////////
/// Generic Step

void ghost_simplified_model_step(struct ghost_simplified_model_transition trans)
{
	ensure_atomic_lock();
	lock_sm();

	if (! is_initialised) {
		goto unlock;
	}

	GHOST_LOG_CONTEXT_ENTER();
	GHOST_LOG(trans, trans);

	current_transition = trans;

#ifdef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS
	if (ghost_print_on("sm_diff_trans"))
		copy_sm_state_into(the_ghost_state_pre);
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS */

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
	case TRANS_HINT:
		step_hint(trans);
		break;
	};

	if (ghost_print_on("sm_dump_trans"))
		dump_sm_state(the_ghost_state);

#ifdef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS
	if (ghost_print_on("sm_diff_trans")) {
		ghost_printf("transition simplified model state diff: ");
		ghost_diff_and_print_sm_state(the_ghost_state_pre, the_ghost_state);
	}
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS */

	GHOST_LOG_CONTEXT_EXIT();

unlock:
	unlock_sm();
	ensure_atomic_unlock();
}


//////////////////////////
// Initialisation

static void initialise_ghost_simplified_model_options(void)
{
	ghost_sm_options.promote_DSB_nsh = true;
}

static void initialise_ghost_ptes_memory(phys_addr_t phys, u64 size) {
	GHOST_LOG_CONTEXT_ENTER();
	the_ghost_state->base_addr = phys;
	the_ghost_state->size = size;
	for (int i = 0; i < MAX_BLOBS; i++) {
		the_ghost_state->memory.blobs[i].valid = false;
	}
	is_initialised = true;
	GHOST_LOG_CONTEXT_EXIT();
}

/*
 * one-time synchronisation between the concrete memory
 * and the ghost simplified memory at the beginning of time.
 */
static void sync_simplified_model_memory(void)
{
	u64 pkvm_pgd;

	GHOST_LOG_CONTEXT_ENTER();
	pkvm_pgd = extract_s1_root(read_sysreg(ttbr0_el2));
	register_s1_root(pkvm_pgd);
	GHOST_LOG_CONTEXT_EXIT();
}

/*
 * perform some first-time ghost hint transitions
 */
static void initialise_ghost_hint_transitions(void)
{
	u64 pkvm_pgd;

	GHOST_LOG_CONTEXT_ENTER();
	pkvm_pgd = extract_s1_root(read_sysreg(ttbr0_el2));
	step_hint((struct ghost_simplified_model_transition){
		.src_loc = SRC_LOC, // report as coming from _here_
		.kind = TRANS_HINT,
		.hint_data = (struct trans_hint_data){
			.hint_kind = GHOST_HINT_SET_ROOT_LOCK,
			.location = pkvm_pgd,
			.value = (u64)&pkvm_pgd_lock,
		},
	});
	step_hint((struct ghost_simplified_model_transition){
		.src_loc = SRC_LOC, // report as coming from _here_
		.kind = TRANS_HINT,
		.hint_data = (struct trans_hint_data){
			.hint_kind = GHOST_HINT_SET_ROOT_LOCK,
			.location = (u64)hyp_virt_to_phys(host_mmu.pgt.pgd),
			.value = (u64)&host_mmu.lock,
		},
	});
	GHOST_LOG_CONTEXT_EXIT();
}


void initialise_ghost_simplified_model(phys_addr_t phys, u64 size, unsigned long sm_virt, u64 sm_size)
{
	lock_sm();
	GHOST_LOG_CONTEXT_ENTER();

	the_ghost_state = (struct ghost_simplified_model_state*)sm_virt;
	the_ghost_state_pre = the_ghost_state + 1;

	initialise_ghost_simplified_model_options();
	initialise_ghost_ptes_memory(phys, size);

	/* we can now start taking model steps */
	initialise_ghost_hint_transitions();
	sync_simplified_model_memory();

	GHOST_LOG_CONTEXT_EXIT();
	unlock_sm();
}

//////////////////////////////
//// Printers

int gp_print_write_trans(gp_stream_t *out, struct trans_write_data *write_data)
{
	char *kind = "";
	if (write_data->mo == WMO_release) {
		kind = "rel";
	}

	return ghost_sprintf(out, "W%s %p %lx", kind, write_data->phys_addr, write_data->val);
}

int gp_print_read_trans(gp_stream_t *out, struct trans_read_data *read_data)
{
	return ghost_sprintf(out, "Rs %p (=%lx)", read_data->phys_addr, read_data->val);
}

int gp_print_dsb_trans(gp_stream_t *out, enum dsb_kind *dsb_data)
{
	return ghost_sprintf(out, "%s", dsb_kind_names[*dsb_data]);
}

int gp_print_tlbi_trans(gp_stream_t *out, struct trans_tlbi_data *tlbi_data)
{
	const char *tlbi_kind = tlbi_kind_names[tlbi_data->tlbi_kind];
	switch (tlbi_data->tlbi_kind) {
		case TLBI_vale2is:
		case TLBI_vae2is:
		case TLBI_ipas2e1is:
			return ghost_sprintf(out, "%s pfn=%lx level=%ld", tlbi_kind, tlbi_data->page, tlbi_data->level);
		default:
			return ghost_sprintf(out, "%s", tlbi_kind);
	}

}

int gp_print_msr_trans(gp_stream_t *out, struct trans_msr_data *msr_data)
{
	return ghost_sprintf(out, "MSR %s %lx", sysreg_names[msr_data->sysreg], msr_data->val);
}

int gp_print_hint_trans(gp_stream_t *out, struct trans_hint_data *hint_data)
{
	const char *hint_name = hint_names[hint_data->hint_kind];

	switch (hint_data->hint_kind) {
	case GHOST_HINT_SET_ROOT_LOCK:
		return ghost_sprintf(out, "HINT %s %lx %lx", hint_name, hint_data->location, hint_data->value);
		break;
	default:
		return ghost_sprintf(out, "HINT %s", hint_name);
		;
	}
}

int gp_print_src_loc(gp_stream_t *out, struct src_loc *src_loc)
{
	return ghost_sprintf(out, "at %s:%d in %s", src_loc->file, src_loc->file, src_loc->func);
}

int gp_print_sm_trans(gp_stream_t *out, struct ghost_simplified_model_transition *trans)
{
	int ret;

	ret = gp_print_src_loc(out, &trans->src_loc);
	if (ret)
		return ret;

	ret = ghost_sprintf(out, " ");
	if (ret)
		return ret;

	switch (trans->kind) {
	case TRANS_MEM_WRITE:
		return gp_print_write_trans(out, &trans->write_data);
	case TRANS_MEM_READ:
		return gp_print_read_trans(out, &trans->read_data);
	case TRANS_DSB:
		return gp_print_dsb_trans(out, &trans->dsb_data);
	case TRANS_ISB:
		return ghost_sprintf(out, "ISB");
	case TRANS_TLBI:
		return gp_print_tlbi_trans(out, &trans->tlbi_data);
	case TRANS_MSR:
		return gp_print_msr_trans(out, &trans->msr_data);
	case TRANS_HINT:
		return gp_print_hint_trans(out, &trans->hint_data);
	default:
		BUG();
	};
}

// A helper for the GHOST_LOG and GHOST_WARN macros
// to print out a whole simplified model transition
void GHOST_transprinter(void *data)
{
	struct ghost_simplified_model_transition *trans = (struct ghost_simplified_model_transition *)data;
	ghost_printf("%g(sm_trans)", trans);
}

static const char *lis_names[] = {
	[LIS_unguarded] = "x",
	[LIS_dsbed] = "dsb'd",
	[LIS_dsb_tlbi_all] = "tlbi'd",
};

// Printers for sm state
int gp_print_invalid_unclean_state(gp_stream_t *out, struct aut_invalid *st)
{
	int ret;

	ret = ghost_sprintf(out, "Iunclean");
	if (ret)
		return ret;

	for (int i = 0; i < MAX_CPU; i++) {
		ret = ghost_sprintf(out, " %s", lis_names[st->lis[i]]);
		if (ret)
			return ret;
	}

	return 0;
}

int gp_print_sm_pte_state(gp_stream_t *out, struct sm_pte_state *st)
{
	switch (st->kind) {
	case STATE_PTE_INVALID:
		return ghost_sprintf(out, "I %ld", st->invalid_clean_state.invalidator_tid);
	case STATE_PTE_INVALID_UNCLEAN:
		return gp_print_invalid_unclean_state(out, &st->invalid_unclean_state);
	case STATE_PTE_VALID:
		return ghost_sprintf(out, "V");
	}
}

int gp_print_sm_loc(gp_stream_t *out, struct sm_location *loc)
{
	if (loc->is_pte) {
		return ghost_sprintf(out, "%p (desc:%lx st:%g(sm_pte_state) owner:%p)", loc->phys_addr, loc->val, &loc->state, loc->owner);
	} else {
		return ghost_sprintf(out, "%p %lx", loc->phys_addr, loc->val);
	}

}

int gp_print_sm_blob(gp_stream_t *out, struct ghost_memory_blob *b, u64 indent)
{
	int ret;

	if (!b->valid)
		return ghost_sprintf(out, "<invalid blob>");

	ret = ghost_sprintf(out, "%Iblob %p", indent, b->phys);
	if (ret)
		return ret;

	for (u64 i = 0; i < PAGES_PER_BLOB*SLOTS_PER_PAGE; i++) {
		struct sm_location *loc = &b->slots[i];
		// only show those that are ptes we're tracking
		if (!loc->is_pte)
			continue;

		ret = ghost_sprintf(out, "%I%g(sm_loc)\n", indent+2, loc);
		if (ret)
			return ret;
	}


	return 0;
}

int gp_print_sm_mem(gp_stream_t *out, struct ghost_simplified_memory *mem)
{
	int ret;
	ret = ghost_sprintf(out, "mem:\n");
	if (ret)
		return ret;

	for (int bi = 0; bi < MAX_BLOBS; bi++) {
		struct ghost_memory_blob *b = &mem->blobs[bi];
		ret = gp_print_sm_blob(out, b, 0);
		if (ret)
			return ret;
	}

	return 0;
}

int gp_print_sm_roots(gp_stream_t *out, char *name, u64 len, u64 *roots)
{
	int ret;

	ret = ghost_sprintf(out, "%s roots: [", name);
	if (ret)
		return ret;

	if (len > 0) {
		ret = ghost_sprintf(out, "%p", roots[0]);
		if (ret)
			return ret;

		for (u64 i = 1; i < len; i++) {
			ret = ghost_sprintf(out, ", %p", roots[i]);
			if (ret)
				return ret;
		}
	}

	return ghost_sprintf(out, "]");
}

int gp_print_sm_state(gp_stream_t *out, struct ghost_simplified_model_state *s)
{
	int ret;
	ret = ghost_sprintf(
		out,
	 	""
		"base_addr:.......%p\n"
		"size:............%lx\n"
		"nr_s1_roots:.....%lx\n"
		"nr_s2_roots:.....%lx\n",
		s->base_addr,
		s->size,
		s->nr_s1_roots,
		s->nr_s2_roots
	);
	if (ret)
		return ret;

	ret = gp_print_sm_roots(out, "s1", s->nr_s1_roots, s->s1_roots);
	if (ret)
		return ret;

	ret = gp_print_sm_roots(out, "s2", s->nr_s2_roots, s->s2_roots);
	if (ret)
		return ret;

	ret = gp_print_sm_mem(out, &s->memory);
	if (ret)
		return ret;

	/* TODO: owner locks */
	return 0;
}

void dump_sm_state(struct ghost_simplified_model_state *st)
{
	ghost_printf("%g(sm_state)\n", st);
}

/// Equality checks
bool sm_aut_invalid_eq(struct aut_invalid *i1, struct aut_invalid *i2)
{
	if (i1->invalidator_tid != i2->invalidator_tid)
		return false;

	if (i1->old_valid_desc != i2->old_valid_desc)
		return false;

	for (int i = 0; i < MAX_CPU; i++) {
		if (i1->lis[i] != i2->lis[i])
			return false;
	}

	return true;
}

bool sm_pte_state_eq(struct sm_pte_state *s1, struct sm_pte_state *s2)
{
	if (s1->kind != s2->kind)
		return false;

	switch (s1->kind) {
	case STATE_PTE_INVALID:
		return (s1->invalid_clean_state.invalidator_tid == s2->invalid_clean_state.invalidator_tid);
	case STATE_PTE_INVALID_UNCLEAN:
		return sm_aut_invalid_eq(&s1->invalid_unclean_state, &s2->invalid_unclean_state);
	case STATE_PTE_VALID:
		// TODO: per-CPU LVS
		return true;
	}
}

bool sm_loc_eq(struct sm_location *loc1, struct sm_location *loc2)
{
	if (loc1->phys_addr != loc2->phys_addr)
		return false;

	if (loc1->initialised != loc2->initialised)
		return false;

	if (loc1->initialised && (loc1->val != loc2->val))
		return false;

	if (loc1->is_pte != loc2->is_pte)
		return false;

	if (!sm_pte_state_eq(&loc1->state, &loc2->state))
		return false;

	return true;
}


/// Copying
void copy_sm_state_into(struct ghost_simplified_model_state *out)
{
	memcpy(out, the_ghost_state, sizeof(struct ghost_simplified_model_state));
}