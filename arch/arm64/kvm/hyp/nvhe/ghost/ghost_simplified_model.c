#include <linux/kvm_host.h>
#include <linux/types.h>

#include <asm/kvm.h>
#include <asm/kvm_pkvm.h>

#include <nvhe/spinlock.h>
#include <nvhe/memory.h>
#include <nvhe/mem_protect.h>
#include <nvhe/pkvm.h>
#include <nvhe/mm.h>

#include <nvhe/ghost/ghost_control.h>
#include <nvhe/ghost/ghost_asserts.h>
#include <nvhe/ghost/ghost_extra_debug-pl011.h>
#include <nvhe/ghost/ghost_printer.h>
#include <nvhe/ghost/ghost_spec.h>
#include <nvhe/ghost/ghost_abstraction_diff.h>
#include <nvhe/ghost/ghost_maplets.h>
#include <nvhe/ghost/ghost_pgtable.h>
#include <nvhe/ghost/ghost_simplified_model.h>

#pragma GCC diagnostic ignored "-Wdeclaration-after-statement"

#define OFFSET_IN_PAGE(x) (((x) & GENMASK(PAGE_SHIFT - 1, 0)))
#define IS_PAGE_ALIGNED(x) (OFFSET_IN_PAGE(x) == 0)

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

int transition_id = 0;

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


////////////////////
// Locks

gsm_lock_t *owner_lock(sm_owner_t owner_id)
{
	for (int i = 0; i < the_ghost_state->locks.len; i++) {
		if (the_ghost_state->locks.owner_ids[i] == owner_id) {
			return the_ghost_state->locks.locks[i];
		}
	}

	return NULL;
}

static void swap_lock(sm_owner_t root, gsm_lock_t *lock)
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

static void append_lock(sm_owner_t root, gsm_lock_t *lock)
{
	u64 i;

	if (owner_lock(root)) {
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("can't append lock on already locked location");
		BUG(); // unreachable;
	}

	i = the_ghost_state->locks.len++;
	ghost_assert(i < GHOST_SIMPLIFIED_MODEL_MAX_LOCKS)
	the_ghost_state->locks.owner_ids[i] = root;
	the_ghost_state->locks.locks[i] = lock;
}

static void associate_lock(sm_owner_t root, gsm_lock_t *lock)
{
	if (owner_lock(root)) {
		swap_lock(root, lock);
	} else {
		append_lock(root, lock);
	}
}

static void unregister_lock(u64 root)
{
	int len = the_ghost_state->locks.len;

	for (int i = 0; i < len; i++) {
		if (the_ghost_state->locks.owner_ids[i] == root) {
			len --;
			the_ghost_state->locks.owner_ids[i] = the_ghost_state->locks.owner_ids[len];
			the_ghost_state->locks.locks[i] = the_ghost_state->locks.locks[len];
			the_ghost_state->locks.len --;
			return;
		}
	}
	GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Tried to release a table which did not have a lock");
}

static bool is_correctly_locked(gsm_lock_t *lock, struct lock_state **state)
{
	for (int i = 0; i < the_ghost_state->lock_state.len; i++) {
		if (the_ghost_state->lock_state.address[i] == lock) {
			if (state != NULL) {
				*state = &the_ghost_state->lock_state.locker[i];
			}
			return the_ghost_state->lock_state.locker[i].id == cpu_id();
		}
	}
	return false;
}

static bool is_location_locked(struct sm_location *loc)
{
	if (!loc->initialised || !loc->is_pte)
		return true;

	// If the location is owned by a thread, check that it is this thread.
	if (loc->thread_owner >= 0)
		return loc->thread_owner == cpu_id();

	// Otherwise, get the owner of the location
	struct lock_state *state;
	sm_owner_t owner_id = loc->owner;
	// assume 0 cannot be a valid owner id
	if (!owner_id)
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("must have associated location with an owner");
	// get the address of the lock
	gsm_lock_t *lock = owner_lock(owner_id);
	// check the state of the lock
	return is_correctly_locked(lock, &state);
}

/**
 * assert_owner_locked() - Validates that the owner of a pte is locked by its lock.
 */
void assert_owner_locked(struct sm_location *loc, struct lock_state **state)
{
	ghost_assert(loc->initialised && loc->is_pte);
	sm_owner_t owner_id = loc->owner;
	// assume 0 cannot be a valid owner id
	if (!owner_id)
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("must have associated location with an owner");
	gsm_lock_t *lock = owner_lock(owner_id);
	if (!lock)
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("must have associated owner with an root");
	if (!is_correctly_locked(lock, state)) {
		ghost_printf_ext("%g(sm_loc)", loc);
		ghost_printf_ext("%g(sm_locks)", the_ghost_state->locks);
		
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("must write to pte while holding owner lock");
	}
}


#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
///////////
// Memory

#define BLOB_SIZE ((1UL) << BLOB_SHIFT)
#define BLOB_OFFSET_MASK GENMASK(BLOB_SHIFT - 1, 0)
#define ALIGN_DOWN_TO_BLOB(x) ((x) & ~BLOB_OFFSET_MASK)
#define OFFSET_IN_BLOB(x) ((x) & BLOB_OFFSET_MASK)
#define SLOT_OFFSET_IN_BLOB(x) (OFFSET_IN_BLOB(x) >> SLOT_SHIFT)

void copy_sm_state_into(struct ghost_simplified_model_state *out);

#ifdef CONFIG_NVHE_GHOST_SPEC_SAFETY_CHECKS
/*
 * A simple and slow, but very robust, sanity check over the blobs.
 */
static bool check_sanity_of_blobs(void)
{
	int c = 0;

	for (int i = 1; i < the_ghost_state->memory.nr_allocated_blobs; i++) {
		if (! (blob_of(&the_ghost_state->memory, i - 1)->phys < blob_of(&the_ghost_state->memory, i)->phys))
			return false;
	}


	for (int i = 0; i < MAX_BLOBS; i++) {
		if (the_ghost_state->memory.blobs_backing[i].valid)
			c++;
	}

	if (c != the_ghost_state->memory.nr_allocated_blobs)
		return false;

	return true;
}

static bool check_sanity_of_no_blob(u64 phys)
{
	u64 page = ALIGN_DOWN_TO_BLOB(phys);

	for (int i = 0; i < MAX_BLOBS; i++) {
		struct ghost_memory_blob *b = &the_ghost_state->memory.blobs_backing[i];
		if (b->valid && b->phys == page) {
			return false;
		}
	}

	return true;
}
#endif /* CONFIG_NVHE_GHOST_SPEC_SAFETY_CHECKS */

#define BLOBINDX(mem, i) ((mem)->ordered_blob_list[(i)])

struct ghost_memory_blob *blob_of(struct ghost_simplified_memory *mem, u64 i)
{
	return &mem->blobs_backing[BLOBINDX(mem, i)];
}

struct ghost_memory_blob *find_blob(struct ghost_simplified_memory *mem, u64 phys)
{
	int l, r;
	struct ghost_memory_blob *this;
	u64 page = ALIGN_DOWN_TO_BLOB(phys);

	l = 0;
	r = mem->nr_allocated_blobs - 1;

	/*
	 * as usual with binary search, it's easy until you need to stop
	 * going to m+1 or m-1 ensures we always make progress towards one end
	 */
	while (l <= r) {
		int m = (l + r) >> 1;
		this = blob_of(mem, m);

		if (this->phys < page) {
			l = m + 1;
		} else if (page == this->phys) {
			return this;
		} else if (page < this->phys) {
			r = m - 1;
		}
	}

	return NULL;
}

static void insert_blob_at_end(struct ghost_simplified_memory *mem, u64 b)
{
	mem->ordered_blob_list[mem->nr_allocated_blobs++] = b;
}

static int bubble_blob_down(struct ghost_simplified_memory *mem)
{
	int i;
	i = mem->nr_allocated_blobs;
	while (--i > 0 && blob_of(mem, i)->phys < blob_of(mem, i - 1)->phys) {
		int j = BLOBINDX(mem, i);
		BLOBINDX(mem, i) = BLOBINDX(mem, i - 1);
		BLOBINDX(mem, i - 1) = j;
	}

	return i;
}

static int get_free_blob(void)
{
	for (int i = 0; i < MAX_BLOBS; i++) {
		struct ghost_memory_blob *this = &the_ghost_state->memory.blobs_backing[i];
		if (!this->valid)
			return i;
	}

	GHOST_WARN("simplified model ran out of free blobs");
	ghost_assert(false);
	return 0;
}

static struct ghost_memory_blob *ensure_blob(u64 phys)
{
	u64 blob_phys = ALIGN_DOWN_TO_BLOB(phys);
	struct ghost_memory_blob *this;

	/* already one exists, done. */
	this = find_blob(&the_ghost_state->memory, blob_phys);
	if (this)
		return this;

	ghost_safety_check(check_sanity_of_no_blob(phys));

	// otherwise, have to grab a new blob and insert it into the table
	insert_blob_at_end(&the_ghost_state->memory, get_free_blob());
	this = blob_of(&the_ghost_state->memory, the_ghost_state->memory.nr_allocated_blobs - 1);
	ghost_assert(!this->valid);

	// and initialise it.
	this->valid = true;
	this->phys = blob_phys;
	// the slots are intentionally uninitialised;
	// as of yet, they haven't been "seen" by the simplified model
	// so let the first-seen checks initialise them.
	for (int i = 0; i < SLOTS_PER_PAGE; i++) {
		struct sm_location *slot = &this->slots[i];
		slot->initialised = false;
		slot->phys_addr = blob_phys + i*sizeof(u64);
	}

	// finally, we bubble it down in the ordered list
	// to maintain the sorted order
	bubble_blob_down(&the_ghost_state->memory);
	ghost_safety_check(check_sanity_of_blobs());

	return this;
}

bool blob_unclean(struct ghost_memory_blob *blob)
{
	for (int i = 0; i < SLOTS_PER_PAGE; i++) {
		if (blob->slots[i].is_pte && blob->slots[i].state.kind == STATE_PTE_INVALID_UNCLEAN)
			return true;
	}

	return false;
}

/**
 * location() - Read an address from the simplified model state.
 * @phys: the physical address.
 */
struct sm_location *location(u64 phys)
{
	struct ghost_memory_blob *blob = ensure_blob(phys);
	struct sm_location *loc = &blob->slots[SLOT_OFFSET_IN_BLOB(phys)];
	return loc;
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
	u64 *hyp_va;
	u64 hyp_val;

	// otherwise, convert to index in memory and get the val
	loc = location(addr);

	// Check that the location is well-locked
	if (! is_location_locked(loc))
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Tried to read a physical location without holding the lock");


	hyp_va = (u64*)hyp_phys_to_virt((phys_addr_t)addr);
	hyp_val = *hyp_va;

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
	// but we only need to check for locations we are supposedly tracking
	if (loc->is_pte && hyp_val != value) {
		GHOST_LOG_CONTEXT_ENTER();
		GHOST_LOG(hyp_va, u64);
		GHOST_LOG(value, u64);
		GHOST_LOG(hyp_val, u64);
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("the simplified model detected a PTE that changed under it");
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


static u64 discover_start_level(ghost_stage_t stage)
{
	if (stage == GHOST_STAGE2) {
		u64 vtcr = read_sysreg(vtcr_el2);
		return read_start_level(vtcr);
	} else {
		u64 tcr = read_sysreg(tcr_el2);
		return read_start_level(tcr);
	}
}

static u64 discover_page_size(ghost_stage_t stage)
{
	u64 tcr;
	u64 tg0;

	if (stage == GHOST_STAGE2) {
		tcr = read_sysreg(vtcr_el2);
	} else {
		tcr = read_sysreg(tcr_el2);
	}

	tg0 = (tcr & TCR_TG0_MASK) >> TCR_TG0_SHIFT;

	if (tg0 == 0) {
		return 4*1024;
	} else if (tg0 == 1) {
		return 64*1024;
	} else if (tg0 == 2) {
		return 16*1024;
	} else {
		BUG(); // unreachable;
	}
}

static u64 discover_nr_concatenated_pgtables(ghost_stage_t stage)
{
	/* stage1 is never concatenated */
	if (stage == GHOST_STAGE1)
		return 1;

	/* as per J.a D8-5832 */

	// assume pkvm has 4k graule
	ghost_assert(discover_page_size(GHOST_STAGE2) == PAGE_SIZE);

	// assume stage2 translations starting at level 0
	ghost_assert(discover_start_level(GHOST_STAGE2) == 0);

	u64 t0sz = (read_sysreg(vtcr_el2) & 0b111111);

	// now we know t0sz must be between 24 and 12.
	if (t0sz >= 16) {
		return 1;
	} else if (t0sz == 15) {
		return 2;
	} else if (t0sz == 14) {
		return 4;
	} else if (t0sz == 13) {
		return 8;
	} else if (t0sz == 12) {
		return 16;
	} else {
		BUG(); // unreachable;
	}
}

static bool is_desc_valid(u64 descriptor)
{
	return (descriptor & PTE_BIT_VALID) == PTE_BIT_VALID;
}

static bool is_desc_table(u64 descriptor, u64 level, ghost_stage_t stage)
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

struct ghost_exploded_descriptor deconstruct_pte(u64 partial_ia, u64 desc, u64 level, ghost_stage_t stage)
{
	struct ghost_exploded_descriptor deconstructed;

	deconstructed.ia_region = (struct ghost_addr_range){
		.range_start = partial_ia,
		.range_size = MAP_SIZES[level],
	};
	deconstructed.level = level;
	deconstructed.stage = stage;


	if (! is_desc_valid(desc)) {
		deconstructed.kind = PTE_KIND_INVALID;
		return deconstructed;
	} else if (is_desc_table(desc, level, stage)) {
		deconstructed.kind = PTE_KIND_TABLE;
		deconstructed.table_data.next_level_table_addr = extract_table_address(desc);
		return deconstructed;
	} else {
		deconstructed.kind = PTE_KIND_MAP;
		deconstructed.map_data.oa_region = (struct ghost_addr_range){
			.range_start = extract_output_address(desc, level),
			.range_size = MAP_SIZES[level],
		};
		ghost_mair_t mair;

		// for pKVM's own Stage 1 tables, the memory attributes are actually stored
		// in the indirection register (MAIR)
		if (stage == GHOST_STAGE1)
			// TODO: BS: read sysregs from simplified model not h/w
			//           they should be part of s1_roots or something?
			mair = read_mair(read_sysreg(mair_el2));
		else
			mair = no_mair();
		deconstructed.map_data.attrs = parse_attrs(stage, mair, desc, (u8)level, DUMMY_AAL);
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
	ghost_stage_t stage;

	void* data;
};

enum pgtable_traversal_flag {
	READ_UNLOCKED_LOCATIONS,
	NO_READ_UNLOCKED_LOCATIONS,
};

typedef void (*pgtable_traverse_cb)(struct pgtable_traverse_context *ctxt);

static void traverse_pgtable_from(u64 root, u64 table_start, u64 partial_ia, u64 level, ghost_stage_t stage, pgtable_traverse_cb visitor_cb, enum pgtable_traversal_flag flag, void *data)
{
	struct pgtable_traverse_context ctxt;

	GHOST_LOG_CONTEXT_ENTER();
	ctxt.root = root;
	ctxt.stage = stage;
	ctxt.data = data;
	ctxt.level = level;

	ghost_assert(IS_PAGE_ALIGNED(table_start));

	for (int i = 0; i < 512; i++) {
		u64 pte_phys;
		u64 desc;
		u64 pte_ia;

		struct sm_location *loc;

		GHOST_LOG_CONTEXT_ENTER_INNER("loop");
		GHOST_LOG_INNER("loop", i, u32);

		pte_phys = table_start + i*sizeof(u64);
		GHOST_LOG_INNER("loop", pte_phys, u64);

		loc = location(pte_phys);

		// If the location is owned by another thread, then don't keep going
		if (flag == NO_READ_UNLOCKED_LOCATIONS && loc->thread_owner >= 0 && loc->thread_owner != cpu_id()) {
			GHOST_LOG_CONTEXT_EXIT_INNER("loop");
			break;
		}

		desc = read_phys(pte_phys);
		GHOST_LOG_INNER("loop", desc, u64);


		/* this pte maps a region of MAP_SIZES[level] starting from here */
		pte_ia = partial_ia + i*MAP_SIZES[level];

		ctxt.loc = loc;
		ctxt.descriptor = desc;
		ctxt.exploded_descriptor = deconstruct_pte(pte_ia, desc, level, stage);
		ctxt.leaf = ctxt.exploded_descriptor.kind != PTE_KIND_TABLE;
		visitor_cb(&ctxt);

		/* visitor can't have changed the actual descriptor ... */
		ghost_safety_check(read_phys(pte_phys) == desc);

		switch (ctxt.exploded_descriptor.kind) {
		case PTE_KIND_TABLE:
			traverse_pgtable_from(
				root,
				ctxt.exploded_descriptor.table_data.next_level_table_addr,
				pte_ia,
				level+1,
				stage,
				visitor_cb,
				flag,
				data
			);
			break;
		case PTE_KIND_MAP:
		case PTE_KIND_INVALID:
		default:
			break;
		}
		GHOST_LOG_CONTEXT_EXIT_INNER("loop");
	}
	GHOST_LOG_CONTEXT_EXIT();
}

static void traverse_pgtable(u64 root, ghost_stage_t stage, pgtable_traverse_cb visitor_cb, enum pgtable_traversal_flag flag, void *data)
{
	u64 start_level;
	GHOST_LOG_CONTEXT_ENTER();

	start_level = discover_start_level(stage);
	GHOST_LOG(root, u64);
	GHOST_LOG(start_level, u64);

	// assume uses 4k granule, starting from level 0, without multiple concatenated pagetables
	ghost_assert(start_level == 0);
	ghost_assert(discover_page_size(stage) == PAGE_SIZE);
	ghost_assert(discover_nr_concatenated_pgtables(stage) == 1);

	traverse_pgtable_from(root, root, 0, start_level, stage, visitor_cb, flag, data);
	GHOST_LOG_CONTEXT_EXIT();
}

static void add_location_to_unclean_PTE(struct sm_location* loc)
{
	// Check that the location is not already in the set
	for (int i = 0; i < the_ghost_state->unclean_locations.len; i++) {
		if (loc == the_ghost_state->unclean_locations.locations[i]) {
			GHOST_WARN("A location was added twice to the unclean PTEs");
			ghost_assert(false);
		}
	}

	// Add it to the set
	ghost_assert(the_ghost_state->unclean_locations.len < MAX_UNCLEAN_LOCATIONS);
	the_ghost_state->unclean_locations.locations[the_ghost_state->unclean_locations.len] =
		loc;
	the_ghost_state->unclean_locations.len ++;


}

static struct pgtable_traverse_context construct_context_from_pte(struct sm_location *loc, void *data) {

	// Check that the location is consistent and well-locked
	u64 desc = read_phys(loc->phys_addr);

	struct pgtable_traverse_context ctx;
	ctx.loc = loc;
	ctx.descriptor = desc;
	ctx.exploded_descriptor = loc->descriptor;
	ctx.level = loc->descriptor.level;
	ctx.leaf = loc->descriptor.kind != PTE_KIND_TABLE;
	ctx.root = loc->owner;
	ctx.stage = loc->descriptor.stage;
	ctx.data = data;

	return ctx;
}


static void traverse_all_unclean_PTE(pgtable_traverse_cb visitor_cb, void* data, enum mapping_stage stage)
{
	struct sm_location *loc;
	u64 *len = &the_ghost_state->unclean_locations.len;

	for (int i = 0; i < *len; i++) {
		loc = the_ghost_state->unclean_locations.locations[i];

		ghost_assert(loc->initialised);
		ghost_assert(loc->is_pte);
		ghost_assert(loc->state.kind == STATE_PTE_INVALID_UNCLEAN);

		if (stage != GHOST_STAGE_NONE)
			if (stage != loc->descriptor.stage)
				break;



		// We rebuild the context from the descriptor of the location
		struct pgtable_traverse_context ctx = construct_context_from_pte(loc, data);
		
		visitor_cb(&ctx);
		
		// If the update resulted in cleaning the location, remove it from the list of
		// unclean locations
		if (loc->state.kind != STATE_PTE_INVALID_UNCLEAN) {
			// Take the last location of the list and put it in the current cell
			(*len)--;
			the_ghost_state->unclean_locations.locations[i] =
					the_ghost_state->unclean_locations.locations[*len];
			// decrement i to run on the current cell
			i--;
		}
	}
}


struct pgtable_walk_result {
	u64 requested_pte;
	bool found;

	struct ghost_exploded_descriptor descriptor;

	u64 root;
	ghost_stage_t stage;

	u64 level;
};

void finder_cb(struct pgtable_traverse_context *ctxt)
{
	struct pgtable_walk_result *result = (struct pgtable_walk_result*)ctxt->data;
	if (ctxt->loc->phys_addr == result->requested_pte) {
		result->found = true;
		result->root = ctxt->root;
		result->descriptor = ctxt->exploded_descriptor;
		result->stage = ctxt->stage;
		result->level = ctxt->level;
	}
}

struct pgtable_walk_result find_pte(struct sm_location *loc)
{
	struct pgtable_walk_result result;
	result.found = false;
	result.requested_pte = loc->phys_addr;

	ghost_assert(loc->initialised && loc->is_pte);

	traverse_pgtable(loc->owner, loc->descriptor.stage, finder_cb, NO_READ_UNLOCKED_LOCATIONS, &result);

	return result;
}

/**
 * initial_state() - Construct an initial sm_pte_state for a clean descriptor.
 */
struct sm_pte_state initial_state(u64 partial_ia, u64 desc, u64 level, ghost_stage_t stage)
{
	struct sm_pte_state state;
	struct ghost_exploded_descriptor deconstructed = deconstruct_pte(partial_ia, desc, level, stage);
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
		BUG(); // unreachable;
	}

	return state;
}


///////////////////
// TLB maintenance

enum sm_tlbi_op_method_kind decode_tlbi_method_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_vmalle1is:
	case TLBI_vmalle1:
		return TLBI_OP_BY_ADDR_SPACE;

	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_ipas2e1is:
		return TLBI_OP_BY_INPUT_ADDR;

	case TLBI_alle1is:
		return TLBI_OP_BY_ALL;

	default:
		BUG();  // TODO: missing kind
	}
}

bool decode_tlbi_shootdown_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vmalls12e1is:
	case TLBI_vmalle1is:
	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_ipas2e1is:
	case TLBI_alle1is:
		return true;

	case TLBI_vmalls12e1:
	case TLBI_vmalle1:
		return false;

	default:
		BUG();  // TODO: missing kind
	}
}

enum sm_tlbi_op_stage decode_tlbi_stage_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_vmalle1is:
	case TLBI_vmalle1:
		return TLBI_OP_STAGE1;

	case TLBI_ipas2e1is:
		return TLBI_OP_STAGE2;

	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_alle1is:
		return TLBI_OP_BOTH_STAGES;

	default:
		BUG();  // TODO: missing kind
	}
}

enum sm_tlbi_op_regime_kind decode_tlbi_regime_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vale2is:
	case TLBI_vae2is:
		return TLBI_REGIME_EL2;

	case TLBI_vmalle1is:
	case TLBI_vmalle1:
	case TLBI_ipas2e1is:
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_alle1is:
		return TLBI_REGIME_EL10;

	default:
		BUG();  // TODO: missing kind
	}
}

struct tlbi_op_method_by_address_data decode_tlbi_by_addr(struct trans_tlbi_data data)
{
	struct tlbi_op_method_by_address_data decoded_data = {0};

	decoded_data.page = data.page;

	switch (data.tlbi_kind) {
	case TLBI_vale2is:
		decoded_data.affects_last_level_only = true;
		break;
	default:
		decoded_data.affects_last_level_only = false;
		break;
	}

	decoded_data.page = data.page;

	if (data.level < 0b0100) {
		decoded_data.has_level_hint = false;
	} else {
		decoded_data.has_level_hint = true;
		decoded_data.level_hint = data.level & 0b11;
	}

	return decoded_data;
}

struct tlbi_op_method_by_address_space_id_data decode_tlbi_by_space_id(struct trans_tlbi_data data)
{
	struct tlbi_op_method_by_address_space_id_data decoded_data = {0};
	decoded_data.asid_or_vmid = 0;
	return decoded_data;
}


struct sm_tlbi_op decode_tlbi(struct trans_tlbi_data data)
{
	struct sm_tlbi_op tlbi;

	tlbi.stage = decode_tlbi_stage_kind(data.tlbi_kind);
	tlbi.regime = decode_tlbi_regime_kind(data.tlbi_kind);
	tlbi.shootdown = decode_tlbi_shootdown_kind(data.tlbi_kind);
	tlbi.method.kind = decode_tlbi_method_kind(data.tlbi_kind);
	switch (tlbi.method.kind) {
	case TLBI_OP_BY_INPUT_ADDR:
		tlbi.method.by_address_data = decode_tlbi_by_addr(data);
		break;

	case TLBI_OP_BY_ADDR_SPACE:
		tlbi.method.by_id_data = decode_tlbi_by_space_id(data);
		break;

	default:
		BUG(); // TODO: missing kind (TLBI ALL?)
	}

	return tlbi;
}


/////////////////////
// BBM requirements

static bool is_only_update_to_sw_bits(u64 before, u64 after)
{
	return (before & ~PTE_FIELD_UPPER_ATTRS_SW_MASK) == (after & ~PTE_FIELD_UPPER_ATTRS_SW_MASK);
}


/**
 * requires_bbm() - Whether a break-before-make sequence is architecturally required between two writes.
 * @loc: the memory location.
 * @before: the value of the first write.
 * @after: the value of the second write.
 *
 * See ARM DDI 0487 J.a D8.14.1 ("Using break-before-make when updating translation table entries")
 */
static bool requires_bbm(struct sm_location *loc, u64 before, u64 after)
{
	struct ghost_exploded_descriptor before_descriptor = deconstruct_pte(loc->descriptor.ia_region.range_start, before, loc->descriptor.level, loc->descriptor.stage);
	struct ghost_exploded_descriptor after_descriptor = deconstruct_pte(loc->descriptor.ia_region.range_start, after, loc->descriptor.level, loc->descriptor.stage);

	/* BBM is only a requirement between writes of valid PTEs */
	if (before_descriptor.kind == PTE_KIND_INVALID || after_descriptor.kind == PTE_KIND_INVALID)
		return false;

	/* if one is a table entry, really need to BBM between */
	if (before_descriptor.kind == PTE_KIND_TABLE || after_descriptor.kind == PTE_KIND_TABLE)
		return true;

	ghost_assert(before_descriptor.kind == PTE_KIND_MAP);
	ghost_assert(after_descriptor.kind == PTE_KIND_MAP);

	/* if a change in OA */
	if (before_descriptor.map_data.oa_region.range_size != after_descriptor.map_data.oa_region.range_size) {
		// TODO: BS: this is overapproximate,
		//           should be: "and if at least one is writeable, or memory contents different"
		return true;
	}

	// TODO: BS: a change in memory type, shareability, or cacheability
	// TODO: BS: FEAT_BBM (?)
	// TODO: BS: global entries (?)
	// over approximate all of the above, by checking everything same except maybe SW bits.
	if (! is_only_update_to_sw_bits(before, after))
		return true;

	return false;
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
 * if loc (was) a table entry, traverse the old children
 * and check they were all clean (VALID or INVALID, but not INVALID_UNCLEAN).
 */
static bool pre_all_reachable_clean(struct sm_location *loc)
{
	bool all_clean;

	if (! loc->is_pte)
		return true;

	// sanity check: it's actually in a tree somewhere...
	// If the location is not owned by a thread, check that we can reach it by walking
	// from the registered root. 
	if (loc->thread_owner == -1) {
		struct pgtable_walk_result pte = find_pte(loc);
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
		loc->descriptor.stage,
		clean_reachability_checker_cb,
		READ_UNLOCKED_LOCATIONS,
		&all_clean
	);

	// NOTE: the traversal may have unset all_clean.
	return all_clean;
}

/**
 * Callback to mark a location in the page table as a page table entry
 * in the simplified model.
*/
void mark_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised) {
		// if this was the first time we saw it
		// initialise it and copy in the value
		loc->initialised = true;
		// by default, the location is not owned by any thread
		loc->thread_owner = -1;

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
	loc->owner = (sm_owner_t)ctxt->root;
	loc->descriptor = ctxt->exploded_descriptor;
	loc->state = initial_state(ctxt->exploded_descriptor.ia_region.range_start, ctxt->descriptor, ctxt->level, ctxt->stage);
}

void unmark_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised) {
		// if this was the first time we saw it
		// initialise it and copy in the value
		loc->initialised = true;
		// by default, the location is not owned by any thread
		loc->thread_owner = -1;
	} else if (! loc->is_pte) {
		// TODO: BS: is this catch-fire or simply unreachable?
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("unmark non-PTE");
	}

	// mark that this location is no longer an active pte
	// and stop following the automata
	loc->is_pte = false;
}

/**
 * walker function to mark the PTE as not writable. This function is not exercised in
 * pKVM.
 */
void mark_not_writable_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (loc->thread_owner >= 0)
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE(
				"The parent of an entry that is owned by a thread has been invalidated"
			);

	if (! loc->initialised) {
		// unreachable
		BUG();
	} else if (!loc->is_pte) {
		// unreachable
		BUG();
	} else {
		// mark the child as not writable
		loc->state.kind = STATE_PTE_NOT_WRITABLE;
	}
}

///////////////////
// Pagetable roots

static bool root_exists_in(u64 *root_table, phys_addr_t root)
{
	for (int i = 0; i < MAX_ROOTS; i++) {
		if (root_table[i] == root)
			return true;
	}

	return false;
}

static bool root_exists(phys_addr_t root)
{
	return root_exists_in(the_ghost_state->s1_roots, root) || root_exists_in(the_ghost_state->s2_roots, root);
}

static void try_insert_root(u64 *root_table, u64 root)
{
	for (int i = 0; i < MAX_ROOTS; i++) {
		if (root_table[i] == 0) {
			root_table[i] = root;
			return;
		}
	}

	GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("cannot insert more than MAX_ROOT roots");
}

static void try_remove_root(u64 *root_table, u64 root)
{
	for (int i = 0; i < MAX_ROOTS; i++) {
		if (root_table[i] == root) {
			root_table[i] = 0;
			return;
		}
	}

	GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("cannot insert more than MAX_ROOT roots");
}


static void try_register_root(ghost_stage_t stage, phys_addr_t root)
{
	GHOST_LOG_CONTEXT_ENTER();
	if (root_exists(root))
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("root already exists");

	u64 *root_table =
		stage == GHOST_STAGE2 ? the_ghost_state->s2_roots : the_ghost_state->s1_roots;

	// TODO: also associate ASID/VMID ?
	try_insert_root(root_table, root);

	if (stage == GHOST_STAGE1) {
		the_ghost_state->nr_s1_roots++;
	} else {
		the_ghost_state->nr_s2_roots++;
	}

	traverse_pgtable(root, stage, mark_cb, READ_UNLOCKED_LOCATIONS, NULL);
	GHOST_LOG_CONTEXT_EXIT();
}

static void try_unregister_root(ghost_stage_t stage, phys_addr_t root)
{
	GHOST_LOG_CONTEXT_ENTER();

	u64 *root_table =
		stage == GHOST_STAGE2 ? the_ghost_state->s2_roots : the_ghost_state->s1_roots;

	if (! root_exists_in(root_table, root))
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("root doesn't exist");

	// TODO: also associate ASID/VMID ?
	traverse_pgtable(root, stage, unmark_cb, READ_UNLOCKED_LOCATIONS, NULL);
	try_remove_root(root_table, root);
	if (stage == GHOST_STAGE1) {
		the_ghost_state->nr_s1_roots--;
	} else {
		the_ghost_state->nr_s2_roots--;
	}
	GHOST_LOG_CONTEXT_EXIT();
}
#endif /*CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */


////////////////////
// Step write sysreg

#define VTTBR_EL2_BADDR_MASK	(GENMASK(47, 1))

static phys_addr_t extract_s2_root(u64 vttb)
{
	return vttb & VTTBR_EL2_BADDR_MASK;
}

#define TTBR0_EL2_BADDR_MASK	(GENMASK(47, 1))

static phys_addr_t extract_s1_root(u64 ttb)
{
	return ttb & TTBR0_EL2_BADDR_MASK;
}

#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
static void step_msr(struct ghost_simplified_model_transition trans)
{
	u64 root;
	// TODO: BS: also remember which is current?
	switch (trans.msr_data.sysreg) {
	case SYSREG_TTBR_EL2:
		root = extract_s1_root(trans.msr_data.val);

		if (! root_exists_in(the_ghost_state->s1_roots, root)) {
			try_register_root(GHOST_STAGE1, root);
		}
		// TODO: BS: else, at least check ASID/VMID match...

		break;
	case SYSREG_VTTBR:
		root = extract_s2_root(trans.msr_data.val);

		if (! root_exists_in(the_ghost_state->s2_roots, root)) {
			try_register_root(GHOST_STAGE2, root);
		}
		// TODO: BS: else, at least check ASID/VMID match...

		break;
	default:
		BUG(); // unreachable?
	}
}

////////////////////////
// Step on memory write

static void __update_descriptor_on_write(struct sm_location *loc, u64 val)
{
	loc->descriptor = deconstruct_pte(loc->descriptor.ia_region.range_start, val, loc->descriptor.level, loc->descriptor.stage);
}

/*
 * when writing a new table entry
 * must ensure that the child table(s) are all clean
 * and not owned by another pgtable
 * then mark them as owned
 */
static void step_write_table_mark_children(pgtable_traverse_cb visitor_cb, struct sm_location *loc)
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
			loc->descriptor.stage,
			visitor_cb,
			READ_UNLOCKED_LOCATIONS,
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

	// update the descriptor
	__update_descriptor_on_write(loc, val);

	// check that if we're writing a TABLE entry
	// that the new tables are all 'good'
	step_write_table_mark_children(mark_cb, loc);

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
	u64 old = read_phys_pre(loc->phys_addr);

	if (is_desc_valid(val)) {
		if (! requires_bbm(loc, old, val)) {
			return;
		}

		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("BBM valid->valid");
	}

	loc->state.kind = STATE_PTE_INVALID_UNCLEAN;
	loc->state.invalid_unclean_state = (struct aut_invalid) {
		.invalidator_tid = cpu_id(),
		.old_valid_desc = old,
		.lis = LIS_unguarded
	};

	// Add location to the list of unclean locations
	add_location_to_unclean_PTE(loc);

	step_write_table_mark_children(mark_not_writable_cb, loc);
}


static void step_write_on_unwritable(struct sm_location *loc, u64 val) {
	// If the write does not change anything, continue
	if (loc->val == val)
		return;

	// Writing invalid on invalid is also benign
	if ((! is_desc_valid(loc->val)) && (! is_desc_valid(val)))
		return;

	// You can't change an unwritable descriptor. 
	GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Wrote on a page with an unclean parent");
}

static void write_is_authorized(struct sm_location *loc, struct ghost_simplified_model_transition trans, u64 val)
{
	struct lock_state *state_of_lock;

	// if the location is owned by a given thread, just test if it is this one
	if (loc->thread_owner >= 0) {
		if (loc->thread_owner == cpu_id())
			// Write unauthorized to change?
			return;
		else
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Location owned by a thread but accessed by another");
	}

	assert_owner_locked(loc, &state_of_lock);
	switch (state_of_lock->write_authorization) {
		case AUTHORIZED:
			// We are not authorized to write plain on it anymore
			state_of_lock->write_authorization = UNAUTHORIZED_PLAIN_VALID;
			break;
		case UNAUTHORIZED_PLAIN_VALID:
			// We cannot write plain (exept invalid on invalid)
			if (trans.write_data.mo == WMO_plain) {
				if (loc->state.kind == STATE_PTE_VALID || is_desc_valid(val))
					GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Wrote plain without authorization");
			}
			break;
		default:
			BUG();
	}
}

static void __step_write(struct ghost_simplified_model_transition trans)
{
	enum memory_order_t mo = trans.write_data.mo;
	u64 val = trans.write_data.val;

	// look inside memory at `addr`
	struct sm_location *loc = location(trans.write_data.phys_addr);

	if (!loc->is_pte) {
		goto done;
	}

	// must own the lock on the pgtable this pte is in.
	write_is_authorized(loc, trans, val);

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
	case STATE_PTE_NOT_WRITABLE:
		step_write_on_unwritable(loc, val);
		break;
	default:
		BUG(); // unreachable;
	}

done:
	loc->val = val;
	return;
}

static void __step_write_memset(u64 phys_addr, u64 val)
{
	ghost_assert(IS_PAGE_ALIGNED(phys_addr));
	for (int i = 0; i < 512; i++) {
		__step_write((struct ghost_simplified_model_transition){
			.kind = TRANS_MEM_WRITE,
			.write_data = (struct trans_write_data){
				.mo=WMO_plain,
				.phys_addr=phys_addr+i*sizeof(u64),
				.val=val
			}
		});
	}

}

static void step_write(struct ghost_simplified_model_transition trans)
{
	switch (trans.write_data.mo) {
	case GHOST_MEMSET_PAGE:
		__step_write_memset(trans.write_data.phys_addr, trans.write_data.val);
		break;

	case WMO_plain:
	case WMO_release:
		__step_write(trans);
		break;

	default:
		BUG(); // unreachable
	}
}

////////////////////////
// Step on memory read

static void step_read(struct ghost_simplified_model_transition trans)
{
	struct sm_location *loc = location(trans.read_data.phys_addr);

	// read doesn't have any real behaviour, except to return the value stored in memory.
	// so we just assert that the value in the real concrete memory is what we are tracking.
	// (the read_phys already does this check, but it's never bad to double check).
	ghost_assert(read_phys(loc->phys_addr) == loc->val);
}

/////////////////
// Step on a DSB

/*
 * when invalidating a zeroed table entry
 * unmark them as now no longer owned by the parent
 *
 * TODO: BS: is this correct?
 * TODO: TF: This is not tested as pKVM does not invalidate table descriptors.
 */
static void step_dsb_invalid_unclean_unmark_children(struct sm_location *loc)
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
	old_desc = deconstruct_pte(loc->descriptor.ia_region.range_start, old, loc->descriptor.level, loc->descriptor.stage);


	// look at the old entry, and see if it was a table.
	if (old_desc.kind == PTE_KIND_TABLE) {
		// if we zero child entry, then zero the table entry
		// require that the child entries were TLBI'd first.
		// this means we don't have to recursively check the olds all the way down...
		// TODO: BS: is this too strong?
		if (! pre_all_reachable_clean(loc)) {
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("BBM write table descriptor with unclean children");
		}

		traverse_pgtable_from(
			loc->owner,
			old_desc.table_data.next_level_table_addr,
			loc->descriptor.ia_region.range_start,
			loc->descriptor.level,
			loc->descriptor.stage,
			unmark_cb,
			READ_UNLOCKED_LOCATIONS,
			NULL);
	}

	GHOST_LOG_CONTEXT_EXIT();
}


void dsb_visitor(struct pgtable_traverse_context *ctxt)
{
	thread_identifier this_cpu = cpu_id();
	struct sm_location *loc = ctxt->loc;
	enum dsb_kind dsb_kind = *(enum dsb_kind *)ctxt->data;


	// If the location is not locked then do not do anything
	if (!is_location_locked(ctxt->loc))
		return;

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

		switch (loc->state.invalid_unclean_state.lis) {
		case LIS_unguarded:
			// if not yet DSBd, then tick it forward
			loc->state.invalid_unclean_state.lis = LIS_dsbed;
			break;
		case LIS_dsb_tlbied:
			// if DSB+TLBI'd already, this DSB then propagates that TLBI everywhere,
			// but only if it's the right kind of DSB
			// also release the children
			if (dsb_kind == DSB_ish) {
				// All the children can be released
				step_dsb_invalid_unclean_unmark_children(loc);
				// The PTE is now clean
				loc->state.kind = STATE_PTE_INVALID;
				loc->state.invalid_clean_state.invalidator_tid = this_cpu;
				// So the new descriptor is the only one visible
				__update_descriptor_on_write(loc, loc->val);
			}
			break;
		case LIS_dsb_tlbi_ipa:
			// if DSB+TLBI IPA, then advance the state locally so the next TLBI can happen.
			// but only if it's the right kind of DSB
			if (dsb_kind == DSB_ish) {
				loc->state.invalid_unclean_state.lis = LIS_dsb_tlbi_ipa_dsb;
			}
			break;
		default:
			break;
		}
		break;
	default:
		break;
	}
}

static void reset_write_authorizations(void) {
	int len = the_ghost_state->lock_state.len;
	struct lock_state *states = the_ghost_state->lock_state.locker;
	for (int i = 0; i < len; i++) {
		if (states[i].id == cpu_id())
			states[i].write_authorization = AUTHORIZED;
	}
}

static void step_dsb(struct ghost_simplified_model_transition trans)
{
	// annoyingly, DSBs aren't annotated with their addresses.
	// so we do the really dumb thing: we go through every pagetable that we know about
	// and step any we find in the right state.
	traverse_all_unclean_PTE(dsb_visitor, &trans.dsb_data, GHOST_STAGE_NONE);

	// The DSBs also enforce a sufficient barrier to allow plain writes again
	reset_write_authorizations();
}

///////////////////
// Step on a TLBI

static void step_pte_on_tlbi_after_dsb(struct sm_location *loc, struct sm_tlbi_op *tlbi)
{
	switch (tlbi->regime) {
	case TLBI_REGIME_EL2:
		loc->state.invalid_unclean_state.lis = LIS_dsb_tlbied;
		break;

	case TLBI_REGIME_EL10:
		switch (tlbi->stage) {
		case TLBI_OP_STAGE1:
			/* stage1 invalidation before stage2 invalidation is ineffective */
			break;

		case TLBI_OP_STAGE2:
			/* stage2 invalidation alone only invalidates those ipas */
			loc->state.invalid_unclean_state.lis = LIS_dsb_tlbi_ipa;
			break;

		case TLBI_OP_BOTH_STAGES:
			loc->state.invalid_unclean_state.lis = LIS_dsb_tlbied;
			break;

		default:
			BUG(); // unreachable;
		}
		break;

	default:
		BUG(); // unreachable;
	}

}

static void step_pte_on_tlbi_after_tlbi_ipa(struct sm_location *loc, struct sm_tlbi_op *tlbi)
{
	ghost_assert(tlbi->regime == TLBI_REGIME_EL10);

	switch (tlbi->stage) {
	case TLBI_OP_STAGE1:
	case TLBI_OP_BOTH_STAGES:
		loc->state.invalid_unclean_state.lis = LIS_dsb_tlbied;
		break;

	case TLBI_OP_STAGE2:
		/* additional second-stage invalidation has no added effect */
		break;

	default:
		BUG(); // unreachable;
	}
}

static void step_pte_on_tlbi(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;
	struct sm_tlbi_op *tlbi = (struct sm_tlbi_op*)ctxt->data;

	thread_identifier this_cpu = cpu_id();

	// sanity check: if doing a TLBI on a tree with a root we know about
	// then all the children in that tree must have been marked by the (V)TTBR registration
	// or the writes of table entries...
	ghost_assert(loc->initialised);

	switch (loc->state.kind) {
	case STATE_PTE_INVALID_UNCLEAN:
		// if the core that did the unclean write to this pte is not the core doing the tlbi
		// then that tlbi has no effect in the simplified model
		if (loc->state.invalid_unclean_state.invalidator_tid != this_cpu)
			return;

		// TODO: BS: finish dispatch on (loc LIS * TLBI kind)
		switch (loc->state.invalid_unclean_state.lis) {
		// trying to do a TLBI without having done a DSB has no effect
		case LIS_unguarded:
			return;
		case LIS_dsbed:
			step_pte_on_tlbi_after_dsb(loc, tlbi);
			break;
		case LIS_dsb_tlbi_ipa_dsb:
			step_pte_on_tlbi_after_tlbi_ipa(loc, tlbi);
			break;
		default:
			BUG();  // TODO: BS: other TLBIs
		}

		break;
	default:
		/* if clean, no effect */
		break;
	}
}


static bool all_children_invalid(struct sm_location *loc)
{
	// Assert that we are on a table descriptor
	ghost_assert(loc->initialised && loc->is_pte);
	
	if (loc->descriptor.kind != PTE_KIND_TABLE)
		return true;

	phys_addr_t table_addr = loc->descriptor.table_data.next_level_table_addr;
	struct sm_location *child;


	for (int i = 0; i< 512; i++) {
		// For each child, check that it is an invalid child
		child = location(table_addr + 8 * i);
		ghost_assert(child->initialised && child->is_pte);
		ghost_assert(child->state.kind == STATE_PTE_NOT_WRITABLE)
		if (child->descriptor.kind != PTE_KIND_INVALID) {
			return false;
		}
	}

	return true;
}

static bool should_perform_tlbi(struct pgtable_traverse_context *ctxt)
{
	u64 tlbi_addr;
	u64 ia_start;
	u64 ia_end;

	// If the location is not locked then do not apply the TLBI
	if (!is_location_locked(ctxt->loc))
		return false;

	struct sm_tlbi_op *tlbi = (struct sm_tlbi_op*)ctxt->data;

	// TODO: BS: need to match up regime with which pgtable loc is in.
	//           and broadcast and so on.

	if (!tlbi->shootdown) {
		if (ghost_sm_options.promote_TLBI_nsh) {
			tlbi->shootdown = true;
		} else {
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Unsupported TLBI (expected broadcast)");
		}
	}

	if (tlbi->method.kind == TLBI_OP_BY_ADDR_SPACE) {
		if (ghost_sm_options.promote_TLBI_by_id) {
			tlbi->method.kind = TLBI_OP_BY_ALL;
		} else {
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Unsupported TLBI-by-(AS/VM)ID");
		}
	}

	switch (tlbi->method.kind) {
	case TLBI_OP_BY_INPUT_ADDR:
		// input-address range of the PTE we're visiting
		ia_start = ctxt->exploded_descriptor.ia_region.range_start;
		ia_end = ia_start + ctxt->exploded_descriptor.ia_region.range_size;
		tlbi_addr = tlbi->method.by_address_data.page << PAGE_SHIFT;



		// If the PTE has valid children, the TLBI by VA is not enough
		if (! ctxt->leaf) {
			if (! all_children_invalid(ctxt->loc)) {
				return false;
			}
		}

		// Test if the VA address of the PTE is the same as the VA of the TLBI
		if (! ((ia_start <= tlbi_addr) && (tlbi_addr < ia_end))) {
			return false;
		}

		/*
		 * if it is a leaf, but not at the last level, and we asked for last-level-only invalidation,
		 * then nothing happens
		 */
		if (ctxt->level != 3 && tlbi->method.by_address_data.affects_last_level_only) {
			return false;
		}

		break;

	case TLBI_OP_BY_ADDR_SPACE:
		BUG(); // TODO: BS: by-VMID and by-ASID

	case TLBI_OP_BY_ALL:
		return true;

	default:
		BUG(); // unreachable;
	}

	return true;
}

static void tlbi_visitor(struct pgtable_traverse_context *ctxt)
{
	GHOST_LOG_CONTEXT_ENTER();

	if (should_perform_tlbi(ctxt)) {
		step_pte_on_tlbi(ctxt);
	}

	GHOST_LOG_CONTEXT_EXIT();
}

static void step_tlbi(struct ghost_simplified_model_transition trans)
{
	ghost_assert(trans.kind == TRANS_TLBI);

	struct sm_tlbi_op decoded = decode_tlbi(trans.tlbi_data);

	switch (decoded.regime) {
	/* TLBIs that hit host/guest tables */
	case TLBI_REGIME_EL10:
		traverse_all_unclean_PTE(tlbi_visitor, &decoded, GHOST_STAGE2);
		break;

	/* TLBIs that hit pKVM's own pagetable */
	case TLBI_REGIME_EL2:
		traverse_all_unclean_PTE(tlbi_visitor, &decoded, GHOST_STAGE1);
		break;

	default:
		BUG(); // unreachable;
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

static void step_hint_set_root_lock(u64 root, gsm_lock_t *lock)
{
	// TODO: BS: on teardown a VM's lock might get disassociated,
	// then re-associated later with a different lock.
	//
	// currently this just swaps the lock over without any safety checks.
	associate_lock(root, lock);
}

static void step_hint_set_owner_root(u64 phys, u64 root)
{
	// the whole page should be owned by the same owner
	// but in the simplified model, the metadata is split by 64-bit location,
	// so we iterate to set all in the same page.
	for (u64 p = PAGE_ALIGN_DOWN(phys); p < PAGE_ALIGN(phys); p += sizeof(kvm_pte_t)) {
		struct sm_location *loc = location(p);

		// TODO: BS: before letting us disassociate a pte with a given VM/tree,
		// first we need to check that it's clean enough to forget about
		// the association with the old VM

		loc->owner = root;
	}
}

void check_release_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	ghost_assert(loc->initialised);
	ghost_assert(loc->is_pte);

	if (loc->state.kind == STATE_PTE_INVALID_UNCLEAN)
		GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("cannot release table where children are still unclean");
}

static void step_hint_release_table(u64 root)
{
	struct sm_location *loc = location(root);

	// TODO: BS: also check that it's not currently in-use by someone

	// need to check the table is clean.
	traverse_pgtable_from(
		root,
		loc->owner,
		loc->descriptor.ia_region.range_size,
		loc->descriptor.level,
		loc->descriptor.stage,
		check_release_cb,
		READ_UNLOCKED_LOCATIONS,
		NULL);
	try_unregister_root(loc->descriptor.stage, root);

	// remove the mapping from the root to the lock of the page-table
	unregister_lock(root);
}

static void step_hint_set_PTE_thread_owner(u64 phys, u64 val)
{
	// TODO: mark all the parents as immutable
	struct sm_location *loc = location(phys);

	ghost_assert(loc->initialised);
	ghost_assert(loc->is_pte);
	ghost_assert(loc->descriptor.level == 3);

	loc->thread_owner = val;
}

static void step_hint(struct ghost_simplified_model_transition trans)
{
	switch (trans.hint_data.hint_kind) {
	case GHOST_HINT_SET_ROOT_LOCK:
		step_hint_set_root_lock(trans.hint_data.location, (gsm_lock_t *)trans.hint_data.value);
		break;
	case GHOST_HINT_SET_OWNER_ROOT:
		step_hint_set_owner_root(trans.hint_data.location, trans.hint_data.value);
		break;
	case GHOST_HINT_RELEASE_TABLE:
		step_hint_release_table(trans.hint_data.location);
		break;
	case GHOST_HINT_SET_PTE_THREAD_OWNER:
		step_hint_set_PTE_thread_owner(trans.hint_data.location, trans.hint_data.value);
		break;
	default:
		BUG(); // unreachable;
	}
}

//////////////////////
// LOCK

static void __step_lock(gsm_lock_t *lock_addr)
{
	int len = the_ghost_state->lock_state.len;
	// look for the address in the map
	for (int i = 0; i < len; i++)
	{
		if (the_ghost_state->lock_state.address[i] == lock_addr) {
			GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Tried to lock a component that was alerady held");
		}
	}
	// If the lock is not yet in the map, we append it
	ghost_assert(len < GHOST_SIMPLIFIED_MODEL_MAX_LOCKS);

	the_ghost_state->lock_state.address[len] = lock_addr;
	the_ghost_state->lock_state.locker[len].id = cpu_id();
	the_ghost_state->lock_state.locker[len].write_authorization = AUTHORIZED;

	the_ghost_state->lock_state.len ++;

}

static void __step_unlock(gsm_lock_t *lock_addr)
{
	int len = the_ghost_state->lock_state.len;
	// look for the address in the map
	for (int i = 0; i < len; i++)
	{
		if (the_ghost_state->lock_state.address[i] == lock_addr) {
			if (the_ghost_state->lock_state.locker[i].id == cpu_id()){
				// unlock the position
				len--;
				the_ghost_state->lock_state.locker[i] = the_ghost_state->lock_state.locker[len];
				the_ghost_state->lock_state.address[i] = the_ghost_state->lock_state.address[len];
				the_ghost_state->lock_state.len--;
						
				return;
			} else {
				GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Tried to unlock a cpmponent that was held by another thread");
			}
		}
	}
	GHOST_SIMPLIFIED_MODEL_CATCH_FIRE("Tried to unlock a component that was not held");
}

static void step_lock(struct ghost_simplified_model_transition trans)
{
	switch (trans.lock_data.kind) {
	case GHOST_SIMPLIFIED_LOCK:
		__step_lock((gsm_lock_t *) trans.lock_data.address);
		break;
	case GHOST_SIMPLIFIED_UNLOCK:
		__step_unlock((gsm_lock_t *) trans.lock_data.address);
		break;
	default:
		BUG(); // unreachable;
	}
}


///////////////////////////
/// Generic Step

static void step(struct ghost_simplified_model_transition trans)
{

	GHOST_LOG_CONTEXT_ENTER();
	GHOST_LOG(trans, trans);

	current_transition = trans;
	if (__this_cpu_read(ghost_print_this_hypercall) && ghost_print_on("ghost_simplified_model_step"))
		ghost_printf_ext(GHOST_WHITE_ON_CYAN "%g(sm_trans)" GHOST_NORMAL "\n", &trans);

#ifdef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS
	if (__this_cpu_read(ghost_print_this_hypercall) && ghost_print_on("sm_diff_trans"))
		copy_sm_state_into(the_ghost_state_pre);
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS */

	switch (trans.kind) {
	case TRANS_MEM_WRITE:
		step_write(trans);
		break;
	case TRANS_MEM_ZALLOC:
		// Nothing to do
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
	case TRANS_LOCK:
		step_lock(trans);
		break;
	};

	if (__this_cpu_read(ghost_print_this_hypercall) && ghost_print_on("sm_dump_trans"))
		dump_sm_state(the_ghost_state);

#ifdef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS
	if (__this_cpu_read(ghost_print_this_hypercall) && ghost_print_on("sm_diff_trans")) {
		ghost_printf("transition simplified model state diff: ");
		ghost_diff_and_print_sm_state(the_ghost_state_pre, the_ghost_state);
		ghost_printf("\n");
	}
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_DIFF_ON_TRANS */

	GHOST_LOG_CONTEXT_EXIT();
}
#else /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */
static void step(struct ghost_simplified_model_transition trans)
{
	ghost_printf_ext(GHOST_WHITE_ON_CYAN "ID: %d; CPU: %d; %g(sm_trans)" GHOST_NORMAL "\n", transition_id, cpu_id(), &trans);
	transition_id++;
}

#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */



void ghost_simplified_model_step(struct ghost_simplified_model_transition trans)
{
	lock_sm();
#ifdef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
	step(trans);
#else /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */

	if (is_initialised) {
	    step(trans);
	}
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */
	unlock_sm();
}


//////////////////////////
// Initialisation

#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY

static void initialise_ghost_simplified_model_options(void)
{
	ghost_sm_options.promote_DSB_nsh = true;
	ghost_sm_options.promote_TLBI_nsh = true;
	ghost_sm_options.promote_TLBI_by_id = true;
}

static void initialise_ghost_ptes_memory(phys_addr_t phys, u64 size) {
	GHOST_LOG_CONTEXT_ENTER();
	the_ghost_state->base_addr = phys;
	the_ghost_state->size = size;
	the_ghost_state->memory.nr_allocated_blobs = 0;
	for (int i = 0; i < MAX_BLOBS; i++) {
		the_ghost_state->memory.blobs_backing[i].valid = false;
		the_ghost_state->memory.ordered_blob_list[i] = 0xDEADDEADDEADDEAD;
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
	/* don't step() a MSR-like transition
	 * because there is not a current TTBR0_EL2 in effect. */
	pkvm_pgd = extract_s1_root(read_sysreg(ttbr0_el2));
	try_register_root(GHOST_STAGE1, pkvm_pgd);
	GHOST_LOG_CONTEXT_EXIT();
}
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */

/*
 * perform some first-time ghost hint transitions
 */
static void initialise_ghost_hint_transitions(void)
{
	u64 pkvm_pgd;

	GHOST_LOG_CONTEXT_ENTER();
	pkvm_pgd = extract_s1_root(read_sysreg(ttbr0_el2));
	step((struct ghost_simplified_model_transition){
		.src_loc = SRC_LOC, // report as coming from _here_
		.kind = TRANS_HINT,
		.hint_data = (struct trans_hint_data){
			.hint_kind = GHOST_HINT_SET_ROOT_LOCK,
			.location = pkvm_pgd,
			.value = hyp_virt_to_phys(&pkvm_pgd_lock),
		},
	});
	step((struct ghost_simplified_model_transition){
		.src_loc = SRC_LOC, // report as coming from _here_
		.kind = TRANS_HINT,
		.hint_data = (struct trans_hint_data){
			.hint_kind = GHOST_HINT_SET_ROOT_LOCK,
			.location = (u64)hyp_virt_to_phys(host_mmu.pgt.pgd),
			.value = hyp_virt_to_phys(&host_mmu.lock),
		},
	});
	GHOST_LOG_CONTEXT_EXIT();
}

static void initialise_fixmap(void)
{
	get_fixmap();
}


void initialise_ghost_simplified_model(phys_addr_t phys, u64 size, unsigned long sm_virt, u64 sm_size)
{

#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
	lock_sm();
	GHOST_LOG_CONTEXT_ENTER();

	the_ghost_state = (struct ghost_simplified_model_state*)sm_virt;
	the_ghost_state_pre = the_ghost_state + 1;

	initialise_ghost_simplified_model_options();
	initialise_ghost_ptes_memory(phys, size);

	/* we can now start taking model steps */
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */
	initialise_ghost_hint_transitions();
#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
	sync_simplified_model_memory();


	GHOST_LOG_CONTEXT_EXIT();
	unlock_sm();

	// This needs to be outside the locked region as it is going to take the SM lock
	initialise_fixmap();
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */
}

//////////////////////////////
//// Printers

#define ID_STRING(x) [x]=#x
static const char *automaton_state_names[] = {
	ID_STRING(STATE_PTE_VALID),
	ID_STRING(STATE_PTE_INVALID_UNCLEAN),
	ID_STRING(STATE_PTE_INVALID),
	ID_STRING(STATE_PTE_NOT_WRITABLE)
};

static const char *pte_kind_names[] = {
	ID_STRING(PTE_KIND_TABLE),
	ID_STRING(PTE_KIND_MAP),
	ID_STRING(PTE_KIND_INVALID),
};

static const char *sm_tlbi_op_stage_names[] = {
	ID_STRING(TLBI_OP_STAGE1),
	ID_STRING(TLBI_OP_STAGE2),
	ID_STRING(TLBI_OP_BOTH_STAGES),
};

static const char *sm_tlbi_op_method_kind_names[] = {
	ID_STRING(TLBI_OP_BY_ALL),
	ID_STRING(TLBI_OP_BY_INPUT_ADDR),
	ID_STRING(TLBI_OP_BY_ADDR_SPACE),
};

static const char *sm_tlbi_op_regime_kind_names[] = {
	ID_STRING(TLBI_REGIME_EL10),
	ID_STRING(TLBI_REGIME_EL2),
};

static const char *tlbi_kind_names[] = {
	ID_STRING(TLBI_vmalls12e1),
	ID_STRING(TLBI_vmalls12e1is),
	ID_STRING(TLBI_vmalle1is),
	ID_STRING(TLBI_alle1is),
	ID_STRING(TLBI_vmalle1),
	ID_STRING(TLBI_vale2is),
	ID_STRING(TLBI_vae2is),
	ID_STRING(TLBI_ipas2e1is)
};

static const char *dsb_kind_names[] = {
	ID_STRING(DSB_ish),
	ID_STRING(DSB_ishst),
	ID_STRING(DSB_nsh)
};

static const char *sysreg_names[] = {
	ID_STRING(SYSREG_VTTBR),
	ID_STRING(SYSREG_TTBR_EL2),
};

static const char *hint_names[] = {
	ID_STRING(GHOST_HINT_SET_ROOT_LOCK),
	ID_STRING(GHOST_HINT_SET_OWNER_ROOT),
	ID_STRING(GHOST_HINT_RELEASE_TABLE),
	ID_STRING(GHOST_HINT_SET_PTE_THREAD_OWNER),
};

static const char *lock_type_names[] = {
	[GHOST_SIMPLIFIED_LOCK] = "LOCK",
	[GHOST_SIMPLIFIED_UNLOCK] = "UNLOCK",
};

int gp_print_write_trans(gp_stream_t *out, struct trans_write_data *write_data)
{
	char *kind;
	switch (write_data->mo) {
	case WMO_plain:
		kind = "";
		break;
	case WMO_release:
		kind = "rel";
		break;
	case GHOST_MEMSET_PAGE:
		kind="page";
		break;
	default:
		BUG(); // unreachable?
	}

	return ghost_sprintf(out, "W%s %p %lx", kind, write_data->phys_addr, write_data->val);
}

int gp_print_zalloc_trans(gp_stream_t *out, struct trans_zalloc_data *zalloc_data) {
	return ghost_sprintf(out, "ZALLOC %lx size: %lx", zalloc_data->location, zalloc_data->size);
}

int gp_print_read_trans(gp_stream_t *out, struct trans_read_data *read_data)
{
	return ghost_sprintf(out, "R %p (=%lx)", read_data->phys_addr, read_data->val);
}

int gp_print_dsb_trans(gp_stream_t *out, enum dsb_kind *dsb_data)
{
	return ghost_sprintf(out, "%s", dsb_kind_names[*dsb_data]);
}

int gp_print_sm_decoded_tlbi(gp_stream_t *out, struct sm_tlbi_op *tlbi)
{
	int ret;

	ret = ghost_sprintf(out, "(");
	if (ret) return ret;

	if (tlbi->shootdown) {
		ret = ghost_sprintf(out, "broadcast ");
		if (ret) return ret;
	}

	ret = ghost_sprintf(out, "%s", sm_tlbi_op_method_kind_names[tlbi->method.kind]);
	if (ret) return ret;

	ret = ghost_sprintf(out, " stage:%s", sm_tlbi_op_stage_names[tlbi->stage]);
	if (ret) return ret;

	ret = ghost_sprintf(out, " regime:%s", sm_tlbi_op_regime_kind_names[tlbi->regime]);
	if (ret) return ret;

	switch (tlbi->method.kind) {
	case TLBI_OP_BY_INPUT_ADDR:
		ret = ghost_sprintf(out, " ia_pfn:%p", tlbi->method.by_address_data.page);
		if (ret) return ret;

		if (tlbi->method.by_address_data.has_level_hint) {
			ret = ghost_sprintf(out, " ttl:%d", tlbi->method.by_address_data.level_hint);
			if (ret) return ret;
		}

		if (tlbi->method.by_address_data.affects_last_level_only) {
			ret = ghost_sprintf(out, " last-level-only");
			if (ret) return ret;
		}

		return ghost_sprintf(out, ")");

	case TLBI_OP_BY_ADDR_SPACE:
		return ghost_sprintf(out, " asid_or_vmid:%lu)", tlbi->method.by_id_data.asid_or_vmid);

	case TLBI_OP_BY_ALL:
		return ghost_sprintf(out, " ALL)");
	}

}

int gp_print_tlbi_trans(gp_stream_t *out, struct trans_tlbi_data *tlbi_data)
{
	const char *tlbi_kind = tlbi_kind_names[tlbi_data->tlbi_kind];
	switch (tlbi_data->tlbi_kind) {
		case TLBI_vale2is:
		case TLBI_vae2is:
		case TLBI_ipas2e1is:
			return ghost_sprintf(out, "%s pfn=%lx level=%lu", tlbi_kind, tlbi_data->page, tlbi_data->level);
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
	case GHOST_HINT_SET_OWNER_ROOT:
	case GHOST_HINT_SET_PTE_THREAD_OWNER:
		return ghost_sprintf(out, "HINT %s %lx %lx", hint_name, hint_data->location, hint_data->value);
		break;
	case GHOST_HINT_RELEASE_TABLE:
		return ghost_sprintf(out, "HINT %s %lx", hint_name, hint_data->location);
		break;
	default:
		BUG(); // unreachable?
	}
}

int gp_print_lock_trans(gp_stream_t *out, struct trans_lock_data *lock_data)
{

	return ghost_sprintf(out, "%s %lx", lock_type_names[lock_data->kind], lock_data->address);
}

int gp_print_src_loc(gp_stream_t *out, struct src_loc *src_loc)
{
	return ghost_sprintf(out, "at %s:%d in %s", src_loc->file, src_loc->lineno, src_loc->func);
}

int gp_print_sm_trans(gp_stream_t *out, struct ghost_simplified_model_transition *trans)
{
	int ret;

	switch (trans->kind) {
	case TRANS_MEM_WRITE:
		ret = gp_print_write_trans(out, &trans->write_data);
		break;
	case TRANS_MEM_ZALLOC:
		ret = gp_print_zalloc_trans(out, &trans->zalloc_data);
		break;
	case TRANS_MEM_READ:
		ret = gp_print_read_trans(out, &trans->read_data);
		break;
	case TRANS_DSB:
		ret = gp_print_dsb_trans(out, &trans->dsb_data);
		break;
	case TRANS_ISB:
		ret = ghost_sprintf(out, "ISB");
		break;
	case TRANS_TLBI:
		ret = gp_print_tlbi_trans(out, &trans->tlbi_data);
		break;
	case TRANS_MSR:
		ret = gp_print_msr_trans(out, &trans->msr_data);
		break;
	case TRANS_HINT:
		ret = gp_print_hint_trans(out, &trans->hint_data);
		break;
	case TRANS_LOCK:
		ret = gp_print_lock_trans(out, &trans->lock_data);
		break;
	default:
		BUG();
	};

	if (ret)
		return ret;

	ret = ghost_sprintf(out, " ");
	if (ret)
		return ret;

	return gp_print_src_loc(out, &trans->src_loc);
}

// A helper for the GHOST_LOG and GHOST_WARN macros
// to print out a whole simplified model transition
void GHOST_transprinter(void *data)
{
	struct ghost_simplified_model_transition *trans = (struct ghost_simplified_model_transition *)data;
	ghost_printf_ext("%g(sm_trans)", trans);
}

static const int KIND_PREFIX_LEN = 2;
static const char* KIND_PREFIX_NAMES[] = {
	[STATE_PTE_INVALID] = "I ",
	[STATE_PTE_INVALID_UNCLEAN] = "IU",
	[STATE_PTE_VALID] = "V ",
	[STATE_PTE_NOT_WRITABLE] = "NW",
};

static const int LIS_NAME_LEN = 2;
static const char* LIS_NAMES[] = {
	[LIS_unguarded] = "n ",
	[LIS_dsbed] = "d ",
	[LIS_dsb_tlbi_ipa] = "ti",
	[LIS_dsb_tlbi_ipa_dsb] = "td",
	[LIS_dsb_tlbied] = "ta",
};


// TODO: invalidator_tid will only be 1 char as MAX_CPU is 4, maybe this could be less fragile.
static const int INVALIDATOR_TID_NAME_LEN = 1;

// output needs to be long enough for at least "{prefix} {LIS} {INVALIDATOR_THREAD}"
static const int PTE_STATE_LEN = KIND_PREFIX_LEN + 1 + LIS_NAME_LEN + 1 + INVALIDATOR_TID_NAME_LEN;

// Printers for sm state
int gp_print_sm_pte_state(gp_stream_t *out, struct sm_pte_state *st)
{
	const char *prefix = KIND_PREFIX_NAMES[st->kind];

	switch (st->kind) {
	case STATE_PTE_INVALID:
		return ghost_sprintf_ext(out, "%s%I%d", prefix, PTE_STATE_LEN - KIND_PREFIX_LEN - INVALIDATOR_TID_NAME_LEN, st->invalid_clean_state.invalidator_tid);
	case STATE_PTE_INVALID_UNCLEAN:
		return ghost_sprintf_ext(out, "%s%I%s %d", prefix, PTE_STATE_LEN - KIND_PREFIX_LEN - LIS_NAME_LEN - 1 - INVALIDATOR_TID_NAME_LEN, LIS_NAMES[st->invalid_unclean_state.lis], st->invalid_unclean_state.invalidator_tid);
	case STATE_PTE_VALID:
		return ghost_sprintf_ext(out, "%s%I", prefix, PTE_STATE_LEN - KIND_PREFIX_LEN);
	case STATE_PTE_NOT_WRITABLE:
		return ghost_sprintf_ext(out, "%s%I%s %d", prefix, PTE_STATE_LEN - KIND_PREFIX_LEN - LIS_NAME_LEN - 1 - INVALIDATOR_TID_NAME_LEN, LIS_NAMES[st->invalid_unclean_state.lis], st->invalid_unclean_state.invalidator_tid);
	}
}

int gp_print_sm_loc(gp_stream_t *out, struct sm_location *loc)
{
	char *init = loc->initialised ? "*" : "!";

	if (loc->is_pte) {
		u64 start = loc->descriptor.ia_region.range_start;
		u64 end = loc->descriptor.ia_region.range_size + start;
		return ghost_sprintf_ext(out, "%s[%p]=%lx (pte_st:%g(sm_pte_state) root:%p, range:%lx-%lx)", init, loc->phys_addr, loc->val, &loc->state, loc->owner, start, end);
	} else {
		return ghost_sprintf(out, "%s[%p]=%lx", init, loc->phys_addr, loc->val);
	}

}


#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
int gp_print_sm_blob(gp_stream_t *out, struct ghost_memory_blob *b, u64 indent)
{
	int ret;

	if (sm_print_condensed() && !blob_unclean(b))
		return 0;

	if (!b->valid)
		return ghost_sprintf(out, "<invalid blob>");

	ret = ghost_sprintf_ext(out, "%I%g(sm_blob)\n", indent, b);
	if (ret)
		return ret;

	for (u64 i = 0; i < SLOTS_PER_PAGE; i++) {
		struct sm_location *loc = &b->slots[i];
		// only show those that are ptes we're tracking
		if (!loc->is_pte)
			continue;

		// don't waste energy printing 'clean' entries...
		if (!sm_print_condensed() || loc->state.kind == STATE_PTE_INVALID_UNCLEAN) {
			ret = ghost_sprintf_ext(out, " %I%g(sm_loc)\n", indent+2, loc);
		if (ret)
			return ret;
		}
	}

	return 0;
}

int gp_print_sm_blob_info(gp_stream_t *out, struct ghost_memory_blob *b)
{
	if (b->valid) {
		int tracked = 0;
		int invalid = 0;
		int invalid_unclean = 0;

		for (u64 i = 0; i < SLOTS_PER_PAGE; i++) {
			struct sm_location *loc = &b->slots[i];
			// only show those that are ptes we're tracking
			if (!loc->is_pte)
				continue;
			++tracked;
			if (loc->state.kind == STATE_PTE_INVALID)
				invalid++;
			else if (loc->state.kind == STATE_PTE_INVALID_UNCLEAN)
				invalid_unclean++;
		}

		return ghost_sprintf(out, "<blob %p->%p, %d tracked, %d invalid (clean), %d invalid (unclean)>", b->phys, b->phys + BLOB_SIZE, tracked, invalid, invalid_unclean);
	} else {
		return ghost_sprintf(out, "<invalid blob>");
	}
}



int gp_print_sm_mem(gp_stream_t *out, struct ghost_simplified_memory *mem)
{
	int ret;
	bool empty = true;

	ret = ghost_sprintf(out, "mem:\n");
	if (ret)
		return ret;

	for (int bi = 0; bi < mem->nr_allocated_blobs; bi++) {
		struct ghost_memory_blob *b = blob_of(mem, bi);

		if (!sm_print_condensed() || blob_unclean(b))
			empty = false;

		ret = gp_print_sm_blob(out, b, 0);
		if (ret)
			return ret;
	}

	if (empty) {
		ret = ghost_sprintf(out, "<clean>\n");
		if (ret)
			return ret;
	}

	return 0;
}

#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */

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

int gp_print_sm_lock(gp_stream_t *out, struct owner_locks *locks, int i)
{
	int ret;
#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
	struct lock_state *state;
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */

#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
	if (is_correctly_locked(locks->locks[i], &state)) 
		ret = ghost_sprintf(out, "(%p,%p, locked by thread %d, %s)", locks->owner_ids[i], locks->locks[i], state->id, state->write_authorization == AUTHORIZED ? "write authorized" : "write not authorized");
	else
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */
		ret = ghost_sprintf(out, "(%p,%p)", locks->owner_ids[i], locks->locks[i]);

	return ret;
}

int gp_print_sm_locks(gp_stream_t *out, struct owner_locks *locks)
{
	int ret;
	ret = ghost_sprintf(out, "%s", "locks: [");
	if (ret)
		return ret;

	if (locks->len > 0) {
	ret = gp_print_sm_lock(out, locks, 0);
		for (u64 i = 1; i < locks->len; i++) {
			ret = ghost_sprintf(out,", ");
			ret = gp_print_sm_lock(out, locks, i);
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

	ret = ghost_sprintf(out, "\n");
	if (ret)
		return ret;

	ret = gp_print_sm_roots(out, "s2", s->nr_s2_roots, s->s2_roots);
	if (ret)
		return ret;

	ret = ghost_sprintf(out, "\n");
	if (ret)
		return ret;

	ret = gp_print_sm_locks(out, &s->locks);
	if (ret)
		return ret;

	ret = ghost_sprintf(out, "\n");
	if (ret)
		return ret;


#ifndef CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY
	ret = gp_print_sm_mem(out, &s->memory);
	if (ret)
		return ret;
#endif /* CONFIG_NVHE_GHOST_SIMPLIFIED_MODEL_LOG_ONLY */

	return 0;
}

void dump_sm_state(struct ghost_simplified_model_state *st)
{
	ghost_printf_ext("%g(sm_state)\n", st);
}

/// Equality checks
bool sm_aut_invalid_eq(struct aut_invalid *i1, struct aut_invalid *i2)
{
	if (i1->invalidator_tid != i2->invalidator_tid)
		return false;

	if (i1->old_valid_desc != i2->old_valid_desc)
		return false;

	if (i1->lis != i2->lis) {
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
	case STATE_PTE_NOT_WRITABLE:
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