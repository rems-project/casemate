#include <casemate-impl.h>

///////////
// Memory

void initialise_ghost_ptes_memory(phys_addr_t phys, u64 size)
{
	GHOST_LOG_CONTEXT_ENTER();
	MODEL()->base_addr = phys;
	MODEL()->size = size;
	MODEL()->memory.nr_allocated_blobs = 0;
	for (int i = 0; i < MAX_BLOBS; i++) {
		MODEL()->memory.blobs_backing[i].valid = false;
		MODEL()->memory.ordered_blob_list[i] = 0xDEADDEADDEADDEAD;
	}
	GHOST_LOG_CONTEXT_EXIT();
}

/*
 * simple and slow, but very robust, sanity checks over the blobs.
 */

static bool check_sanity_of_ordered_blob_list(void)
{
	for (int i = 1; i < MODEL()->memory.nr_allocated_blobs; i++) {
		if (! (blob_of(&MODEL()->memory, i - 1)->phys <
		       blob_of(&MODEL()->memory, i)->phys))
			return false;
	}

	return true;
}

static bool check_sanity_of_nr_allocated_blobs(void)
{
	int c = 0;

	ghost_safety_check(MODEL()->memory.nr_allocated_blobs <= MAX_BLOBS);

	for (int i = 0; i < MAX_BLOBS; i++)
		if (MODEL()->memory.blobs_backing[i].valid)
			c++;

	if (c != MODEL()->memory.nr_allocated_blobs)
		return false;

	return true;
}

static bool check_sanity_of_allocated_blobs_in_order_list(void)
{
	for (int i = 0; i < MAX_BLOBS; i++) {
		struct casemate_memory_blob *blob = &MODEL()->memory.blobs_backing[i];

		if (blob->valid) {
			/* find it in the ordered blob list */
			for (int j = 0; j < MODEL()->memory.nr_allocated_blobs; j++) {
				if (blob_of(&MODEL()->memory, j)->phys == blob->phys)
					goto found;
			}
			return false;

found:
			continue;
		}
	}

	return true;
}

static bool check_sanity_of_ordered_list_valid(void)
{
	for (int i = 0; i < MODEL()->memory.nr_allocated_blobs; i++) {
		if (! blob_of(&MODEL()->memory, i)->valid)
			return false;
	}

	return true;
}

static bool check_sanity_of_blobs(void)
{
	/* ordered blob list well-ordered */
	ghost_safety_check(check_sanity_of_ordered_blob_list());

	/* nr_allocated_blobs matches number of valid blobs */
	ghost_safety_check(check_sanity_of_nr_allocated_blobs());

	/* all the allocated blobs appear in the ordered list */
	ghost_safety_check(check_sanity_of_allocated_blobs_in_order_list());

	/* all the blobs that appear in the ordered list are valid */
	ghost_safety_check(check_sanity_of_ordered_list_valid());

	return true;
}

static bool check_sanity_of_no_blob(u64 phys)
{
	u64 page = ALIGN_DOWN_TO_BLOB(phys);

	for (int i = 0; i < MODEL()->memory.nr_allocated_blobs; i++) {
		struct casemate_memory_blob *b = blob_of(&MODEL()->memory, i);
		if (b->valid && b->phys == page) {
			return false;
		}
	}

	return true;
}

/** BLOBINDX() - Given an order index return the index in the blob backing list
 */
#define BLOBINDX(mem, i) ((mem)->ordered_blob_list[(i)])

struct casemate_memory_blob *blob_of(struct casemate_model_memory *mem, u64 i)
{
	ghost_safety_check(i < mem->nr_allocated_blobs);
	ghost_safety_check(BLOBINDX(mem, i) < MAX_BLOBS);
	return &mem->blobs_backing[BLOBINDX(mem, i)];
}

struct casemate_memory_blob *find_blob(struct casemate_model_memory *mem, u64 phys)
{
	int l, r;
	struct casemate_memory_blob *this;
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

static void insert_blob_at_end(struct casemate_model_memory *mem, u64 b)
{
	ghost_safety_check(mem->nr_allocated_blobs < MAX_BLOBS);
	mem->ordered_blob_list[mem->nr_allocated_blobs++] = b;
}

static int bubble_blob_down(struct casemate_model_memory *mem)
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
		struct casemate_memory_blob *this = &MODEL()->memory.blobs_backing[i];
		if (! this->valid)
			return i;
	}

	GHOST_WARN("ghost model ran out of free blobs");
	ghost_assert(false);
	return 0;
}

static struct casemate_memory_blob *ensure_blob(u64 phys)
{
	u64 blob_phys = ALIGN_DOWN_TO_BLOB(phys);
	struct casemate_memory_blob *this;

	/* already one exists, done. */
	this = find_blob(&MODEL()->memory, blob_phys);
	if (this)
		return this;

	/* should be the case that there is no blob for this page */
	ghost_safety_check(check_sanity_of_no_blob(blob_phys));

	// otherwise, have to grab a new blob and insert it into the table
	insert_blob_at_end(&MODEL()->memory, get_free_blob());
	this = blob_of(&MODEL()->memory, MODEL()->memory.nr_allocated_blobs - 1);
	ghost_assert(! this->valid);

	// and initialise it.
	this->valid = true;
	this->phys = blob_phys;
	// the slots are intentionally uninitialised;
	// as of yet, they haven't been "seen" by the ghost model
	// so let the first-seen checks initialise them.
	for (int i = 0; i < SLOTS_PER_PAGE; i++) {
		struct sm_location *slot = &this->slots[i];
		slot->initialised = false;
		slot->phys_addr = blob_phys + i * sizeof(u64);
	}

	// finally, we bubble it down in the ordered list
	// to maintain the sorted order
	bubble_blob_down(&MODEL()->memory);
	ghost_safety_check(check_sanity_of_blobs());

	return this;
}

bool blob_unclean(struct casemate_memory_blob *blob)
{
	for (int i = 0; i < SLOTS_PER_PAGE; i++) {
		if (blob->slots[i].is_pte &&
		    blob->slots[i].state.kind == STATE_PTE_INVALID_UNCLEAN)
			return true;
	}

	return false;
}

/**
 * location() - Read an address from the ghost model state.
 * @phys: the physical address.
 */
struct sm_location *location(u64 phys)
{
	struct casemate_memory_blob *blob = ensure_blob(phys);
	ghost_assert(blob);
	ghost_safety_check(SLOT_OFFSET_IN_BLOB(phys) < SLOTS_PER_PAGE);
	struct sm_location *loc = &blob->slots[SLOT_OFFSET_IN_BLOB(phys)];
	touch(phys);
	return loc;
}

/**
 * read_phys() - Read a location from the ghost model memory.
 * @pre: if true, read-from the memory before the transition.
 *
 * for reading the location this transition is writing,
 * `pre` selects reading the 'old' value of the location.
 */
static u64 __read_phys(u64 addr, bool pre)
{
	struct sm_location *loc;
	u64 value;
	u64 phys_val;

	// otherwise, convert to index in memory and get the val
	loc = location(addr);

	/* TODO: BS: it seems we shouldn't have to hold the lock to read the pgtable
	 * as a concurrently accessing write */
	// Check that the location is well-locked
	// if (! is_location_locked(loc))
	// 	GHOST_MODEL_CATCH_FIRE("Tried to read a physical location without holding the lock");

	if (! loc->initialised) {
		GHOST_WARN("saw uninitialised location %p", addr);

		if (side_effect()->read_physmem == NULL)
			GHOST_MODEL_CATCH_FIRE(
				"saw uninitialised location without read_physmem side-effect instantiated\n");

		// if not yet initialised
		// assume the program was well-behaved up until now
		// and just return the current concrete value
		phys_val = side_effect()->read_physmem((u64)addr);
		return phys_val;
	}

	value = loc->val;

	// EDGE CASE: if `addr` is the address this transition is writing to
	// then the current value in the model memory will be old.
	if (is_on_write_transition(addr)) {
		if (pre) {
			// if want the old value, return it.
			return value;
		} else {
			// otherwise, secretly return the value we are about to write.
			// then continue with checks.
			value = CURRENT_TRANS().hw_step.write_data.val;
		}
	}

	// santity check:
	// if the model thinks the value is that, make sure the real location has that too
	// but we only need to check for locations we are supposedly tracking
	if (loc->is_pte && side_effect()->read_physmem &&
	    (phys_val = side_effect()->read_physmem((u64)addr)) != value) {
		GHOST_LOG_CONTEXT_ENTER();
		GHOST_LOG(value, u64);
		GHOST_LOG(phys_val, u64);
		GHOST_MODEL_CATCH_FIRE("the ghost model detected a PTE that changed under it");
		GHOST_LOG_CONTEXT_EXIT();
	}

	return value;
}

/**
 * read_phys_pre() - Read a physical address from the ghost model memory.
 *
 * This reads from the state just before the transition.
 * i.e. if this transition is a write to a location,
 * then this returns the previous value for that location.
 */
u64 read_phys_pre(u64 addr)
{
	return __read_phys(addr, true);
}

/**
 * read_phys() - Read a physical address from the ghost model memory.
 */
u64 read_phys(u64 addr)
{
	return __read_phys(addr, false);
}
