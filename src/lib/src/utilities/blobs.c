#include <casemate-impl.h>

///////////
// Memory

void initialise_ghost_ptes_memory(phys_addr_t phys, u64 size) {
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
		struct casemate_memory_blob *b = &the_ghost_state->memory.blobs_backing[i];
		if (b->valid && b->phys == page) {
			return false;
		}
	}

	return true;
}

#define BLOBINDX(mem, i) ((mem)->ordered_blob_list[(i)])

struct casemate_memory_blob *blob_of(struct casemate_model_memory *mem, u64 i)
{
	return &mem->blobs_backing[BLOBINDX(mem, i)];
}

/*
 * given a physical address, get the index in the ordered list its blob is at.
 */
int __find_blob_index(struct casemate_model_memory *mem, u64 phys)
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
			return m;
		} else if (page < this->phys) {
			r = m - 1;
		}
	}

	return -1;
}

struct casemate_memory_blob *find_blob(struct casemate_model_memory *mem, u64 phys)
{
	int i = __find_blob_index(mem, phys);

	if (i < 0)
		return NULL;

	return blob_of(mem, i);
}

static void insert_blob_at_end(struct casemate_model_memory *mem, u64 b)
{
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
		struct casemate_memory_blob *this = &the_ghost_state->memory.blobs_backing[i];
		if (!this->valid)
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
	// as of yet, they haven't been "seen" by the ghost model
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

bool blob_unclean(struct casemate_memory_blob *blob)
{
	for (int i = 0; i < SLOTS_PER_PAGE; i++) {
		if (blob->slots[i].is_pte && blob->slots[i].state.kind == STATE_PTE_INVALID_UNCLEAN)
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
	struct sm_location *loc = &blob->slots[SLOT_OFFSET_IN_BLOB(phys)];
	touch(phys);
	return loc;
}

void __try_free_blob(struct casemate_memory_blob *blob)
{
	int i;
	struct casemate_model_memory *mem = &the_ghost_state->memory;

	for (int i = 0; i < SLOTS_PER_PAGE; i++) {
		struct sm_location *slot = &blob->slots[i];
		if (slot->initialised)
			return;
	}

	/* the whole page is now free */
	blob->valid = false;

	/* ... and removed from the quick-search list */
	i = __find_blob_index(mem, blob->phys);
	ghost_assert(i > 0);

	for (; i < mem->nr_allocated_blobs - 1; i++) {
		BLOBINDX(mem, i) = BLOBINDX(mem, i+1);
	}
	mem->nr_allocated_blobs--;
}

/**
 * forget_location() - Stop tracking a location.
 */
void forget_location(struct sm_location *loc)
{
	if (loc->is_pte)
		GHOST_MODEL_CATCH_FIRE("cannot forget a PTE");

	/* unmark it! */
	loc->is_pte = false;
	loc->initialised = false;

	__try_free_blob(BLOB_CONTAINER_OF(loc));
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
		if (side_effect()->read_physmem == NULL)
			GHOST_MODEL_CATCH_FIRE("saw uninitialised location %p, without read_physmem side-effect instantiated\n");

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
			value = current_transition.hw_step.write_data.val;
		}
	}

	// santity check:
	// if the model thinks the value is that, make sure the real location has that too
	// but we only need to check for locations we are supposedly tracking
	if (loc->is_pte && side_effect()->read_physmem && (phys_val = side_effect()->read_physmem((u64)addr)) != value) {
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
