#ifndef CASEMATE_MODEL_STATE_H
#define CASEMATE_MODEL_STATE_H

#include <casemate.h>

#include <casemate-impl/ll.h>
#include <casemate-impl/options.h>

#include <casemate-impl/transitions.h>
#include <casemate-impl/state.h>

#define BLOB_SIZE ((1UL) << BLOB_SHIFT)
#define BLOB_OFFSET_MASK BITMASK(BLOB_SHIFT - 1, 0)
#define ALIGN_DOWN_TO_BLOB(x) ((x) & ~BLOB_OFFSET_MASK)
#define OFFSET_IN_BLOB(x) ((x)&BLOB_OFFSET_MASK)
#define SLOT_OFFSET_IN_BLOB(x) (OFFSET_IN_BLOB(x) >> SLOT_SHIFT)

#define CURRENT_TRANS() STATE()->current_transition

/**
 * read_phys_pre() - Read a physical address from the ghost model memory.
 *
 * This reads from the state just before the transition.
 * i.e. if this transition is a write to a location,
 * then this returns the previous value for that location.
 */
u64 read_phys_pre(u64 addr);

/**
 * read_phys() - Read a physical address from the ghost model memory.
 */
u64 read_phys(u64 addr);

/**
 * initialise_ghost_ptes_memory() - Initialises the global blobs.
 * @phys: the physical address to put the global blobs at.
 * @size: the size of the blob memory.
 */
void initialise_ghost_ptes_memory(phys_addr_t phys, u64 size);

/**
 * find_blob() - Given a phys, find the blob containing it.
 *
 * Returns NULL if no blob is found.
 */
struct casemate_memory_blob *find_blob(struct casemate_model_memory *mem, u64 phys);

/**
 * free_blob() - Given a blob, free it if it contains no initialised memory
 */
void free_blob(struct casemate_memory_blob *blob);

/**
 * blob_of() - Given an index in the ordered_blob_list, return the corresponding blob
 */
struct casemate_memory_blob *blob_of(struct casemate_model_memory *mem, u64 i);

/**
 * blob_unclean() - Is any slot in the blob in an unclean state.
 */
bool blob_unclean(struct casemate_memory_blob *blob);

/**
 * page() - Retrieve the ghost-model blob for a page-aligned physical location
 */
struct casemate_memory_blob *page(u64 phys);

/**
 * is_in_uncleans() - Is physical address in the fast uncleans lookup table
 */
static inline bool is_in_uncleans(struct sm_location *loc)
{
	return ll_contains(&MODEL()->uncleans, &loc->uncleans);
}

/**
 * blob_uninitialised() - Are all slots completely uninitialised
 */
bool blob_uninitialised(struct casemate_memory_blob *blob);

/**
 * location() - Retrieve the ghost-model memory for a given physical address
 */
struct sm_location *location(u64 phys);

/**
 * stage_from_ttbr() - Get stage from name of TTBR.
 *
 * Returns false if given sysreg name is not a valid TTBR.
 */
bool stage_from_ttbr(enum ghost_sysreg_kind sysreg, entry_stage_t *out_stage);

void try_register_root(struct roots *roots, entry_stage_t stage, phys_addr_t baddr, addr_id_t id);

/**
 * regime_enabled() - Returns True if the given translation regime is currently enabled
 */
bool regime_enabled(entry_stage_t stage);

/**
 * is_on_write_transition() - Returns true when the current step is a write transition to `p`.
 */
static inline bool is_on_write_transition(u64 p)
{
	return (CURRENT_TRANS().kind == TRANS_HW_STEP &&
		CURRENT_TRANS().hw_step.kind == HW_MEM_WRITE &&
		CURRENT_TRANS().hw_step.write_data.phys_addr == p);
}

/**
 * @was_table_descriptor() - Returns true for invalid (clean) entries that used to be tables
 */
bool was_table_descriptor(struct sm_location *loc);

/**
 * is_unclean_location - Returns true if the given location is currently unclean
 */
static inline bool is_unclean_location(struct sm_location *loc)
{
	if (! loc->initialised)
		return false;

	if (! loc->is_pte)
		return false;

	return (loc->state.kind == STATE_PTE_INVALID_UNCLEAN);
}

static inline thread_identifier cpu_id(void)
{
	return CURRENT_TRANS().tid;
}

/**
 * is_location_locked() - Returns true if the lock for a given location is currently marked as owned.
 */
bool is_location_locked(struct sm_location *loc);

/**
 * is_correctly_locked() - Returns true if the given lock is owned by this physical thread.
 * @lock: the address of the lock.
 * @state: output address to write the state of the lock to.
 *
 * NOTE: when synchronisation checking is disabled always returns false and *state is undefined.
 */
bool is_correctly_locked(gsm_lock_addr_t lock, struct lock_state **state);

/// VMIDs

bool retrieve_root_for_vmid(vmid_t vmid, phys_addr_t *out_root);
bool retrieve_vmid_for_root(phys_addr_t root, vmid_t *out_vmid);
// bool vmid_already_exists(vmid_t vmid);
int associate_vmid(vmid_t vmid, sm_owner_t root);
void free_vmid(vmid_t vmid);

/// Equality and printing

bool sm_aut_invalid_eq(struct aut_invalid *i1, struct aut_invalid *i2);
bool sm_pte_state_eq(struct sm_pte_state *s1, struct sm_pte_state *s2);
bool sm_loc_eq(struct sm_location *loc1, struct sm_location *loc2);
void dump_cm_state(struct casemate_model_state *st);

/// Copying

void copy_cm_state_into(struct casemate_model_state *out);

void ghost_diff_and_print_sm_state(struct casemate_model_state *s1,
				   struct casemate_model_state *s2);

/**
 * step() - Internal step.
 */
void step(struct casemate_model_step trans);

/**
 * dump_state() - Print model state to `arg` using driver.
 */
int dump_state(void *arg, struct casemate_model_state *s);

/**
 * put_trans() - Prints a trace event directly
 */
void put_step(struct casemate_model_step *trans);

/**
 * trace_step() - Generate a trace record for a given transition and give it to the driver.
 */
void trace_step(struct casemate_model_step *trans);

/**
 * ensure_traced_current_transition() - Trace current transition, if applicable, if not already done so.
 */
void ensure_traced_current_transition(bool force);

/**
 * output_error_context() - Dump info about what Casemate knows of a location
 */
void output_error_context(const char *msg);

static inline void ERROR_REMEMBER_LOC(struct sm_location *loc)
{
	struct casemate_error_context *ctx = &STATE()->error_ctx;

	/* if already remembered, just increment */
	for (int i = 0; i < ctx->nr_locs; i++) {
		if (ctx->loc[i] == loc) {
			ctx->refcounts[i]++;
			return;
		}
	}

	/* remember it */
	if (ctx->nr_locs < MAX_REMEMBERED_LOCATIONS) {
		int i = ctx->nr_locs++;
		ctx->loc[i] = loc;
		ctx->refcounts[i] = 1;
	}
}

static inline void ERROR_FORGET_LOC(struct sm_location *loc)
{
	struct casemate_error_context *ctx = &STATE()->error_ctx;

	for (int i = 0; i < ctx->nr_locs; i++) {
		if (ctx->loc[i] == loc) {
			ctx->refcounts[i]--;

			if (ctx->refcounts[i] == 0) {
				ctx->loc[i] = ctx->loc[ctx->nr_locs - 1];
				ctx->nr_locs--;
			}

			return;
		}
	}
}

#endif /* CASEMATE_MODEL_STATE_H */
