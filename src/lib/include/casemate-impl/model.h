#ifndef CASEMATE_MODEL_STATE_H
#define CASEMATE_MODEL_STATE_H

#include <casemate.h>

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
 * blob_of() - Given an index in the ordered_blob_list, return the corresponding blob
 */
struct casemate_memory_blob *blob_of(struct casemate_model_memory *mem, u64 i);

/**
 * blob_unclean() - Is any slot in the blob in an unclean state.
 */
bool blob_unclean(struct casemate_memory_blob *blob);

/**
 * location() - Retrieve the ghost-model memory for a given physical address
 */
struct sm_location *location(u64 phys);

/**
 * forget_location() - Stop tracking a location.
 */
void forget_location(struct sm_location *loc);

/**
 * stage_from_ttbr() - Get stage from name of TTBR.
 *
 * Returns false if given sysreg name is not a valid TTBR.
 */
bool stage_from_ttbr(enum ghost_sysreg_kind sysreg, entry_stage_t *out_stage);

void try_register_root(struct roots *roots, phys_addr_t baddr, addr_id_t id);

/**
 * is_on_write_transition() - Returns true when the current step is a write transition to `p`.
 */
static inline bool is_on_write_transition(u64 p)
{
	return (CURRENT_TRANS().kind == TRANS_HW_STEP &&
		CURRENT_TRANS().hw_step.kind == HW_MEM_WRITE &&
		CURRENT_TRANS().hw_step.write_data.phys_addr == p);
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
bool is_correctly_locked(gsm_lock_addr_t *lock, struct lock_state **state);

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
 * trace_step() - Generate a trace record for a given transition and give it to the driver.
 */
void trace_step(struct casemate_model_step *trans);

/**
 * ensure_traced_current_transition() - Trace current transition, if applicable, if not already done so.
 */
void ensure_traced_current_transition(bool force);

#endif /* CASEMATE_MODEL_STATE_H */
