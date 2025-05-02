#include <casemate-impl.h>

//////////////////////////
// Initialisation

struct casemate_options sm_options;
struct ghost_driver driver;

struct casemate_model_state *the_ghost_state;
struct casemate_model_state *the_ghost_state_pre;
bool is_initialised = false;

struct casemate_watchpoints sm_watchpoints;
bool touched_watchpoint = false;

/**
 * opts() - Get model options.
 */
struct casemate_options *opts(void)
{
	return &sm_options;
}

/**
 * side_effect() - Perform a side-effect using the ghost driver.
 */
struct ghost_driver *side_effect(void)
{
	return &driver;
}

void initialise_ghost_driver(struct ghost_driver *d)
{
	/* copy their driver into ours
	 * so we don't have a reference to some unstable state */
	driver = *d;
}

int initialise_casemate_model(struct casemate_options *cfg, phys_addr_t phys, u64 size,
			      void *sm_virt, u64 sm_size)
{
	int ret = 0;
	u64 expected_size;

	lock_sm();
	GHOST_LOG_CONTEXT_ENTER();

	the_ghost_state = (struct casemate_model_state *)sm_virt;
	the_ghost_state_pre = the_ghost_state + 1;
	transition_id = 0;

	expected_size = sizeof(struct casemate_model_state);
	if (cfg->check_opts.print_opts & CM_PRINT_DIFF_TO_STATE_ON_STEP)
		expected_size *= 2;

	if (sm_size < expected_size) {
		ret = -12;
		goto out;
	}

	/* copy their configuration into ours
	 * so we don't have a reference to some unstable state */
	*opts() = *cfg;
	initialise_ghost_ptes_memory(phys, size);
	the_ghost_state->roots_s1.stage = ENTRY_STAGE1;
	the_ghost_state->roots_s2.stage = ENTRY_STAGE2;

	GHOST_LOG_CONTEXT_EXIT();
	unlock_sm();

out:
	return ret;
}

int casemate_watch_location(u64 loc)
{
	int ret;
	lock_sm();

	if (sm_watchpoints.num_watchpoints >= CASEMATE_MAX_WATCHPOINTS) {
		ret = -1;
		goto out;
	}

	sm_watchpoints.watchpoints[sm_watchpoints.num_watchpoints++] = loc;
	ret = 0;

out:
	unlock_sm();
	return ret;
}