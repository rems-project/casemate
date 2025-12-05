#include <casemate-impl.h>

//////////////////////////
// Initialisation

struct ghost_driver driver;
struct casemate_state *the_ghost_state;

/**
 * opts() - Get model options.
 */
struct casemate_options *opts(void)
{
	return &STATE()->opts;
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

int attach_casemate_model(void *st)
{
	the_ghost_state = st;
	if (! the_ghost_state->is_initialised) {
		return -1;
	}

	return 0;
}

int initialise_casemate_model(struct casemate_options *cfg, phys_addr_t phys, u64 size,
			      void *sm_virt, u64 sm_size)
{
	int ret = 0;
	u64 expected_size;

	the_ghost_state = (struct casemate_state *)sm_virt;
	the_ghost_state->transition_id = 0;
	the_ghost_state->watchpoints.num_watchpoints = 0;
	init_sm_lock();

	/* now there's a lock, we can start doing other things */
	GHOST_LOG_CONTEXT_ENTER();

	/* align to an 8-byte boundary */
	STATE()->st = (struct casemate_model_state *)ALIGN_UP_TO(
		(u64)(sm_virt + sizeof(struct casemate_state)), 8);
	STATE()->st_pre = (struct casemate_model_state *)ALIGN_UP_TO((u64)(STATE()->st + 1), 8);
	STATE()->transition_id = 0;

	expected_size = sizeof(struct casemate_state) + sizeof(struct casemate_model_state);
	if (cfg->check_opts.print_opts & CM_PRINT_DIFF_TO_STATE_ON_STEP)
		expected_size += PAGE_SIZE + sizeof(struct casemate_model_state);

	if (sm_size < expected_size) {
		ret = -12;
		goto out;
	}

	/* copy their configuration into ours
	 * so we don't have a reference to some unstable state */
	*opts() = *cfg;
	initialise_ghost_ptes_memory(phys, size);

	MODEL()->roots_s1.stage = ENTRY_STAGE1;
	MODEL()->roots_s2.stage = ENTRY_STAGE2;
	STORE_RLX(STATE()->is_initialised, true);

out:
	GHOST_LOG_CONTEXT_EXIT();
	return ret;
}

int casemate_watch_location(u64 loc)
{
	int ret;
	lock_sm();

	if (STATE()->watchpoints.num_watchpoints >= CASEMATE_MAX_WATCHPOINTS) {
		ret = -1;
		goto out;
	}

	STATE()->watchpoints.watchpoints[STATE()->watchpoints.num_watchpoints++] = loc;
	ret = 0;

out:
	unlock_sm();
	return ret;
}
