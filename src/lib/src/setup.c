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

static void init_roots(struct roots *roots)
{
	roots->len = 0;
}

static void init_thrd_ctxt(struct cm_thrd_ctxt *ctx)
{
	ctx->current_s1.present = false;
	ctx->current_s2.present = false;

	for (u64 i = 0; i < SYSREG_MAIR_EL2 + 1; i++) {
		ctx->regs[i].present = false;
	}
}

static void init_sm_state(struct casemate_options *cfg, phys_addr_t phys, u64 size)
{
	/* copy their configuration into ours
	 * so we don't have a reference to some unstable state */
	*opts() = *cfg;

	init_sm_lock();

	STATE()->transition_id = 0;
	STATE()->watchpoints.num_watchpoints = 0;

	/* initialise the model memory */
	initialise_ghost_ptes_memory(phys, size);

	MODEL()->unclean_locations.len = 0;
	init_roots(&MODEL()->roots);

	for (int i = 0; i < MAX_CPU; i++)
		init_thrd_ctxt(&MODEL()->thread_context[i]);

	MODEL()->locks.len = 0;
	MODEL()->lock_state.len = 0;

	/* mark as initialised */
	STORE_RLX(STATE()->is_initialised, true);
}

int initialise_casemate_model(struct casemate_options *cfg, phys_addr_t phys, u64 size,
			      void *sm_virt, u64 sm_size)
{
	int ret;
	u64 expected_size;
	GHOST_LOG_CONTEXT_ENTER();

	expected_size = sizeof(struct casemate_state) + sizeof(struct casemate_model_state);
	if (cfg->check_opts.print_opts & CM_PRINT_DIFF_TO_STATE_ON_STEP)
		expected_size += sizeof(struct casemate_model_state);

	if (sm_size < expected_size) {
		ret = -12;
		goto out;
	}

	/* install as this instance's state
	 * and initialise it */
	the_ghost_state = (struct casemate_state *)sm_virt;
	init_sm_state(cfg, phys, size);

	ret = 0;
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
