#ifndef CASEMATE_OPTIONS_H
#define CASEMATE_OPTIONS_H

#include <casemate.h>

#define CASEMATE_MAX_WATCHPOINTS 16
struct casemate_watchpoints {
	u64 num_watchpoints;
	u64 watchpoints[CASEMATE_MAX_WATCHPOINTS];
};

/**
 * opts() - Get model options.
 */
struct casemate_options *opts(void);

/**
 * side_effect() - Perform a side-effect using the ghost driver.
 */
struct ghost_driver *side_effect(void);

/**
 * touch() - Note that the model touched a location, for watchpoint tracking.
 */
void touch(u64 location);

/*
 * TODO: BS: make these functions with callbacks into the driver
 * so the ghost driver can do more fine-grained choice of tracing/printing/diffing.
 */

static inline bool should_trace(void)
{
	return (opts()->enable_tracing);
}

static inline bool should_print_state(void)
{
	return (opts()->check_opts.enable_printing &&
		((opts()->check_opts.print_opts & CM_PRINT_WHOLE_STATE_ON_STEP) != 0));
}

static inline bool should_print_unclean_only(void)
{
	return (opts()->check_opts.enable_printing &&
		((opts()->check_opts.print_opts & CM_PRINT_ONLY_UNCLEAN) != 0));
}

static inline bool should_print_diffs(void)
{
	return (opts()->check_opts.enable_printing &&
		((opts()->check_opts.print_opts & CM_PRINT_DIFF_TO_STATE_ON_STEP) != 0));
}

static inline bool should_track_only_watchpoints(void)
{
	return (opts()->track_watchpoints);
}

static inline bool should_trace_condensed(void)
{
	return (opts()->enable_tracing && opts()->log_opts.condensed_format);
}

#endif /* CASEMATE_OPTIONS_H */
