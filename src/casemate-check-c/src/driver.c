#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <getopt.h>
#include <assert.h>

#include <casemate-impl.h>
#include <casemate-check-impl.h>

u64 TCR_EL2 = (0b00 << TCR_TG0_LO) | ((64 - 48) << TCR_EL2_T0SZ_LO);
u64 VTCR_EL2 = (0b00 << TCR_TG0_LO) | ((64 - 48) << TCR_EL2_T0SZ_LO);
u64 MAIR_EL2 = 0;

u64 ghost_cm_read_sysreg(enum ghost_sysreg_kind sysreg)
{
	switch (sysreg) {
	case SYSREG_VTCR_EL2:
		return VTCR_EL2;
	case SYSREG_TCR_EL2:
		return TCR_EL2;
	case SYSREG_MAIR_EL2:
		return MAIR_EL2;

	case SYSREG_VTTBR:
	case SYSREG_TTBR_EL2:
		assert(false);

	default:
		assert(false);
	}
}

void ghost_cm_abort(const char *msg)
{
	if (! QUIET) {
		if (COLOR)
			printf(GHOST_WHITE_ON_RED);
		printf("! %s", msg);
		if (COLOR)
			printf(GHOST_NORMAL);
		printf("\n");
	}
	exit(1);
}

struct _string_buffer {
	char *buf;
	int n;
};

int ghost_cm_print(void *arg, const char *format, va_list ap)
{
	int ret;
	if (arg != NULL) {
		struct _string_buffer *buf = arg;
		ret = vsnprintf(buf->buf, buf->n, format, ap);
		if (ret < 0)
			return ret;
		buf->buf += ret;
		buf->n -= ret;
		return 0;
	} else {
		ret = vprintf(format, ap);
		if (ret < 0)
			return ret;
		return 0;
	}
}

void *ghost_cm_make_buffer(char *arg, u64 n)
{
	struct _string_buffer *buf = malloc(sizeof(struct _string_buffer));
	buf->buf = arg;
	buf->n = n;
	return buf;
}

void ghost_cm_free_buffer(void *buf)
{
	free(buf);
}

void ghost_cm_trace(const char *record)
{
	if (COLOR)
		printf(GHOST_WHITE_ON_CYAN);
	printf("%s", record);
	if (COLOR)
		printf(GHOST_NORMAL);
	printf("\n");
}

u64 casemate_cpu_id(void)
{
	return 0;
}

void *initialise_casemate(void)
{
	void *st;
	struct casemate_options opts = CASEMATE_DEFAULT_OPTS;
	u64 sm_size = 2 * sizeof(struct casemate_model_state);
	struct ghost_driver sm_driver = {
		.read_physmem = NULL,
		.read_sysreg = ghost_cm_read_sysreg,
		.abort = ghost_cm_abort,
		.print = ghost_cm_print,
		.sprint_create_buffer = ghost_cm_make_buffer,
		.sprint_destroy_buffer = ghost_cm_free_buffer,
		.trace = ghost_cm_trace,
	};

	opts.enable_checking = SHOULD_CHECK;
	opts.check_opts.enable_printing = SHOULD_PRINT_DIFF | SHOULD_PRINT_STATE;
	opts.check_opts.print_opts = CM_PRINT_NONE;
	opts.track_watchpoints = SHOULD_TRACK_ONLY_WATCHPOINTS;
	if (SHOULD_PRINT_ONLY_UNCLEANS)
		opts.check_opts.print_opts |= CM_PRINT_ONLY_UNCLEAN;
	if (SHOULD_PRINT_DIFF)
		opts.check_opts.print_opts |= CM_PRINT_DIFF_TO_STATE_ON_STEP;
	if (SHOULD_PRINT_STATE)
		opts.check_opts.print_opts |= CM_PRINT_WHOLE_STATE_ON_STEP;
	opts.log_opts.condensed_format = SHOULD_TRACE_CONDENSED;

	/* TODO: for now ... */
	opts.check_opts.promote_TLBI_by_id = true;
	opts.check_opts.check_synchronisation = SHOULD_CHECK_LOCKS;

	opts.enable_tracing = SHOULD_TRACE;

	st = malloc(sm_size);
	initialise_casemate_model(&opts, 0, 0, (u64)st, sm_size);
	initialise_ghost_driver(&sm_driver);
	return st;
}
