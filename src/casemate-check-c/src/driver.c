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
u64 HCR_EL2 = (0b1 << HCR_VM_BIT);
u64 SCTLR_EL2 = (0b1 << SCTLR_M_BIT);
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
	case SYSREG_HCR_EL2:
		return HCR_EL2;
	case SYSREG_SCTLR_EL2:
		return SCTLR_EL2;

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

int ghost_cm_putc(char c)
{
	return printf("%c", c);
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
	int err;
	void *st;
	u64 sm_size;
	struct casemate_options opts = CASEMATE_DEFAULT_OPTS;
	struct ghost_driver sm_driver = {
		.putc = ghost_cm_putc,
		.read_physmem = NULL,
		.read_sysreg = NO_DEFAULT_SYSREGS ? NULL : ghost_cm_read_sysreg,
		.abort = ghost_cm_abort,
		.trace = ghost_cm_trace,
	};

	opts.enable_checking = SHOULD_CHECK;
	opts.check_opts.enable_printing = SHOULD_PRINT_DIFF | SHOULD_PRINT_STATE;
	opts.check_opts.print_opts = CM_PRINT_NONE;
	opts.check_opts.uninit_behavior = UNINIT_BEHAVIOR;
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
	opts.enable_safety_checks = HARDEN;

	sm_size = sizeof_casemate_model(&opts);
	st = malloc(sm_size);
	err = initialise_casemate_model(&opts, 0, 0, st, sm_size);
	if (err)
		assert(false);

	initialise_ghost_driver(&sm_driver);
	return st;
}
