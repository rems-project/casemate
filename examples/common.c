#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include <unistd.h>
#include <getopt.h>

#include <assert.h>

#include "common.h"
#include <casemate-impl.h>

struct casemate_model_state *st;

u64 TCR_EL2 = (0b00 << TCR_TG0_LO) | ((64 - 48) << TCR_EL2_T0SZ_LO);
u64 VTCR_EL2 = (0b00 << TCR_TG0_LO) | ((64 - 48) << TCR_EL2_T0SZ_LO);
u64 MAIR_EL2 = 0;

bool SHOULD_PRINT_STATE = false;
bool SHOULD_PRINT_DIFF = false;
bool SHOULD_PRINT_ONLY_UNCLEANS = true;
bool SHOULD_CHECK = true;
bool SHOULD_TRACE = true;
bool SHOULD_TRACE_CONDENSED = false;
bool QUIET = false;

bool COLOUR = false;

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
	if (!QUIET) {
		if (COLOUR)
			printf(GHOST_WHITE_ON_RED);
		printf("! %s", msg);
		if (COLOUR)
			printf(GHOST_NORMAL);
		printf("\n");
	}
	exit(1);
}

struct _string_buffer {
	char *buf;
	int n;
};

int ghost_cm_print(void* arg, const char *format, va_list ap)
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
		ret =vprintf(format, ap);
		if (ret < 0)
			return ret;
		return 0;
	}
}

void *ghost_cm_make_buffer(char* arg, u64 n)
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
	if (COLOUR)
		printf(GHOST_WHITE_ON_CYAN);
	printf("%s", record);
	if (COLOUR)
		printf(GHOST_NORMAL);
	printf("\n");
}

static void print_help_and_quit(void)
{
	printf(
		"Usage: \n"
		"  -t --trace    	print trace record for each step\n"
		"  -c            	condensed trace format\n"
		"  -d --diff     	show diffs of state\n"
		"  -U --cleans   	show clean locations in states/diffs\n"
		"  -p --print    	print state out at each step\n"
		"  --dry-run     	do not run checks\n"
		"  -q            	quiet, do not print state, or trace steps, or show error messages\n"
		"  --colour      	print with ANSI escape colour codes\n"
		"  -a --no-colour 	ascii-only, no ANSI escape colour codes\n"
	);
	exit(0);
}

void common_read_argv(int argc, char **argv)
{
	if (!isatty(STDOUT_FILENO)) {
		COLOUR = false;
	}

	static struct option long_options[] = {
		{"print",      no_argument, 0,  0 },
		{"quiet",      no_argument, 0,  1 },
		{"trace",      no_argument, 0,  2 },
		{"diff",       no_argument, 0,  3 },
		{"clean",      no_argument, 0,  4 },
		{"dry-run",    no_argument, 0,  5 },
		{"no-colour",  no_argument, 0,  6 },
		{"colour",     no_argument, 0,  7 },
		{"help",       no_argument, 0,  8 },
		{0,            0,           0,  0 }
	};

	int c;
	while ((c = getopt_long(argc, argv, "acptqdhU", long_options, 0)) != - 1) {
		switch (c) {
		case 0:
		case 'p':
			SHOULD_PRINT_STATE = true;
			break;

		case 1:
		case 'q':
			SHOULD_TRACE = false;
			SHOULD_PRINT_STATE = false;
			SHOULD_PRINT_DIFF = false;
			QUIET = true;
			break;

		case 2:
		case 't':
			SHOULD_TRACE = true;
			break;

		case 3:
		case 'd':
			SHOULD_PRINT_DIFF = true;
			break;

		case 'c':
			SHOULD_TRACE_CONDENSED = true;
			break;

		case '4':
		case 'U':
			SHOULD_PRINT_ONLY_UNCLEANS = false;


		case 5:
			SHOULD_CHECK = false;
			break;

		case 6:
		case 'a':
			COLOUR = false;
			break;

		case 7:
			COLOUR = true;
			break;

		case 8:
		case 'h':
			print_help_and_quit();
			break;

		default:
			assert(false);
		}
	}
}

u64 casemate_cpu_id(void)
{
	return 0;
}

void common_init(int argc, char **argv)
{
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

	common_read_argv(argc, argv);
	opts.enable_checking = SHOULD_CHECK;

	opts.check_opts.enable_printing = SHOULD_PRINT_DIFF | SHOULD_PRINT_STATE;
	opts.check_opts.print_opts = CM_PRINT_NONE;
	if (SHOULD_PRINT_ONLY_UNCLEANS)
		opts.check_opts.print_opts |= CM_PRINT_ONLY_UNCLEAN;
	if (SHOULD_PRINT_DIFF)
		opts.check_opts.print_opts |= CM_PRINT_DIFF_TO_STATE_ON_STEP;
	if (SHOULD_PRINT_STATE)
		opts.check_opts.print_opts |= CM_PRINT_WHOLE_STATE_ON_STEP;
	opts.log_opts.condensed_format = SHOULD_TRACE_CONDENSED;

	/* TODO: for now ... */
	opts.check_opts.promote_TLBI_by_id = true;

	opts.enable_tracing = SHOULD_TRACE;

	st = malloc(sm_size);
	initialise_casemate_model(&opts, 0, 0, (u64)st, sm_size);
	initialise_ghost_driver(&sm_driver);
}
