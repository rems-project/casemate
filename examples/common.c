#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include <unistd.h>
#include <getopt.h>

#include <assert.h>
#include <threads.h>

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
bool SHOULD_CHECK_LOCKS = true;
bool SHOULD_TRACE = true;
bool SHOULD_TRACE_CONDENSED = false;
bool QUIET = false;

bool COLOR = false;

u64 ghost_cm_read_sysreg(enum ghost_sysreg_kind sysreg)
{
	assert(false);
}

void ghost_cm_abort(const char *msg)
{
	if (!QUIET) {
		if (COLOR)
			printf(GHOST_WHITE_ON_RED);
		printf("! %s", msg);
		if (COLOR)
			printf(GHOST_NORMAL);
		printf("\n");
	}
	exit(1);
}

int ghost_cm_putc(char c)
{
	printf("%c", c);
	return 0;
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

static void print_help_and_quit(void)
{
	printf(
		"Usage: \n"
		"  -R --racy      	do not check locks/synchronisation are respected\n"
		"  -t --trace    	print trace record for each step\n"
		"  -c            	condensed trace format\n"
		"  -d --diff     	show diffs of state\n"
		"  -U --cleans   	show clean locations in states/diffs\n"
		"  -p --print    	print state out at each step\n"
		"  --dry-run     	do not run checks\n"
		"  -q            	quiet, do not print state, or trace steps, or show error messages\n"
		"  --color      	print with ANSI escape color codes\n"
		"  -a --no-color 	ascii-only, no ANSI escape color codes\n"
	);
	exit(0);
}

void common_read_argv(int argc, char **argv)
{
	if (!isatty(STDOUT_FILENO)) {
		COLOR = false;
	}

	static struct option long_options[] = {
		{"print",      no_argument, 0,  0 },
		{"quiet",      no_argument, 0,  1 },
		{"trace",      no_argument, 0,  2 },
		{"diff",       no_argument, 0,  3 },
		{"clean",      no_argument, 0,  4 },
		{"dry-run",    no_argument, 0,  5 },
		{"no-color",   no_argument, 0,  6 },
		{"color",      no_argument, 0,  7 },
		{"help",       no_argument, 0,  8 },
		{"racy",       no_argument, 0,  'R' },
		{0,            0,           0,  0 }
	};

	int c;
	while ((c = getopt_long(argc, argv, "acptqdhUR", long_options, 0)) != - 1) {
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

		case 'R':
			SHOULD_CHECK_LOCKS = false;
			break;

		case 6:
		case 'a':
			COLOR = false;
			break;

		case 7:
			COLOR = true;
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


int no_spawned_threads;
thrd_t threads[4];

struct channel {
	int full;
	int content;
};

struct channel channel[4];
mtx_t m;

void spawn_thread(thrd_start_t fn)
{
	int err;

	assert(no_spawned_threads < 4);
	err = thrd_create(&threads[no_spawned_threads++], fn, NULL);
	assert(err == thrd_success);
}

void join(void)
{
	for (int i = 0; i < no_spawned_threads; i++) {
		int err = thrd_join(threads[i], NULL);
		assert(err == thrd_success);
	}
}

void send(tid_t to, int v) {
	while (1) {
		mtx_lock(&m);
		if (channel[to].full) {
			mtx_unlock(&m);
			continue;
		}

		channel[to].content = v;
		channel[to].full = 1;
		mtx_unlock(&m);
		return;
	}
}

int recv(void) {
	int v;
	tid_t tid = casemate_cpu_id();
	while (1) {
		mtx_lock(&m);
		if (!channel[tid].full) {
			mtx_unlock(&m);
			continue;
		}

		v = channel[tid].content;
		channel[tid].full = 0;
		mtx_unlock(&m);
		return v;
	}
}

u64 casemate_cpu_id(void)
{
	thrd_t cur = thrd_current();
	for (int i = 0; i < no_spawned_threads; i++) {
		if (thrd_equal(cur, threads[i]))
			return (u64)(i+1);
	}
	return 0;
}

void common_init(int argc, char **argv)
{
	int err;
	struct casemate_options opts = CASEMATE_DEFAULT_OPTS;
	u64 sm_size = sizeof(struct casemate_state) + 2*sizeof(struct casemate_model_state);
	struct ghost_driver sm_driver = {
		.putc = ghost_cm_putc,
		.read_physmem = NULL,
		.read_sysreg = ghost_cm_read_sysreg,
		.abort = ghost_cm_abort,
		.trace = ghost_cm_trace,
	};

	common_read_argv(argc, argv);
	opts.enable_checking = SHOULD_CHECK;

	opts.check_opts.enable_printing = SHOULD_PRINT_DIFF | SHOULD_PRINT_STATE;
	opts.check_opts.check_synchronisation = SHOULD_CHECK_LOCKS;
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
	err = initialise_casemate_model(&opts, 0, 0, st, sm_size);
	if (err) {
		fprintf(stderr, "common: failed to initialise casemate state\n");
		exit(1);
	}
	initialise_ghost_driver(&sm_driver);

	casemate_model_step_msr(SYSREG_VTCR_EL2, VTCR_EL2);
	casemate_model_step_msr(SYSREG_TCR_EL2, TCR_EL2);
	casemate_model_step_msr(SYSREG_MAIR_EL2, MAIR_EL2);

	mtx_init(&m, mtx_plain);
}
