#include <stdlib.h>
#include <stdio.h>
#include <getopt.h>
#include <assert.h>

#include <casemate-impl.h>
#include <casemate-check-impl.h>

bool SHOULD_PRINT_STATE = false;
bool SHOULD_PRINT_DIFF = false;
bool SHOULD_PRINT_ONLY_UNCLEANS = true;
bool SHOULD_CHECK = true;
bool SHOULD_TRACE = true;
bool SHOULD_TRACE_CONDENSED = false;
bool QUIET = false;
bool COLOUR = true;

bool DEBUG = false;

const char *trace_file_name = NULL;

static void print_help_and_quit(void)
{
	printf(
		"Usage: \n"
		" ./casemate-check TRACE_FILE_NAME [OPTIONS]\n"
		"\n"
		"Options:\n"
		"  -t --trace     	print trace record for each step\n"
		"  -c             	condensed trace format\n"
		"  -d --diff      	show diffs of state\n"
		"  -U --cleans    	show clean locations in states/diffs\n"
		"  -p --print     	print state out at each step\n"
		"  --dry-run      	do not run checks\n"
		"  -q             	quiet, do not print state, or trace steps, or show error messages\n"
		"  -a --no-colour 	ascii-only, no ANSI escape colour codes\n"
		"  -D --debug     	debug mode\n"
	);
	exit(0);
}


void parse_opts(int argc, char **argv)
{
	static struct option long_options[] = {
		{"print",      no_argument, 0,  0 },
		{"quiet",      no_argument, 0,  1 },
		{"trace",      no_argument, 0,  2 },
		{"diff",       no_argument, 0,  3 },
		{"clean",      no_argument, 0,  4 },
		{"dry-run",    no_argument, 0,  5 },
		{"no-colour",  no_argument, 0,  6 },
		{"debug",      no_argument, 0,  7 },
		{"help",       no_argument, 0,  8 },
		{0,            0,           0,  0 }
	};

	int c;
	while ((c = getopt_long(argc, argv, "acptqdhUD", long_options, 0)) != - 1) {
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
			break;


		case 5:
			SHOULD_CHECK = false;
			break;

		case 6:
		case 'a':
			COLOUR = false;
			break;

		case 7:
		case 'D':
			DEBUG = true;
			break;

		case 8:
		case 'h':
			print_help_and_quit();
			break;

		default:
			assert(false);
		}
	}

	for (; optind < argc; optind++){
		optarg = argv[optind];

		if (trace_file_name) {
			fprintf(stderr, "! must pass only a single trace file to parse\n");
			exit(1);
		}

		trace_file_name = optarg;
	}

	if (!trace_file_name) {
		fprintf(stderr, "! must pass a log file\n");
		exit(1);
	}
}