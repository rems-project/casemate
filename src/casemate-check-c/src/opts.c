#include <stdlib.h>
#include <stdio.h>
#include <getopt.h>
#include <assert.h>
#include <unistd.h>

#include <casemate-impl.h>
#include <casemate-check-impl.h>

bool SHOULD_PRINT_STATE = false;
bool SHOULD_PRINT_DIFF = false;
bool SHOULD_PRINT_ONLY_UNCLEANS = true;
bool SHOULD_CHECK = true;
bool SHOULD_CHECK_LOCKS = true;
bool SHOULD_TRACK_ONLY_WATCHPOINTS = false;
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
		"  -R --racy      	do not check locks/synchronisation are respected\n"
		"  -t --trace     	print trace record for each step\n"
		"  -T --no-trace  	do not print trace record for each step\n"
		"  -c             	condensed trace format\n"
		"  -d --diff      	show diffs of state\n"
		"  -U --all        	show all (including unclean) locations in states/diffs\n"
		"  -p --print     	print state out at each step\n"
		"  -C --dry-run   	do not run checks\n"
		"  -q             	quiet, do not print state, or trace steps, or show error messages\n"
		"  -a --no-colour 	ascii-only, no ANSI escape colour codes\n"
		"  -D --debug     	debug mode\n"
		"  -W<addr>       	watch this address\n"
	);
	exit(0);
}

int hextoi(const char *s, u64 *out);

void parse_opts(int argc, char **argv)
{
	if (!isatty(STDOUT_FILENO)) {
		COLOUR = false;
	}

	static struct option long_options[] = {
		{"print",      no_argument, 0,  'p' },
		{"quiet",      no_argument, 0,  'q' },
		{"trace",      no_argument, 0,  't' },
		{"no-trace",   no_argument, 0,  'T' },
		{"diff",       no_argument, 0,  'd' },
		{"all",        no_argument, 0,  'U' },
		{"dry-run",    no_argument, 0,  'C' },
		{"racy",       no_argument, 0,  'R' },
		{"no-colour",  no_argument, 0,  'a' },
		{"debug",      no_argument, 0,  'D' },
		{"help",       no_argument, 0,  'h' },
		{0,            0,           0,  0 }
	};

	int c;
	while ((c = getopt_long(argc, argv, "acptTqdhUDRW:", long_options, 0)) != - 1) {
		switch (c) {
		case 'p':
			SHOULD_PRINT_STATE = true;
			break;

		case 'q':
			SHOULD_TRACE = false;
			SHOULD_PRINT_STATE = false;
			SHOULD_PRINT_DIFF = false;
			QUIET = true;
			break;

		case 't':
			SHOULD_TRACE = true;
			break;

		case 'T':
			SHOULD_TRACE = false;
			break;

		case 'd':
			SHOULD_PRINT_DIFF = true;
			break;

		case 'c':
			SHOULD_TRACE_CONDENSED = true;
			break;

		case 'U':
			SHOULD_PRINT_ONLY_UNCLEANS = false;
			break;


		case 'C':
			SHOULD_CHECK = false;
			break;

		case 'R':
			SHOULD_CHECK_LOCKS = false;
			break;

		case 'W': {
			u64 val;
			if (optarg[0] != '0' || optarg[1] != 'x') {
				fprintf(stderr, "-W expects hex argument in the form 0x... not '%s'\n", optarg);
				exit(1);
			}
			assert(optarg && optarg[0] == '0' && optarg[1] == 'x');
			assert(!hextoi(optarg+2, &val));
			casemate_watch_location(val);
			SHOULD_TRACK_ONLY_WATCHPOINTS = true;
			break;
		}

		case 'a':
			COLOUR = false;
			break;

		case 'D':
			DEBUG = true;
			break;

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