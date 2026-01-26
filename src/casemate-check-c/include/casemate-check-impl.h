#ifndef CASEMATE_CHECK_IMPL_H
#define CASEMATE_CHECK_IMPL_H

#include <stdio.h>

#include <casemate.h>

extern bool SHOULD_PRINT_STATE;
extern bool SHOULD_PRINT_DIFF;
extern bool SHOULD_PRINT_ONLY_UNCLEANS;
extern bool SHOULD_CHECK;
extern bool SHOULD_CHECK_LOCKS;
extern bool SHOULD_TRACK_ONLY_WATCHPOINTS;
extern bool SHOULD_TRACE;
extern bool SHOULD_TRACE_CONDENSED;
extern bool HARDEN;
extern bool QUIET;
extern bool COLOR;
extern bool DEBUG;

extern const char *trace_file_name;

#define TRACE(FMT, ...) \
	if (DEBUG) { \
		fprintf(stderr, "[TRACE] %s:%u: " FMT "\n", __FILE__, __LINE__, ##__VA_ARGS__); \
	}

void parse_opts(int argc, char **argv);

void *initialise_casemate(void);

void *make_parser(FILE *f, struct casemate_model_step *step);
void parse_record(void *parser);
bool parser_at_EOF(void *parser);
bool parser_at_exclamation(void *parser);

#endif /* CASEMATE_CHECK_IMPL_H */
