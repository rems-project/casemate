#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <getopt.h>
#include <assert.h>

#include <casemate-impl.h>
#include <casemate-check-impl.h>

int main(int argc, char **argv)
{
	int ret;
	parse_opts(argc, argv);
	void *st = initialise_casemate();

	FILE *f = fopen(trace_file_name, "r");
	struct casemate_model_step step;

	void *parser = make_parser(f, &step);
	while (!parser_at_EOF(parser) && !parser_at_exclamation(parser)) {
		parse_record(parser);
		casemate_model_step(step);
	}

	if (parser_at_exclamation(parser)) {
		/* logfile claimed there was an error here ... */
		fprintf(stderr, "! casemate-check: mismatch between success status, logfile had violation but none detected.\n");
		ret = 1;
	} else {
		/* at EOF:
		 * no more transitions, steps had no errors, all good! !*/
		 fprintf(stderr, "casemate-check: log checked successfully.\n");
		 ret = 0;
	}


	free(parser);
	free(st);

	return ret;
}
