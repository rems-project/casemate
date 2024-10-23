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
	parse_opts(argc, argv);
	void *st = initialise_casemate();

	FILE *f = fopen(trace_file_name, "r");
	struct casemate_model_step step;

	void *parser = make_parser(f, &step);
	while (1) {
		parse_record(parser);
		casemate_model_step(step);
	}
	free(parser);

	return 0;
}
