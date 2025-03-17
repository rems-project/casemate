EXAMPLES_DIR=../../examples/expected
LOG_DIR=./logs

all:
	dune build

cm-test-ex:
	for log_file in $(EXAMPLES_DIR)/*.log; do \
		echo "Processing '$$log_file'..."; \
		dune exec casemate -- "$$log_file"; \
	done

cm-test:
	dune exe parser ${trace}

cm-coverage:
	dune exe parser --instrument-with bisect_ppx --force ${trace} && bisect-ppx-report html

clean:
	dune clean
	rm -rf _coverage *.coverage

.PHONY : all sm-test sm-coverage
