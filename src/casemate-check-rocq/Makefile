EXAMPLES_DIR=../../examples/expected
LOG_DIR=./logs

all:
	dune build

run-all:
	for log_file in $(EXAMPLES_DIR)/*.log; do \
	    echo "Processing '$$log_file'..."; \
	    dune exec casemate -- "$$log_file"; \
	done

sm-test:
	dune exec casemate -- $(trace)

sm-coverage:
	dune exec casemate --instrument-with bisect_ppx --force $(trace) && bisect-ppx-report html

clean:
	dune clean
	rm -rf _coverage *.coverage $(LOG_DIR)

.PHONY: all run-all sm-test sm-coverage clean

