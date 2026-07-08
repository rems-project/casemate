EXAMPLES_DIR=../../examples/expected
LOG_DIR=./logs
CASEMATE_EXE=_build/default/src/casemate.exe

all:
	dune build

cm-test-ex:
	dune build ./src/casemate.exe
	for log_file in $(EXAMPLES_DIR)/*.log; do \
		echo "Processing '$$log_file'..."; \
		$(CASEMATE_EXE) "$$log_file"; \
	done

cm-test:
	dune exec ./src/casemate.exe -- ${trace}

cm-coverage:
	dune exec --instrument-with bisect_ppx --force ./src/casemate.exe -- ${trace} && bisect-ppx-report html

clean:
	dune clean
	rm -rf _coverage *.coverage

.PHONY : all sm-test sm-coverage
