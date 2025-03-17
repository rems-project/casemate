EXAMPLES_DIR=../../examples
LOG_DIR=./logs

# Find all executable files in the examples directory that have NO extensions
EXECUTABLES := $(shell find $(EXAMPLES_DIR) -type f -executable ! -name "*.*")

all:
	dune build

run-all:
	mkdir -p $(LOG_DIR)
	for exe in $(EXECUTABLES); do \
		filename=$$(basename -- "$$exe"); \
		log_file="$(LOG_DIR)/$$filename.log"; \
		$$exe -a > "$$log_file"; \
		echo "Running $$log_file"; \
		dune exec casemate -- --dump-state=true --dump-roots=true --dump-trans=true "$$log_file"; \
	done

sm-test:
	dune exec casemate -- $(trace)

sm-coverage:
	dune exec casemate --instrument-with bisect_ppx --force $(trace) && bisect-ppx-report html

clean:
	dune clean
	rm -rf _coverage *.coverage $(LOG_DIR)

.PHONY: all run-all sm-test sm-coverage clean

