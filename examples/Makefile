.PHONY: build clean logs

build-objs += simple
build-objs += good_write
build-objs += bad_no_bbm
build-objs += bad_bbm_missing_tlbi
build-objs += good_bbm
build-objs += bad_no_assoc_lock
build-objs += bad_unlocked_write

build: $(addprefix $(src)/,$(build-objs)) $(src)/compile_commands.json

CFLAGS += -I$(lib_includes)
CFLAGS += -I$(src)/

EXPECTEDDIR = expected

test_objs = $(patsubst %,$(src)/tests/%.o,$(build-objs))
test_expects = $(patsubst %,$(src)/$(EXPECTEDDIR)/%.log,$(build-objs))
test_logs = $(patsubst %,$(src)/tests/%.log,$(build-objs))

common_obj = $(src)/common.o

test_checks = $(patsubst %,check-%,$(build-objs))

checks: $(test_checks)
expected: $(test_expects)
logs: $(test_logs)

.PRECIOUS: $(common_obj) $(test_objs) $(test_logs)

$(src)/%: $(src)/tests/%.o $(common_obj) $(casemate_o)
	$(call run_cmd,LD,$@,$(CC) $^ -o $@)

$(src)/tests/%.log: FORCE
	$(call run_cmd,RUN,$(src)/$*,test -f $(src)/$* && ($(src)/$* -at 1> $@ 2>/dev/null || true))

check-%: $(src)/tests/%.log FORCE
	$(call run_cmd,CHECK,$(src)/$*,$(src)/scripts/check_simulation.py $< $(src)/$(EXPECTEDDIR)/$*.log)

clean-%:
	$(call run_clean,$(src)/$*,rm -f $(src)/$* $(src)/tests/$*.o $(src)/tests/$*.log)

clean_objs = $(patsubst %,clean-%,$(build-objs))
clean: $(clean_objs)
	$(call run_clean,$(src)/common.o,rm -f $(common_obj))

clean-expected:
	$(call run_clean,$(src)/$(EXPECTEDDIR),rm -f $(src)/$(EXPECTEDDIR)/*.log)