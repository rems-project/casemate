include config.mk
include ../tools/utils.mk

tests += simple
tests += good_write
tests += bad_no_bbm
tests += bad_bbm_missing_tlbi
tests += good_bbm

test_exes = $(patsubst %,%,$(tests))
test_objs = $(patsubst %,tests/%.o,$(tests))
test_expects = $(patsubst %,$(EXPECTEDDIR)/%.log,$(tests))
test_logs = $(patsubst %,tests/%.log,$(tests))
test_checks = $(patsubst %,check-%,$(tests))
common_obj = common.o
casemate_obj = $(LIBDIR)/casemate.o

all: $(test_exes) compile_commands.json
checks: $(test_checks)
expected: $(test_expects)

.PHONY: all expected checks
.PRECIOUS: $(common_obj) $(test_objs) $(test_logs)

FORCE:
.PHONY: FORCE

%.o: %.c
	$(call run_cc,$<,$@)

tests/%.o: tests/%.c
	$(call run_cc,$<,$@)

%: tests/%.o $(common_obj) $(casemate_obj)
	$(call run_cmd,LD,$@,$(CC) $^ -o $@)

$(EXPECTEDDIR)/%.log: FORCE
	$(call run_cmd,RUN,$*,test -f ./$* && (./$* -at 1> $@ 2>/dev/null || true))

tests/%.log: FORCE
	$(call run_cmd,RUN,$*,test -f ./$* && (./$* -at 1> $@ 2>/dev/null || true))

check-%: tests/%.log FORCE
	$(call run_cmd,CHECK,$*,./scripts/check_simulation.py $< $(EXPECTEDDIR)/$*.log)

clean-%:
	$(call run_clean,$*,rm -f $(BINDIR)/$* $(BINDIR)/tests/$*.o $(LOGDIR)/$*.log)

clean_objs = $(patsubst %,clean-%,$(tests))
clean: $(clean_objs)
	$(call run_clean,common,rm -f $(common_obj))

clean-expected:
	$(call run_clean,$(EXPECTEDDIR),rm -f $(EXPECTEDDIR)/*.log)

compile_commands.json:
	$(call run_cmd,MK,$@, \
		$(ROOTDIR)/tools/generate_compile_commands.py $(SRCDIR))
.PHONY: compile_commands.json