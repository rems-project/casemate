include config.mk

tests += simple
tests += good_write
tests += bad_no_bbm
tests += bad_bbm_missing_tlbi
tests += good_bbm

test_exes = $(patsubst %,$(BINDIR)/%,$(tests))
test_objs = $(patsubst %,$(BINDIR)/tests/%.o,$(tests))
test_expects = $(patsubst %,$(EXPECTEDDIR)/%.log,$(tests))
test_logs = $(patsubst %,$(LOGDIR)/%.log,$(tests))
test_checks = $(patsubst %,check-%,$(tests))
common_obj = $(BINDIR)/common.o
casemate_obj = $(ONLINEDIR)/casemate.o

define run_cmd
	@echo "  $1			$2" 2>&1
	@$3
endef

define run_clean
	$(call run_cmd,CLEAN,$1, \
		@rm -f $2 \
	)
endef

all: $(test_exes)
checks: $(test_checks)
expected: $(test_expects)

.PHONY: all expected checks
.PRECIOUS: $(common_obj) $(test_objs) $(test_logs)

FORCE:
.PHONY: FORCE

$(BINDIR)/%.o: $(SRCDIR)/%.c
	$(call run_cmd,CC,$<,$(CC) $(CFLAGS) -c $< -o $@)

$(BINDIR)/tests/%.o: $(SRCDIR)/tests/%.c
	$(call run_cmd,CC,$<,$(CC) $(CFLAGS) -c $< -o $@)

$(BINDIR)/%: $(BINDIR)/tests/%.o $(common_obj) $(casemate_obj)
	$(call run_cmd,LD,$@,$(CC) $^ -o $@)

$(EXPECTEDDIR)/%.log: FORCE
	$(BINDIR)/$* -at 1> $@ 2>/dev/null || true
# $(call run_cmd,RUN,$*,$(BINDIR)/$* -at 1> $@ 2>/dev/null || true)

$(LOGDIR)/%.log: FORCE
	@mkdir -p $(LOGDIR)
	$(call run_cmd,RUN,$*,$(BINDIR)/$* -at 1> $@ 2>/dev/null || true)

check-%: $(LOGDIR)/%.log FORCE
	$(call run_cmd,CHECK,$*,./scripts/check_simulation.py $< $(EXPECTEDDIR)/$*.log)

clean-%:
	$(call run_clean,$*.log,rm -f $(BINDIR)/$* $(BINDIR)/$*.o $(LOGDIR)/$*.log)

clean_objs = $(patsubst %,clean-%,$(tests))
clean: $(clean_objs)
	$(call run_clean,common,rm -f $(common_obj))

clean-expected:
	$(call run_clean,$(EXPECTEDDIR),rm -f $(EXPECTEDDIR)/*.log)