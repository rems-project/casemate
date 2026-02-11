.PHONY: build clean logs checks list-build-objs

build-objs += simple
build-objs += good_write
build-objs += bad_no_bbm
build-objs += bad_bbm_missing_tlbi
build-objs += good_bbm
build-objs += bad_no_assoc_lock
build-objs += bad_unlocked_write
build-objs += bad_race
build-objs += bad_reuse_page
build-objs += bad_free_page_without_clean
build-objs += good_free_page
build-objs += good_free_tree
build-objs += good_write_child
build-objs += good_switch
build-objs += bad_switch_wrong_vmid
build-objs += good_bbm_by_VMID
build-objs += bad_bbm_by_wrong_VMID
build-objs += bad_overlap_VMID
build-objs += good_bbm_stage1
build-objs += bad_no_bbm_stage1
build-objs += bad_overlap_ASID
build-objs += bad_EL2_ASID
build-objs += good_release_table

list-build-objs:
	@echo $(build-objs)

build: $(addprefix $(src)/,$(build-objs)) $(src)/compile_commands.json

CFLAGS += -I$(lib_includes)
CFLAGS += -I$(src)/

EXPECTEDDIR = expected

test_objs = $(patsubst %,$(src)/tests/%.o,$(build-objs))
test_expects = $(patsubst %,$(src)/$(EXPECTEDDIR)/%.log,$(build-objs))
test_logs = $(patsubst %,$(src)/tests/%.log,$(build-objs))
src-build-objs := $(addprefix $(src)/, $(build-objs))

common_obj = $(src)/common.o

expected: $(test_expects)

.PRECIOUS: $(common_obj) $(test_objs) $(test_logs)

$(src)/%: $(src)/tests/%.o $(common_obj) $(casemate_o)
	$(call run_cc_as_ld,$^,$@)

check-examples: FORCE
	$(call run_cmd,CHECK,examples,$(src)/scripts/run_tests.py --examples)

check-rocq: FORCE
	$(call run_cmd,CHECK,examples,$(src)/scripts/run_tests.py --rocq)

checks: check-examples check-rocq

clean:
	$(call run_clean,$(src)/common.o,$(common_obj) $(call obj-aux-files, $(common_obj)))
	$(call run_clean,$(src)/tests/,$(src-build-objs) $(call obj-aux-files, $(src-build-objs)))

clean-expected:
	$(call run_clean,$(src)/$(EXPECTEDDIR),rm -f $(src)/$(EXPECTEDDIR)/*.log)
