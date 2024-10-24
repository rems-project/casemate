.PHONY: build clean

build-objs += src/opts.o
build-objs += src/parser.o
build-objs += src/driver.o
build-objs += src/main.o

build-objs := $(addprefix $(src)/,$(build-objs))
check-obj := $(src)/casemate-check

build: $(check-obj) $(build-objs) $(src)/compile_commands.json $(root)/casemate-check

CFLAGS += -I$(src)/include
CFLAGS += -I$(lib_includes)

$(check-obj): $(casemate_o) $(build-objs)
	$(call run_cc_as_ld,$^,$@)

$(root)/casemate-check: $(check-obj)
	$(call run_cp,$(root)/src/casemate-check-c/casemate-check,$(root)/casemate-check)

clean:
	$(call run_clean,$(src)/src,rm -f $(build-objs))
	$(call run_clean,$(check-obj),rm -f $(check-obj))
