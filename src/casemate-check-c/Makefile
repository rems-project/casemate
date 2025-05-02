.PHONY: build clean fmt lint

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
	$(call run_clean,$(src)/src,$(build-objs) $(call obj-aux-files, $(build-objs)))
	$(call run_clean,$(check-obj),$(check-obj) $(call obj-aux-files, $(check-obj)))

fmt:
	$(call run_cmd,FMT,clang-format,\
		$(CLANG-FORMAT) -i $$(find $(src) -iname '*.[ch]') \
	)

lint:
	$(call run_cmd,LINT,clang-format,\
		$(CLANG-FORMAT) --dry-run -Werror $$(find $(src) -iname '*.[ch]') \
	)
