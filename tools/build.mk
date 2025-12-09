# Usage: make -f tools/build.mk root=/path/to/casemate src=path/to/src/dir target=obj

include $(root)/config.mk
include $(root)/tools/run_cmd.mk

INDENT += \t
include $(src)/Makefile

FORCE:
.PHONY: FORCE

# all source files are configuration dependent
CONFIG = $(root)/config.mk

%.o: %.c $(CONFIG)
	$(call run_cc,$<,$@)

%.o.S: %.o
	$(call run_cmd,OBJDUMP,$@, \
		$(OBJDUMP) -rSD $^ > $@ \
	)

$(src)/compile_commands.json:
ifneq ($(CLANGD),)
	$(call run_cmd,MK,$@, \
		$(root)/tools/generate_compile_commands.py $(src) $(root))
endif
.PHONY: $(src)/compile_commands.json

$(src)/: $(target)

source-targets := $(wildcard $(src)/**/*.c)
-include $(source-targets:.c=.d)
