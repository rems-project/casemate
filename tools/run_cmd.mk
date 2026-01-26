Q ?= @

INDENT = \t

define run_cmd
	@printf "  "%-8s"$(INDENT)%s\n" '$1' '$2' 2>&1
	$(Q)$3
endef

define run_clean
	$(call run_cmd,CLEAN,$1, \
		rm -f $2 \
	)
endef

define obj-aux-files
	$(patsubst %.o, %.o.cmd, $1) $(patsubst %.o, %.d, $1) $(patsubst %.o, %.o.S, $1)
endef

define run_cc
$(call run_cmd,CC,$1, \
		echo $(CC) $(CFLAGS) $(CFLAGS-$2) -c $1 -o $2 > $2.cmd \
		&& $(CC) $(CFLAGS) $(CFLAGS-$2) -c $1 -o $2 \
		&& $(OBJDUMP) -rS $2 > $2.S \
	)
endef

define run_cc_as_ld
$(call run_cmd,LD,$2, \
		$(CC) $(CFLAGS) $(CFLAGS-$2) $(foreach lib,$(LIBS),-Wl,-l$(lib)) $1 -o $2 \
	)
endef

define run_ld
$(call run_cmd,LD,$2, \
		$(LD) $(LDFLAGS) $(LDFLAGS-$2) $1 -o $2 \
	)
endef

define run_objcopy
$(call run_cmd,OBJCOPY,$2, \
		$(OBJCOPY) $(OBJCOPYFLAGS) $1 -o $2 \
	)
endef

define run_cp
$(call run_cmd,COPY,$2, \
		cp $1 $2 \
	)
endef

binary-targets := CC LD OBJDUMP OBJCOPY CLANG-FORMAT
other-configs := ARCH CFLAGS LDFLAGS CLANGD

dump-config:
	@$(foreach t,$(binary-targets),echo $(t)=$($(t));)
	@echo
	@$(foreach t,$(other-configs),echo $(t)=$($(t));)
	@echo
	@$(foreach t,$(binary-targets),echo $(t)-VERSION-TEXT='$(shell $($(t)) --version)';)
