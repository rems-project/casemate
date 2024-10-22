define run_cmd
	@printf "  "%-8s"\t%s\n" '$1' '$2' 2>&1
	@$3
endef

define run_clean
	$(call run_cmd,CLEAN,$1, \
		@rm -f $2 \
	)
endef

define run_cc
$(call run_cmd,CC,$1, \
		echo $(CC) $(CFLAGS) -c $1 -o $2 > $2.cmd \
		; $(CC) $(CFLAGS) -c $1 -o $2 \
	)
endef