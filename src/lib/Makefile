CC = clang
LD = ld
OBJDUMP = objdump
CFLAGS = \
	-Wall \
	-I include/ \
	-fPIC -fno-PIE \
	-fno-omit-frame-pointer -fno-unwind-tables \
	-march=armv8-a+nofp -mstrict-align \
	-fno-common -nostdlib \
	-g -gdwarf-4
LDS = model.lds
LDFLAGS = \
	-r \
	-T $(LDS)

LIBDIR = src

all: include/casemate.h casemate.o compile_commands.json casemate.o.S

define run_cmd
	@echo "  $1		$2" 2>&1
	@$3
endef

define run_clean
	$(call run_cmd,CLEAN,$1, \
		@rm -f $2 \
	)
endef

objs = \
	$(LIBDIR)/model.o \
	$(LIBDIR)/setup.o \
	$(LIBDIR)/pgtable.o \
	$(LIBDIR)/trace.o \
	$(LIBDIR)/utilities/string.o \
	$(LIBDIR)/utilities/sync.o \
	$(LIBDIR)/utilities/blobs.o \
	$(LIBDIR)/utilities/state_utils.o \
	$(LIBDIR)/utilities/printer.o \
	$(LIBDIR)/utilities/diff.o \

HEADER_INCLUDES = \
	include/casemate-in/casemate.out.h \
	include/casemate-in/casemate-ghost.out.h \
	include/casemate-in/casemate-state.in.h \
	include/casemate-in/casemate-transitions.in.h \
	include/casemate-in/casemate-helpers.in.h \
	include/casemate-in/casemate-ghost-types.in.h \
	include/casemate-in/casemate-config.in.h

include/casemate.h: $(HEADER_INCLUDES)
	$(call run_cmd,MK,$@, \
		./tools/generate_header.py \
	)

compile_commands.json: $(objs) $(HEADER_INCLUDES)
	$(call run_cmd,MK,$@, \
		./tools/generate_compile_commands.py \
	)

$(LIBDIR)/%.o: $(LIBDIR)/%.c
	$(call run_cmd,CC,$<, \
		echo $(CC) $(CFLAGS) -c $< -o $@ > $@.cmd \
		; $(CC) $(CFLAGS) -c $< -o $@ \
	)

casemate.o: $(objs)
	$(call run_cmd,LD,$@, \
		$(LD) $(LDFLAGS) $^ -o $@ \
	)

casemate.o.S: casemate.o
	$(call run_cmd,OBJDUMP,$@, \
		$(OBJDUMP) -S $^ > $@ \
	)


clean:
	$(call run_clean, casemate.o, casemate.o)
	$(call run_clean, includes, include/casemate.h include/casemate-ghost.h)
	$(call run_clean, $(LIBDIR)/, $(objs) $(patsubst %.o,%.o.cmd,$(objs)))
.PHONY: clean