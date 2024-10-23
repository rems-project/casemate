all: include/casemate.h casemate.o casemate.o.S compile_commands.json

include config.mk
include ../../tools/utils.mk

LIBDIR = src

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
	include/casemate-in/casemate-state.in.h \
	include/casemate-in/casemate-transitions.in.h \
	include/casemate-in/casemate-helpers.in.h \
	include/casemate-in/casemate-ghost-types.in.h \
	include/casemate-in/casemate-config.in.h

include/casemate.h: $(HEADER_INCLUDES)
	$(call run_cmd,MK,$@, \
		./tools/generate_header.py \
	)

compile_commands.json:
	$(call run_cmd,MK,$@, \
		$(ROOTDIR)/tools/generate_compile_commands.py $(SRCDIR))
.PHONY: compile_commands.json

$(LIBDIR)/%.o: $(LIBDIR)/%.c
	$(call run_cc,$<,$@)

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
	$(call run_clean, includes, include/casemate.h)
	$(call run_clean, $(LIBDIR)/, $(objs) $(patsubst %.o,%.o.cmd,$(objs)))
.PHONY: clean