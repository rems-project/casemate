include config.mk
include ../../tools/utils.mk

EXE = casemate-check

casemate_obj = $(LIBDIR)/casemate.o
c_files = \
	src/opts.c \
	src/parser.c \
	src/driver.c \
	src/main.c \

objs = \
	$(patsubst %.c, %.o, $(c_files))

all: $(EXE) compile_commands.json

$(EXE): $(casemate_obj) $(objs)
	$(call run_cmd,LD,$@,$(CC) $^ -o $@)

src/%.o: src/%.c
	$(call run_cc,$<,$@)

compile_commands.json:
	$(call run_cmd,MK,$@, \
		$(ROOTDIR)/tools/generate_compile_commands.py $(SRCDIR))
.PHONY: compile_commands.json

clean:
	$(call run_clean,src,rm -f $(objs))
	$(call run_clean,$(EXE),rm -f $(EXE))
