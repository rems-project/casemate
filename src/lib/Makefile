
.PHONY: build clean headers

build-objs += casemate.h
build-objs += casemate.o
build-objs += casemate.o.S

build: $(addprefix $(src)/,$(build-objs)) $(src)/compile_commands.json

CFLAGS += -I$(src)/include/
CFLAGS += -fPIC -fno-PIE
CFLAGS += -fno-omit-frame-pointer -fno-unwind-tables
ifeq ($(ARCH),AARCH4)
  CFLAGS += -march=armv8-a+nofp -mstrict-align
endif
CFLAGS += -fno-common -nostdlib

LDFLAGS += -r
LDFLAGS += -T $(src)/model.lds

casemate-obj += src/model.o
casemate-obj += src/setup.o
casemate-obj += src/pgtable.o
casemate-obj += src/trace.o
casemate-obj += src/utilities/string.o
casemate-obj += src/utilities/sync.o
casemate-obj += src/utilities/blobs.o
casemate-obj += src/utilities/state_utils.o
casemate-obj += src/utilities/printer.o
casemate-obj += src/utilities/diff.o

headers-deps += include/casemate-in/casemate-config.in.h
headers-deps += include/casemate-in/casemate-helpers.in.h
headers-deps += include/casemate-in/casemate-state.in.h
headers-deps += include/casemate-in/casemate-ghost-types.in.h
headers-deps += include/casemate-in/casemate-transitions.in.h
headers-deps += include/casemate-in/casemate.out.h
headers-objs += casemate.h
headers: $(addprefix $(src)/,$(headers-objs))

headers-deps := $(addprefix $(src)/,$(headers-deps))
$(src)/include/casemate.h: $(headers-deps)
	$(call run_cmd,MK,$@, \
		$(src)/tools/generate_header.py \
	)

$(src)/casemate.o: $(addprefix $(src)/,$(casemate-obj))
	$(call run_ld,$^,$@)

$(src)/casemate.h: $(src)/include/casemate.h
	$(call run_cp,$^,$@)

clean:
	$(call run_clean,$(src)/includes, $(src)/include/casemate.h)
	$(call run_clean,$(src)/src/, $(addprefix $(src)/,$(casemate-obj) $(patsubst %.o,%.o.cmd,$(casemate-obj))))
	$(call run_clean,$(src)/casemate.o, $(src)/casemate.o)
