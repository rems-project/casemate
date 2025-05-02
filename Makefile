.PHONY: build clean
.PHONY: checks example-traces check-examples check-rocq
.PHONY: casemate casemate-check casemate-lib
.PHONY: fmt lint
.PHONY: dump-config
.PHONY: help

all: casemate examples

help:
	@echo 'usage: make [casemate | casemate-check | casemate-lib | examples | clean | checks]'

config.mk: ./configure
	@echo 'Make: configuration out-of-date, please re-run ./configure'

# include auto-generated files
include config.mk
include tools/run_cmd.mk

subdirs += src/lib
subdirs += examples
subdirs += src/casemate-check-c

build: $(subdirs)

.PHONY: $(subdirs)

define build_subdir
  $(call run_cmd,$1,$2,\
  	$(MAKE) --no-print-directory -f $(root)/tools/build.mk Q=$(Q) root=$(root) src=$2 target=$3 $2/ \
  )
endef

define clean_subdir
  $(call build_subdir,CLEAN,$1,clean)
endef

define fmt_subdir
  $(call build_subdir,FMT,$1,fmt)
endef

define lint_subdir
  $(call build_subdir,LINT,$1,lint)
endef

# building

$(subdirs): config.mk
	$(call build_subdir,BUILD,$@,build)

casemate: casemate-lib casemate-check
casemate-check: src/casemate-check-c
casemate-lib: src/lib lib-headers

lib-headers:
	$(call build_subdir,GENHEADER,src/lib,headers)

clean:
	$(call clean_subdir,src/lib)
	$(call clean_subdir,examples)
	$(call clean_subdir,src/casemate-check-c)

example-traces:
	$(call build_subdir,RUN,examples,logs)

check-rocq:
	$(call build_subdir,RUN,examples,check-rocq)

check-examples:
	$(call build_subdir,RUN,examples,check-examples)

checks: check-examples check-rocq

lint:
	$(call lint_subdir,src/lib)

fmt:
	$(call fmt_subdir,src/lib)
