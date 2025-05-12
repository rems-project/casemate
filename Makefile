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


# checkers

example-traces:
	$(call build_subdir,RUN,examples,logs)

check-rocq:
	$(call build_subdir,RUN,examples,check-rocq)

check-examples:
	$(call build_subdir,RUN,examples,check-examples)

checks: check-examples check-rocq

# clang-format

lint:
	$(call lint_subdir,src/lib)
	$(call lint_subdir,src/casemate-check-c)

fmt:
	$(call fmt_subdir,src/lib)
	$(call fmt_subdir,src/casemate-check-c)


# CI/CD versioning control

bump-version:
	@echo "VERSION:$(file <VERSION) NEW_VERSION:$(NEW_VERSION)"
ifneq ($(shell git status -s),)
	@echo error: cannot bump version with untracked changes
	@exit 1
endif
	echo "$(NEW_VERSION)" > VERSION
	git add VERSION
	git commit -m "bump: version: $(NEW_VERSION)"
	git fetch --tags
	git tag v$(NEW_VERSION)
	git push origin main
	git push origin v$(NEW_VERSION)
.PHONY: bump-version
