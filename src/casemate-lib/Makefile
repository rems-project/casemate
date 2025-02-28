.PHONY: build clean headers fmt lint

BINDGEN ?= bindgen
BINDGENARGS ?= \
	--use-core --builtins \
	--disable-header-comment --no-doc-comments --no-layout-tests  \
	--merge-extern-blocks \
	--no-prepend-enum-name --disable-nested-struct-naming \
	--distrust-clang-mangling \
	--allowlist-file=$< \
	--raw-line '\#![allow(warnings)]' \

rustc-target := aarch64-unknown-none
rustc-profile := release
cargo-obj := $(obj)/$(rustc-target)/$(rustc-profile)

build-objs += $(src)/libcasemate.a

build: $(build-objs)
headers: $(src)/src/c_api.rs

$(src)/src/c_api.rs: $(src)/casemate.h $(src)/Makefile
	$(call run_cmd,BINDGEN,$@,$(BINDGEN) $(BINDGENARGS) $< -o $@)

#$(call run_cmd,CARGO,build-casemate,cd $(src) && cargo build -q)

CARGO ?= cargo

CARGOFLAGS = \
	+nightly \
	-Z unstable-options \
	-C $(src) \
	$(CARGOFLAGS_$@) \

cargo-flags-build-std := \
	-Z build-std=core,alloc \
	-Z build-std-features="optimize_for_size" \

RUSTFLAGS = \
	$(RUSTFLAGS_$@) \

rustc-flags-build-std := \
	-C panic=abort \
	-C opt-level=z \
	-C force-unwind-tables=yes \
	-C relocation-model=static \
	-C codegen-units=1 \
	-C symbol-mangling-version=v0 \
	-C target-feature=-bf16,-bti,-sve \

rustc-casemate-hosted-features := \
	 alloc \

-include $(cargo-obj)/libcasemate.d

CARGOFLAGS_$(cargo-obj)/libcasemate.a += $(cargo-flags-build-std)
RUSTFLAGS_$(cargo-obj)/libcasemate.a += $(rustc-flags-build-std)
$(cargo-obj)/libcasemate.a:
	$(call run_cmd,CARGO,$(src), \
		RUSTFLAGS="$(RUSTFLAGS)" $(CARGO) $(CARGOFLAGS) -q rustc \
			--$(rustc-profile) --target $(rustc-target) \
			--features $(rustc-casemate-hosted-features) \
			-- --crate-type=staticlib --emit link,dep-info \
	)

$(src)/libcasemate.a: $(cargo-obj)/libcasemate.a
	$(call run_cmd,OBJCOPY,$@,\
		cp $< $@ \
	)

clean:
	$(call run_cmd,CARGO,clean $(src)/,$(CARGO) $(CARGOFLAGS) -q clean)
	$(call run_clean,$(src)/libcasemate,$(src)/libcasemate.a)


fmt:
	$(call run_cmd,CARGO,$(src) fmt,$(CARGO) $(CARGOFLAGS) fmt)