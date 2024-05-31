all: world
world: verify

# Many thanks to Jonathan Protzenko for its Low* tutorial

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe
KRML_EXE = $(KRML_HOME)/krml

include Makefile.include

FSTAR_OPTIONS = $(SIL) --cache_checked_modules $(FSTAR_EMACS_PARAMS) \
    --already_cached 'FStar Steel C Prims' \
    --compat_pre_typed_indexed_effects \
		--cmi --odir obj --cache_dir obj \
		$(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

obj:
	mkdir $@

ALL_SOURCE_FILES = $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS))) \

ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) --dep full $(ALL_SOURCE_FILES) > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend

depend: .depend

$(ALL_CHECKED_FILES): %.checked:
	@echo "[CHECK      $(basename $(notdir $@))]"
	$(Q)$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	@echo $*

clean:
	-rm -rf .depend obj dist bench/*.{cmx,cmi,o,out}

.PRECIOUS: %.krml
obj/%.krml:
	@echo "[EXTRACT    $(basename $(notdir $@))]"
	$(Q)$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

# steel_types.h defines symbols required by Steel.SpinLock
# steel_base.h defines symbols required by Steel.ArrayArith
extract: $(ALL_KRML_FILES)
	mkdir -p dist
	$(KRML_EXE) -skip-compilation -fparentheses -tmpdir dist \
    -library Steel.ArrayArith -static-header Steel.ArrayArith -no-prefix Steel.ArrayArith \
	  -bundle Steel.SpinLock= -bundle 'FStar.\*,Steel.\*' \
	  -bundle 'StarMalloc=Map.\*,Impl.\*,Spec.\*,Main,Main.Meta,LargeAlloc'[rename=StarMalloc] \
	  -bundle 'SlabsCommon,SlabsFree,SlabsAlloc'[rename=Slabs] \
	  -bundle 'SlotsFree,SlotsAlloc'[rename=Slots] \
	  -bundle 'ArrayList,ArrayListGen'[rename=ArrayList] \
	  -no-prefix Main \
	  -no-prefix LargeAlloc \
	  -no-prefix Mman \
	  -no-prefix MemoryTrap \
	  -warn-error +9 \
	  -add-include 'Steel_SpinLock:"steel_types.h"' \
	  -add-include 'Steel_SpinLock:"steel_base.h"' \
	  $^

FILES = \
$(STEEL_HOME)/src/c/steel_spinlock.c \
dist/ArrayList.c \
dist/krmlinit.c \
dist/StarMalloc.c \
dist/Slabs.c \
dist/Slots.c \
dist/Bitmap5.c \
dist/Utils2.c \
dist/SizeClass.c \
c/utils.c \
c/fatal_error.c \
c/memory.c \
c/lib-alloc.c

lib: verify extract
	mkdir -p out
	$(CC) -O3 -g \
	  -DKRML_VERIFIED_UINT128 \
	  -I $(KRML_HOME)/include \
	  -I $(KRML_LIB)/dist/minimal -I dist \
	  -I $(STEEL_HOME)/include/steel \
	  -pthread -lpthread \
	  -Wall -Wextra \
          -std=gnu11 \
	  -shared -fPIC \
	  $(FILES) \
	  -o out/starmalloc.so

#-Wmissing-prototypes
#-std=c17
#-Wall -Wextra -Wcast-align=strict -Wcast-qual
#-fvisibility=hidden
hardened_lib: verify extract
	mkdir -p out
	$(CC) -DKRML_VERIFIED_UINT128 \
	  -pipe -O3 -g -flto -fPIC \
	  -fno-plt -fstack-clash-protection -fcf-protection -fstack-protector-strong \
	  -I $(KRML_HOME)/include \
	  -I $(KRML_LIB)/dist/minimal -I dist \
	  -I $(STEEL_HOME)/include/steel \
	  -pthread -lpthread \
	  -Wall -Wextra \
	  -march=native \
	  -Wl,-O1,--as-needed,-z,defs,-z,relro,-z,now,-z,nodlopen,-z,text \
	  -shared -fPIC \
	  $(FILES) \
	  -o out/h_starmalloc.so \

.PHONY: all world verify clean depend obj test
