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

ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) --dep full $(ALL_SOURCE_FILES) > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend
endif

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
	  -no-prefix ExternUtils \
	  -warn-error +9 \
	  -add-include 'Steel_SpinLock:"steel_types.h"' \
	  -add-include 'Steel_SpinLock:"steel_base.h"' \
	  $^

# TODO: improve this
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
dist/SizeClassSelection.c \
dist/Config.c \
c/utils.c \
c/fatal_error.c \
c/memory.c \
c/lib-alloc.c

# general approach = try to use most of hardened_malloc's flags
# use _DEFAULT_SOURCE instead of deprecated _BSD_SOURCE
# (2024-05-31) manually tested gcc/clang versions:
# - gcc 14.1.0
# - gcc 13.2.0
# - gcc 12.3.0
# - gcc 11.4.0
# - clang 18.1.6
# - clang 17.0.6
# - clang 16.0.6
# - clang 15.0.7
# TODO:
# - add -Wcast-align=strict or -Wcast-qual
SHARED_FLAGS = -DRKML_VERIFIED_UINT128 \
	       -I dist \
	       -I $(KRML_HOME)/include \
	       -I $(KRML_LIB)/dist/minimal \
	       -I $(STEEL_HOME)/include/steel \
	       -pthread -lpthread \
	       -Wall -Wextra -Wwrite-strings -Wundef \
	       -std=c17 -D_DEFAULT_SOURCE \
	       -shared -fPIC

build_from_extracted_files_debug:
	mkdir -p out
	$(CC) $(SHARED_FLAGS) \
	  -O0 -g \
	  $(FILES) \
	  -o out/starmalloc-debug.so

debug_light: build_from_extracted_files_debug
debug_lib: verify extract
	$(MAKE) build_from_extracted_files_debug

# visible symbols are restricted using -fvisibility=hidden
# (this can be checked using nm -gC out/file.so)
build_from_extracted_files:
	mkdir -p out
	$(CC) $(SHARED_FLAGS) \
	  -pipe -O3 -flto -fPIC \
	  -fno-plt -fstack-clash-protection -fcf-protection -fstack-protector-strong \
	  -fvisibility=hidden \
	  -march=native \
	  -Wl,-O1,--as-needed,-z,defs,-z,relro,-z,now,-z,nodlopen,-z,text \
	  $(FILES) \
	  -o out/starmalloc.so

light: build_from_extracted_files
lib: verify extract
	$(MAKE) extract build_from_extracted_files

hardened_lib:
	@echo "This target has been deprecated, use the lib target instead."
	exit 1

.PHONY: all world verify clean depend obj test
