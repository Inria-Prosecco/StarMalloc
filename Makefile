all: world
world: verify

# Many thanks to Jonathan Protzenko for its Low* tutorial

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe
KRML_EXE = $(KRML_HOME)/krml

include Makefile.include

FSTAR_OPTIONS = $(SIL) --cache_checked_modules $(FSTAR_INCLUDES) \
    --already_cached 'FStar Steel C Prims' \
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

# TODO: remove following hack:
# add-include 'Steel_Spinlock:"steel_base.h"'
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
c/memory.c

# test the allocator with a static binary
test-alloc: verify extract
	$(CC) -O0 -g -DKRML_VERIFIED_UINT126 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
	-I $(STEEL_HOME)/include/steel \
-o a.out \
$(FILES) \
tests/test-alloc.c \
c/lib-alloc.c
	./a.out
test-alloc2: verify extract
	$(CC) -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
	-I $(STEEL_HOME)/include/steel \
  -pthread \
-o a.out \
$(FILES) \
tests/test-alloc2.c \
c/lib-alloc.c
	./a.out

lib:
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
c/lib-alloc.c \
-o out/starmalloc.so

#-Wmissing-prototypes
#-std=c17
#-Wall -Wextra -Wcast-align=strict -Wcast-qual
#-fvisibility=hidden
hardened_lib:
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
c/lib-alloc.c \
-o out/h_starmalloc.so \

#TODO: remove
# test classic AVL trees
#test: verify extract
#	$(CC) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/generic -I dist -lbsd \
#	-o bench/a.out dist/Impl_Test.c
# test AVL trees suited for allocator metadata (no malloc, manual mmap)
#test-tree: verify extract
#	$(CC) -O2 -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/minimal -I dist \
#	-o bench/mavl.out $(FILES) src/lib-alloc.c bench/test2.c

# test the compilation of the allocator
#test-compile-alloc: verify extract
#	$(CC) -DKRML_VERIFIED_UINT128 \
#	-I $(KRML_HOME)/include \
#	-I $(KRML_LIB)/dist/minimal -I dist \
#-o bench/a.out \
#$(FILES) src/lib-alloc.c
#test-both: verify extract
#	$(CC) -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
#	-I $(KRML_HOME)/include \
#	-I $(KRML_LIB)/dist/minimal -I dist \
#-o bench/a.out \
#$(FILES) \
#bench/test-both.c
#	./bench/a.out
#test-slab: verify extract
#	$(CC) -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
#	-I $(KRML_HOME)/include \
#	-I $(KRML_LIB)/dist/minimal -I dist \
#-o bench/a.out \
#$(FILES) \
#bench/test-slab.c
#	./bench/a.out
#test-mmap: verify extract
#	$(CC) -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
#	-I $(KRML_HOME)/include \
#	-I $(KRML_LIB)/dist/minimal -I dist \
#-o bench/a.out \
#$(FILES) \
#bench/test-avl.c
#	./bench/a.out
# test the allocator as a shared library with a simple program
#test-alloc1: lib
#	$(CC) -O0 bench/test-alloc.c -o bench/alloc.a.out
#	LD_PRELOAD=bench/starmalloc.so ./bench/alloc.a.out
## test the allocator as a shared library with zathura
#test-alloc2: lib
#	$(CC) -O0 bench/test-alloc2.c -o bench/alloc.a.out
#	LD_PRELOAD=bench/starmalloc.so ./bench/alloc.a.out
#
#test-alloc2bis: lib
#	$(CC) -O0 bench/test-alloc2.c -o bench/alloc.a.out
#	LD_PRELOAD= ./bench/alloc.a.out

#test-alloc2ter: test-compile-alloc-lib
#	$(CC) -O0 bench/test-alloc2.c -o bench/alloc.a.out
#	LD_PRELOAD=../hardened_malloc/out/libhardened_malloc.so ./bench/alloc.a.out
#test-alloc3: test-compile-alloc-lib
#	LD_PRELOAD=bench/malloc.so zathura
#test-array: verify extract
#	$(CC) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/minimal -I dist -lbsd \
#	-o bench/array.a.out bench/test-array.c
#
#testopt: verify extract
#	$(CC) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/minimal -I dist -lbsd -O2 \
#	-o bench/a.out bench/test.c
#testocaml:
#	ocamlopt -o bench/ocaml.a.out bench/bench.ml
#testcpp:
#	g++ -O2 -o bench/cpp.a.out bench/main.cpp
#bench: testopt testocaml testcpp
#	./bench/bench.sh

#ALL_MODULE_NAMES=$(basename $(ALL_SOURCE_FILES))
#ALL_C_FILES=$(addsuffix .c,$(ALL_MODULE_NAMES))
#
#$(ALL_C_FILES): extract
#	test -f $@
#	touch $@
#
#ALL_O_FILES=$(subst .c,.o,$(ALL_C_FILES))
#
#$(ALL_O_FILES): %.o: %.c
#	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/minimal -o $@ -c $<

.PHONY: all world verify clean depend obj test
