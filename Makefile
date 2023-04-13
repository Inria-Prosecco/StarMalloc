all: world

# Many thanks to Jonathan Protzenko for its Low* tutorial

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

include Makefile.include

KRML_EXE = $(KRML_HOME)/krml

world: verify

hints:
	mkdir $@

obj:
	mkdir $@

FSTAR_OPTIONS = $(SIL) --cache_checked_modules $(FSTAR_INCLUDES) \
    --already_cached 'FStar Steel C Prims' \
		--cmi --odir obj --cache_dir obj \
		$(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

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

.PRECIOUS: %.ml
%.ml:
	@echo "[EXTRACT-ML $(basename $(notdir $@))]"
	$(Q)$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

clean:
	-rm -rf .depend obj dist hints bench/*.{cmx,cmi,o,out}

.PRECIOUS: %.krml
obj/%.krml:
	@echo "[EXTRACT    $(basename $(notdir $@))]"
	$(Q)$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

ALL_MODULE_NAMES=$(basename $(ALL_SOURCE_FILES))

extract: $(ALL_KRML_FILES)
	mkdir -p dist
	$(KRML_EXE) -skip-compilation -no-prefix Mman -tmpdir dist \
    -library Steel.ArrayArith -static-header Steel.ArrayArith -no-prefix Steel.ArrayArith \
		-bundle Steel.SpinLock= -bundle 'FStar.\*,Steel.\*' \
		-bundle 'Map.\*,Impl.\*,Spec.\*'[rename=AVL] \
		-bundle 'StarMalloc=Main,LargeAlloc'[rename=StarMalloc] \
		-bundle 'SlabsCommon,SlabsFree,SlabsAlloc'[rename=Slabs] \
		-bundle 'SlotsFree,SlotsAlloc'[rename=Slots] \
		-bundle 'ArrayList,ArrayListGen'[rename=ArrayList] \
    -no-prefix Main \
    -no-prefix LargeAlloc \
		-warn-error +9 \
		-add-include 'Steel_SpinLock:"krml/steel_types.h"' $^

patch: extract
	sed 's/Steel_SpinLock_acquire(/pthread_mutex_lock(\&/g' -i dist/StarMalloc.c
	sed 's/Steel_SpinLock_release(/pthread_mutex_unlock(\&/g' -i dist/StarMalloc.c
	sed 's/uint64_t x1 = Impl_Trees_Types_ptr_to_u64(x);/uintptr_t x1 = (uintptr_t) x;/g' -i dist/AVL.c
	sed 's/uint64_t y1 = Impl_Trees_Types_ptr_to_u64(y);/uintptr_t y1 = (uintptr_t) y;/g' -i dist/AVL.c

# test classic AVL trees
test: verify extract
	$(CC) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/generic -I dist -lbsd \
	-o bench/a.out dist/Impl_Test.c

FILES = \
$(KRML_LIB)/c/steel_spinlock.c \
dist/ArrayList.c \
dist/AVL.c \
dist/krmlinit.c \
dist/StarMalloc.c \
dist/Slabs.c \
dist/Slots.c \
dist/Bitmap5.c \
dist/Utils2.c \
src/utils.c \
src/main-mmap.c

# test AVL trees suited for allocator metadata (no malloc, manual mmap)
test-tree: verify extract
	$(CC) -O2 -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/minimal -I dist \
	-o bench/mavl.out $(FILES) src/lib-alloc.c bench/test2.c

# test the compilation of the allocator
test-compile-alloc: verify extract
	$(CC) -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
-o bench/a.out \
$(FILES) src/lib-alloc.c

# test the allocator with a static binary
test-alloc0: verify extract patch
	$(CC) -O0 -g -DKRML_VERIFIED_UINT126 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-alloc.c \
src/lib-alloc.c
	./bench/a.out

test-both: verify extract
	$(CC) -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-both.c
	./bench/a.out

test-slab: verify extract
	$(CC) -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-slab.c
	./bench/a.out

test-mmap: verify extract
	$(CC) -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-avl.c
	./bench/a.out

# test the allocator with a static binary
test-alloc0bis: verify extract patch
	$(CC) -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
  -pthread \
-o bench/a.out \
$(FILES) \
bench/test-alloc2.c \
src/lib-alloc.c
	./bench/a.out

# foptimize-strlen = gcc issue culprit
lib: verify extract patch
	echo "using ${CC} compiler"
	$(CC) -O3 \
	-DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
	-pthread -lpthread \
        -std=gnu11 \
-shared -fPIC \
$(FILES) \
src/lib-alloc.c \
-o bench/starmalloc.so

#-Wmissing-prototypes
#-std=c17
#-Wall -Wextra -Wcast-align=strict -Wcast-qual
#-fvisibility=hidden
hardened_lib: verify extract patch
	$(CC) -DKRML_VERIFIED_UINT128 \
	-pipe -O3 -flto -fPIC \
	-fno-plt -fstack-clash-protection -fcf-protection -fstack-protector-strong \
	-I $(KRML_HOME)/include \
	-I $(KRML_LIB)/dist/minimal -I dist \
	-pthread -lpthread \
	-Wwrite-strings -Wno-c++17-extensions -Werror -march=native \
	-Wl,-O1,--as-needed,-z,defs,-z,relro,-z,now,-z,nodlopen,-z,text \
-shared -fPIC \
$(FILES) \
src/lib-alloc.c \
-o bench/h_starmalloc.so \

# test the allocator as a shared library with a simple program
test-alloc1: test-compile-alloc-lib
	$(CC) -O0 bench/test-alloc.c -o bench/alloc.a.out
	LD_PRELOAD=bench/malloc.so ./bench/alloc.a.out
# test the allocator as a shared library with zathura
test-alloc2: test-compile-alloc-lib
	$(CC) -O0 bench/test-alloc2.c -o bench/alloc.a.out
	LD_PRELOAD=bench/malloc.so ./bench/alloc.a.out

test-alloc2bis: test-compile-alloc-lib
	$(CC) -O0 bench/test-alloc2.c -o bench/alloc.a.out
	LD_PRELOAD= ./bench/alloc.a.out

#test-alloc2ter: test-compile-alloc-lib
#	$(CC) -O0 bench/test-alloc2.c -o bench/alloc.a.out
#	LD_PRELOAD=../hardened_malloc/out/libhardened_malloc.so ./bench/alloc.a.out

test-alloc3: test-compile-alloc-lib
	LD_PRELOAD=bench/malloc.so zathura

test-array: verify extract
	$(CC) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/minimal -I dist -lbsd \
	-o bench/array.a.out bench/test-array.c

testopt: verify extract
	$(CC) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_LIB)/dist/minimal -I dist -lbsd -O2 \
	-o bench/a.out bench/test.c
testocaml:
	ocamlopt -o bench/ocaml.a.out bench/bench.ml
testcpp:
	g++ -O2 -o bench/cpp.a.out bench/main.cpp
bench: testopt testocaml testcpp
	./bench/bench.sh

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

.PHONY: all world verify clean depend hints obj test
