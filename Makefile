all: world

# Many thanks to Jonathan Protzenko for its Low* tutorial

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

include Makefile.include

INCLUDE_PATH = $(FSTAR_HOME)/ulib/.cache $(FSTAR_HOME)/ulib/experimental lib_avl/

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
		-bundle 'Impl.Trees.\*'[rename=AVL] \
    -no-prefix Main \
    -no-prefix LargeAlloc \
		-warn-error +9 \
		-add-include 'Steel_SpinLock:"krml/steel_types.h"' $^

# test classic AVL trees
test: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I dist -lbsd \
	-o bench/a.out dist/Impl_Test.c

FILES = \
$(KRML_HOME)/krmllib/c/steel_spinlock.c \
dist/ArrayList.h \
dist/AVL.h \
dist/Map_M.h \
dist/Impl_AVL_M.h \
dist/Impl_BST_M.h \
dist/krmlinit.h \
dist/LargeAlloc.h \
dist/Main.h \
dist/StarMalloc.h \
dist/SizeClass.h \
dist/SlabsAlloc.h \
dist/SlabsFree.h \
dist/SlotsAlloc.h \
dist/SlotsFree.h \
dist/Steel_SpinLock.h \
dist/Bitmap5.h \
dist/Utils2.h \
dist/Mman.h \
dist/ArrayList.c \
dist/AVL.c \
dist/Map_M.c \
dist/Impl_AVL_M.c \
dist/Impl_BST_M.c \
dist/krmlinit.c \
dist/LargeAlloc.c \
dist/Main.c \
dist/StarMalloc.c \
dist/SizeClass.c \
dist/SlabsAlloc.c \
dist/SlabsFree.c \
dist/SlotsAlloc.c \
dist/SlotsFree.c \
dist/Bitmap5.c \
dist/Utils2.c \
src/utils.c \
src/main-mmap.h \
src/main-mmap.c

# test AVL trees suited for allocator metadata (no malloc, manual mmap)
test-tree: verify extract
	gcc -O2 -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal -I dist \
	-o bench/mavl.out $(FILES) src/lib-alloc.c bench/test2.c

# test the compilation of the allocator
test-compile-alloc: verify extract
	gcc -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
-o bench/a.out \
$(FILES) src/lib-alloc.c

# test the allocator with a static binary
test-alloc0: verify extract
	gcc -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-alloc.c \
src/lib-alloc.c
	./bench/a.out

test-both: verify extract
	gcc -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-both.c
	./bench/a.out

test-slab: verify extract
	gcc -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-slab.c
	./bench/a.out

test-mmap: verify extract
	gcc -pthread -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-avl.c
	./bench/a.out

# test the allocator with a static binary
test-alloc0bis: verify extract
	gcc -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
  -pthread \
-o bench/a.out \
$(FILES) \
bench/test-alloc2.c \
src/lib-alloc.c
	./bench/a.out

# test the compilation of the allocator as a shared library
#gcc -g -O0 -DKRML_VERIFIED_UINT128
lib: verify extract
	gcc -O2 -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
	-pthread \
-shared -fPIC -o bench/starmalloc.so \
$(FILES) \
src/lib-alloc.c

#-Wmissing-prototypes
#-std=c17
#-Wall -Wextra -Wcast-align=strict -Wcast-qual
hardened_lib: verify extract
	gcc -DKRML_VERIFIED_UINT128 \
	-pipe -O3 -flto -fPIC -fvisibility=hidden -fno-plt \
	-fstack-clash-protection -fcf-protection -fstack-protector-strong \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
	-pthread \
	-Wwrite-strings -Werror -march=native \
	-Wl,-O1,--as-needed,-z,defs,-z,relro,-z,now,-z,nodlopen,-z,text \
-shared -fPIC -o bench/h_starmalloc.so \
$(FILES) \
src/lib-alloc.c

# test the allocator as a shared library with a simple program
test-alloc1: test-compile-alloc-lib
	gcc -O0 bench/test-alloc.c -o bench/alloc.a.out
	LD_PRELOAD=bench/malloc.so ./bench/alloc.a.out
# test the allocator as a shared library with zathura
test-alloc2: test-compile-alloc-lib
	gcc -O0 bench/test-alloc2.c -o bench/alloc.a.out
	LD_PRELOAD=bench/malloc.so ./bench/alloc.a.out

test-alloc2bis: test-compile-alloc-lib
	gcc -O0 bench/test-alloc2.c -o bench/alloc.a.out
	LD_PRELOAD= ./bench/alloc.a.out

#test-alloc2ter: test-compile-alloc-lib
#	gcc -O0 bench/test-alloc2.c -o bench/alloc.a.out
#	LD_PRELOAD=../hardened_malloc/out/libhardened_malloc.so ./bench/alloc.a.out

test-alloc3: test-compile-alloc-lib
	LD_PRELOAD=bench/malloc.so zathura

test-array: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal -I dist -lbsd \
	-o bench/array.a.out bench/test-array.c

testopt: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal -I dist -lbsd -O2 \
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
#	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal -o $@ -c $<

.PHONY: all world verify clean depend hints obj test
