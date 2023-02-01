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
		-bundle Steel.SpinLock= -bundle 'FStar.\*,Steel.\*' \
    -no-prefix Main \
		-warn-error +9 \
		-add-include 'Steel_SpinLock:"krml/steel_types.h"' $^

# test classic AVL trees
test: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I dist -lbsd \
	-o bench/a.out dist/Impl_Test.c

FILES = \
$(KRML_HOME)/krmllib/c/steel_spinlock.c \
dist/Aux.h \
dist/ArrayList.h \
dist/BlobList.h \
dist/Map_M.h \
dist/Impl_AVL_M.h \
dist/Impl_BST_M.h \
dist/Impl_Test_Mono.h \
dist/Impl_Trees_M.h \
dist/Impl_Trees_Rotate3_M.h \
dist/Impl_Trees_Rotate2_M.h \
dist/Impl_Trees_Rotate_M.h \
dist/LargeAlloc.h \
dist/Main.h \
dist/SmallAlloc.h \
dist/SizeClass.h \
dist/Slabs.h \
dist/Slots.h \
dist/Steel_SpinLock.h \
dist/Bitmap5.h \
dist/Utils2.h \
dist/Mman.h \
dist/ArrayList.c \
dist/BlobList.c \
dist/Map_M.c \
dist/Impl_AVL_M.c \
dist/Impl_BST_M.c \
dist/Impl_Test_Mono.c \
dist/Impl_Trees_M.c \
dist/Impl_Trees_Rotate3_M.c \
dist/Impl_Trees_Rotate2_M.c \
dist/Impl_Trees_Rotate_M.c \
dist/LargeAlloc.c \
dist/Main.c \
dist/SmallAlloc.c \
dist/SizeClass.c \
dist/Slabs.c \
dist/Slots.c \
dist/Bitmap5.c \
dist/Utils2.c \
src/utils.c \
src/lib-alloc0.c \
src/main-mmap.h \
src/main-mmap.c
#src/slab-alloc.c \
#src/slab-alloc.h

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

test-slab: verify extract
	gcc-12 -O0 -g -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
-o bench/a.out \
$(FILES) \
bench/test-slab.c \
src/lib-alloc.c
	./bench/a.out

# test the allocator with a static binary
test-alloc0bis: verify extract
	gcc -O0 -pg -DKRML_VERIFIED_UINT128 \
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
test-compile-alloc-lib: verify extract
	gcc -O2 -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmllib/dist/minimal -I dist \
	-pthread \
-shared -fPIC -o bench/malloc.so \
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
