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

FSTAR_OPTIONS = --cache_checked_modules $(FSTAR_INCLUDES) \
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
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	@echo $*

.PRECIOUS: %.ml
%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

clean:
	-rm -rf .depend obj dist hints bench/*.{cmx,cmi,o,out}

.PRECIOUS: %.krml
obj/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

ALL_MODULE_NAMES=$(basename $(ALL_SOURCE_FILES))
FILTERED_STEEL_FILES = \
  obj/FStar_MSTTotal.krml \
  obj/FStar_NMSTTotal.krml \
  obj/FStar_NMST.krml \
  obj/FStar_MST.krml \
  obj/Steel_Effect.krml \
  obj/Steel_Effect_Atomic.krml \
  obj/Steel_HigherReference.krml \
  obj/Steel_Reference.krml \
  obj/Steel_Semantics_Hoare_MST.krml \
  obj/Some_lemmas.krml \
  obj/Steel_HigherArray0.krml \
  obj/Allocator.krml

FILTERED_KRML_FILES = $(filter-out $(FILTERED_STEEL_FILES), $(ALL_KRML_FILES))

extract: $(FILTERED_KRML_FILES)
	mkdir -p dist
	$(KRML_EXE) -skip-compilation -no-prefix Mman -tmpdir dist \
     -bundle 'FStar.\*,Steel.\*' $^


test: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmlib/dist/generic -I dist -lbsd \
	-o bench/a.out dist/Impl_Test.c
#-o bench/a.out bench/test.c
#-shared -fPIC -o alloc/malloc.so \

test2: verify extract
	gcc -DKRML_VERIFIED_UINT128 \
	-I $(KRML_HOME)/include \
	-I $(KRML_HOME)/krmlib/dist/generic -I dist -lbsd \
-o bench/a.out \
dist/Aux.h \
dist/Impl_AVL_M.h \
dist/Impl_BST_M.h \
dist/Impl_Test_Mono.h \
dist/Impl_Trees_M.h \
dist/Impl_Trees_Rotate3_M.h \
dist/Impl_Trees_Rotate2_M.h \
dist/Impl_Trees_Rotate_M.h \
dist/Main.h \
dist/Mman.h \
dist/internal/Main.h \
dist/Impl_AVL_M.c \
dist/Impl_BST_M.c \
dist/Impl_Test_Mono.c \
dist/Impl_Trees_M.c \
dist/Impl_Trees_Rotate3_M.c \
dist/Impl_Trees_Rotate2_M.c \
dist/Impl_Trees_Rotate_M.c \
dist/Main.c \
alloc/lib-alloc.c



#$(KRML_HOME)/krmllib/dist/generic/Prims.h \
#alloc/lib-alloc.c \
#$(KRML_HOME)/krmllib/dist/generic/prims.c \
#$(KRML_HOME)/include/krml/internal/compat.h \
#$(KRML_HOME)/krmllib/dist/generic/fstar_int32.c \
#$(KRML_HOME)/include/krmllib.h \

#dist/Impl_Test_Mono.c \
#dist/Impl_BST_M.h \
#dist/Map_M.h \
#dist/Impl_Test.h \
#alloc/lib-alloc.c \
#dist/internal/Prims.h \
#dist/internal/Main.h \


#-o bench/a.out bench/test2.c alloc/lib-alloc0.c

test-array: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmlib/dist/minimal -I dist -lbsd \
	-o bench/array.a.out bench/test-array.c
liballoc: verify extract
	gcc -O0 -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmlib/dist/minimal -I dist -I /usr/include/sys -shared -fPIC alloc/lib-alloc.c -o bench/malloc.so
	gcc -O0 -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmlib/dist/minimal -I dist -I /usr/include/sys/ -o bench/alloc.a.out bench/test-alloc.c
test-alloc1: liballoc
	LD_PRELOAD=bench/malloc.so ./bench/alloc.a.out
test-alloc2: liballoc
	LD_PRELOAD=bench/malloc.so zathura

testopt: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmlib/dist/minimal -I dist -lbsd -O2 \
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
#	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmlib/dist/minimal -o $@ -c $<

.PHONY: all world verify clean depend hints obj test
