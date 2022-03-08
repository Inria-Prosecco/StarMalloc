all: world

# Many thanks to Jonathan Protzenko for its Low* tutorial

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

include Makefile.include

INCLUDE_PATH = $(FSTAR_HOME)/ulib/.cache $(FSTAR_HOME)/ulib/experimental lib_avl/

KRML_EXE = $(KREMLIN_HOME)/krml

world: verify

hints:
	mkdir $@

obj:
	mkdir $@

FSTAR_OPTIONS = --cache_checked_modules $(FSTAR_INCLUDES) \
		--cmi --odir obj --cache_dir obj \
	        --already_cached 'Prims,FStar,LowStar,Steel' \
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
	-rm -rf .depend obj dist hints a.out ocaml.a.out bench.cmx bench.cmi bench.o

.PRECIOUS: %.krml
obj/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

ALL_MODULE_NAMES=$(basename $(ALL_SOURCE_FILES))
FILTERED_KRML_FILES=$(filter-out obj/FStar_NMST.krml obj/Steel_%.krml \
  obj/Allocator.krml obj/Some_lemmas.krml,\
  $(ALL_KRML_FILES))

extract: $(FILTERED_KRML_FILES)
	mkdir -p dist
	$(KRML_EXE) -skip-compilation -skip-makefiles -tmpdir dist \
     -bundle 'FStar.\*,Steel.\*' $^

test: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KREMLIN_HOME)/include -I $(KREMLIN_HOME)/kremlib/dist/minimal -I dist -lbsd test.c

testopt: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KREMLIN_HOME)/include -I $(KREMLIN_HOME)/kremlib/dist/minimal -I dist -O2 -lbsd test.c

testocaml:
	ocamlopt -o ocaml.a.out bench.ml

#ALL_C_FILES=$(addsuffix .c,$(ALL_MODULE_NAMES))
#
#$(ALL_C_FILES): extract
#	test -f $@
#	touch $@
#
#ALL_O_FILES=$(subst .c,.o,$(ALL_C_FILES))
#
#$(ALL_O_FILES): %.o: %.c
#	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KREMLIN_HOME)/include -I $(KREMLIN_HOME)/kremlib/dist/minimal -o $@ -c $<

.PHONY: all world verify clean depend hints obj test
