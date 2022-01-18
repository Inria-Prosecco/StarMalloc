all: world

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

INCLUDE_PATH = $(FSTAR_HOME)/ulib/.cache $(FSTAR_HOME)/ulib/experimental

ifdef KREMLIN_HOME
KRML_EXE = $(KREMLIN_HOME)/krml
endif

world: verify

hints:
	mkdir $@

obj:
	mkdir $@

FSTAR_OPTIONS = --cache_checked_modules \
		--cmi --odir obj --cache_dir obj \
	        --already_cached 'Prims,FStar,LowStar,Steel' \
		$(addprefix --include ,$(INCLUDE_PATH)) \
		$(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

ALL_SOURCE_FILES = $(wildcard *.fst *.fsti)

# We need to add some Low* files to the dependency roots, because F* extracts Steel.C null to LowStar null
# since the KReMLin AST does not have a node for null
# TODO: This should be removed, and support for Steel.C null should be directly added to KReMLin instead
SOME_LOWSTAR_FILES = $(FSTAR_HOME)/ulib/LowStar.Monotonic.Buffer.fst $(FSTAR_HOME)/ulib/LowStar.Buffer.fst

.depend: $(ALL_SOURCE_FILES) Makefile
	@$(FSTAR) --dep full $(ALL_SOURCE_FILES) $(SOME_LOWSTAR_FILES) > $@.tmp
	@mv $@.tmp $@

depend: .depend

-include .depend

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	echo $*

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PRECIOUS: %.ml
%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

clean:
	-rm -rf .depend obj dist hints

ifdef KREMLIN_HOME

.PRECIOUS: %.krml
obj/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

ALL_MODULE_NAMES=$(basename $(ALL_SOURCE_FILES))
FILTERED_KRML_FILES=$(filter-out obj/FStar_NMST.krml obj/Steel_%.krml,$(ALL_KRML_FILES))

extract: $(FILTERED_KRML_FILES)
	mkdir -p dist
	$(KRML_EXE) -skip-compilation -skip-makefiles -tmpdir dist \
     -bundle 'FStar.\*,Steel.\*' $^

test: verify extract
	gcc -DKRML_VERIFIED_UINT128 -I $(KREMLIN_HOME)/include -I $(KREMLIN_HOME)/kremlib/dist/minimal -I dist test.c


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

else # no KREMLIN_HOME

extract:
	@echo "KReMLin is not installed, skipping extraction"

endif # KREMLIN_HOME

.PHONY: all world verify clean depend hints obj test
