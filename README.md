# StarMalloc

A verified security-oriented general-purpose userspace memory allocator, that
can be used as a drop-in replacement for the libc allocator.
It is heavily inspired from
[hardened\_malloc](https://github.com/GrapheneOS/hardened_malloc)'s design.

Usual C memory management primitives (including `malloc`, `free`, `realloc`,
`aligned_alloc`) are formally verified using the
[F\*](https://github.com/FStarLang/FStar) verification framework and the
[Steel](https://github.com/FStarLang/Steel) separation logic for memory safety
and functional correctness.

Corresponding verified F* code is extracted to C code thanks to the
[KaRaMeL](https://github.com/FStarLang/karamel) compiler.

## Corresponding papers

- StarMalloc: Verifying a Modern, Hardened Memory Allocator, OOPSLA'24 [[doi + pdf]](https://dl.acm.org/doi/10.1145/3689773)

## Performance and usability

StarMalloc has been successfully tested on the
[mimalloc-bench](https://github.com/daanx/mimalloc-bench) benchmarking suite,
so that its properties can be compared with many other allocators.

Using a modified version of Firefox (additional `--disable-jemalloc` build flag
to use the environment allocator), it has successfully been tested on standard
browser benchmarks (such as JetStream2 and Speedometer 2.1) as a replacement
for the Firefox-shipped memory allocator.

In terms of performance, it is roughly on par with hardened_malloc whose design
was used as a basis. On the mimalloc-benchmarking suite, using hardened_malloc
as a baseline, we get performance ranging from 0.70x to 1.30x, with a geometric
mean on all 31 benches of ~1 (more details in the paper). Please note that some
implementation differences remain (e.g. constant canaries vs. cryptographic
canaries, slightly different quarantine implementation, no security mechanism
for large allocations), which should have very limited performance impact.

## Artifact: experiment (E1)

### Structure of this repository

- `bench`: directory used to save benchmarks results (CSV and PDF files)
- `c`: C code included as part of StarMalloc
- `dist`: C code extracted from StarMalloc verified files
- `extern`: directory used to install mimalloc-bench benchmarks
- `lib_avl_common`, `lib_avl_mono`, `lib_bitmap`, `lib_list`, `lib_misc`: libraries included as part of StarMalloc verified files
- `obj`: directory used to store intermediate objects for extraction
- `out`: directory used to store resulting .so libraries (StarMalloc or StarMalloc with stderr logs)
- `result`: directory used to store Nix derivation build results
- `src`: StarMalloc main verified files
- `tests`: some tests to check memory allocators behaviors
- `vendor`: files included in the repository to compile StarMalloc in a standalone manner (only from C files, no other repository)

### Functions and specifications from the paper

`.fsti` files correspond to interfaces, used as abstraction barriers between `.fst` files.

Briefly:

- verified memory allocator APIs with rich specifications serving as functional correctness theorems: `src/StarMalloc.fst`
- C stubs to define more C functions from this verified basis: `c/lib-alloc.c`
- zeroing specification is included in the `malloc` signature in `src/StarMalloc.fst`
- guard pages specification: see `src/SlabsAlloc.fst`, `allocate_slab_aux_3` signature
- canaries specification is included in the slab allocator allocation functions, see `slab_malloc_generic_canary` and `slab_aligned_alloc_generic_canary` signatures in the `src/Main.Meta.fsti` file
- configuration files are `src/Config.fst{,i}`

Section 3.2/Modeling Slab Metadata

- `dispatch` definition: `src/SlabsCommon.fsti`, `f` definition (search `let f`)
- `starseq` definition: `lib_misc/SteelStarSeqUtils.fst{,i}`
- `slabs_sl_aux` definition: `src/SlabsCommon.fsti`, `left_vprop2_aux` definition
- `slabs_sl` definition: `src/SlabsCommon.fsti`, `left_vprop` definition

Section 3.2/Optimizing Slab Metadata

- `is_list` definition: `lib_list/ArrayListGen.fst{,i}`, `is_dlist2` definition
- `arraylist_sl` definition: refinement predicate is in `lib_list/ArrayListGen.fsti`, `varraylist_refine` definition
- `ind_arraylist_sl` definition: `src/SlabsCommon.fsti`, `ind_varraylist` definition
- `slabs_sl` definition: `src/SlabsCommon.fsti`, `left_vprop` definition

Section 3.3/Iterating on Verified Implementations

- `arraylist_sl` definition: refinement predicate is in `lib_list/ArrayListGen.fsti`, `varraylist_refine` definition
- `ind_arraylist_sl` definition: `src/SlabsCommon.fsti`, `ind_varraylist` definition

Section 3.4/Reusing Generic Predicates

- `available_slot` definition: `src/SlotsAlloc.fst`, `slab_vprop_aux_f` definition
- `slots_sl` definition: `src/SlotsAlloc.fst`, `slab_vprop_aux` definition
- `slab_sl` definition: `src/SlotsAlloc.fst`, `slab_vprop` definition

Section 3.4/Reusing the Slab Allocator

- in the `src/LargeAlloc.fst` file, the `trees_malloc2_aux` function reuses code from the `src/SizeClass.fst` file, that is related to the slab allocator
- in the same file, the same thing applies for the `trees_free2_aux` function

Section 3.5

- `init_size_classes` definition: `src/Main.fst`, `init_size_classes_aux` definition
- `init` definition with normalization: `src/Main.fst`, `init_size_classes` definition
- corresponding extracted C code is the `Main_Meta_init` function in `dist/StarMalloc.c`

Section 5.2/Supported APIs

- `aligned_alloc` corresponds to the verified `aligned_alloc` function in `src/StarMalloc.fst`
- `malloc_usable_size` corresponds to the verified `full_getsize` and `getsize` functions in `src/StarMalloc.fst` (stub is in `c/lib-alloc.c`)
- other exposed APIs (e.g., memalign) are defined in `c/lib-alloc.c`

Section 5.2/Hardening Features

- `malloc` corresponds to the `malloc` signature in `src/StarMalloc.fst`, serving as a functional correctness theorem
- `dispatch` definition: `src/SlabsCommon.fsti`, `f` definition (search `let f`)
- `slab_guard_intro_guard`: `src/Guards.fsti`, `mmap_trap_guard` (in particular, no `untrap` function)
- guard pages specification: see `src/SlabsAlloc.fst`, `allocate_slab_aux_3` signature

Section 5.2/Syscall Modeling

- `mmap` axiomatization: `src/Mman.fst`, `mmap_u8` signature
- alignment axiomatization: `src/ArrayAlignment.fst` file

## Security mechanisms

Most of the security mechanisms are configurable.

- Segregated metadata
- Heap canaries
- Zeroing at allocation and zeroing-on-free
- Guard pages
- Quarantine

## Verification guarantees

What does "verified" mean here? What are the properties of the allocator?
We get a functional correctness theorem that states that the allocator is behaving like a reasonable allocator. Here are some of the properties that have been proven to hold, in any supported configuration of the allocator (security mechanisms, number of arenas, ...):

- `malloc` returns `NULL` or an array of at least the requested size;
- `malloc` returns `NULL` or a 16-bytes aligned array, `aligned_alloc` returns `NULL` or an array aligned as requested (large alignments still WIP).

We also get as a corollary, as StarMalloc is developed using Steel, a concurrent separation logic (CSL) for F\*, that it is memory-safe and thread-safe. All of this assumes the soudness of the toolchain, which is already used in large other verification projects.

Out-of-scope are security properties, even though we would very much like to tackle this as future work.

## Build

## Full build

Assuming F\*, Steel and KaRaMeL have been installed, the following environment variables must be set.

- `FSTAR_HOME` pointing to the F\* installation directory,
- `STEEL_HOME` pointing to the Steel installation directory,
- `KRML_HOME` pointing to the KaRaMeL installation directory.

Only `z3-4.13.3` is currently supported to build StarMalloc.

### Light build

With only a C compiler as dependency, the following command will produce `out/starmalloc.so` out of pre-extracted C files (`dist/` directory) and vendored C files (`vendor/` directory):
`STEEL_HOME=1 KRML_HOME=1 NODEPEND=1 VENDOR=1 make light`.
(TODO: this command should be easier)

- `{FSTAR,STEEl,KRML}_HOME=1` : so that checks in `Makefile.include` will not fail
- `NODEPEND=1`: skip dependency check requiring F\*
- `VENDOR=1`: use vendored files, otherwise Steel and KaRaMeL are required

StarMalloc can then be used this way: `LD_PRELOAD=out/starmalloc.so <program>`.
Note: some programs (e.g. Firefox or Chromium) use shipped allocators instead of the system (or environment) allocator, some additional work (such as recompilation with additional build flags) may be required.

## Performance evaluation

Using `bash setup-all.sh -st-only` followed by `bash build-bench-env.sh hm bench
lean redis rocksdb linux` from the `external/mimalloc-bench` directory, the
mimalloc-bench benchmarking suite is ready to be used, assuming required
dependencies all are already installed.

From the `extern/mimalloc-bench/out/bench` directory, one can then run benchmarks
using `bash ../../bench.sh sys hm st allt no-security` to test the system
allocator, hardened\_malloc and StarMalloc on all benchmarks measuring
performance (time and memory).

## External repositories

- [hardened\_malloc](https://github.com/GrapheneOS/hardened_malloc)
- [F\*](https://github.com/FStarLang/FStar)
- [Steel](https://github.com/FStarLang/steel)
- [KaRaMeL](https://github.com/FStarLang/karamel)
- [mimalloc-bench](https://github.com/daanx/mimalloc-bench)
- [JetStream2](https://browserbench.org/JetStream/)
- [Speedometer 2.1](https://browserbench.org/Speedometer2.1/)
- [Speedometer 3.0](https://browserbench.org/Speedometer3.0/)

## Future work

- (CI) add CI check about compiling StarMalloc with `OTHERFLAGS="--admit_smt_queries true"` (currently fails on `src/Main.fst` file, upstream issue)
- (benchmark) try Speedometer 3.0
- (feature) `free_sized` (C23) and `free_aligned_sized` (C23) implementations could be refined to be stricter (only wrappers for now)
- (feature) support for 16K pages
- (feature) support for ARM MTE (Memory Tagging Extension)
- (feature) Android support
- (feature) improve support for a F\*/Steel client
- slab allocations:
  - (feature) add support for 48-bytes size-class
  - (security) slots quarantine (WIP)
  - (security) initial mapping of allocation region should be `PROT_NONE`
  - (performance) size class selection could be improved (`malloc` case = done, `aligned_alloc` case remaining)
  - (security) randomizing guard pages
- large allocations:
  - (specification) some properties could be proven about the `PTRDIFF_MAX` limit
  - (performance) AVL tree node allocation is reusing the slab allocator with an hardened configuration: use a dedicated light configuration instead

## License

All the code in this repository is released under an Apache 2.0 license, with the exception of `c/fatal_error.c` that contains some logging helpers from the [hardened\_malloc](https://github.com/GrapheneOS/hardened_malloc) repository under the MIT license.
Please note that for practical reasons, some code from Steel and KaRaMeL is vendored in `vendor/`: the Apache 2.0 license also applies to this directory.

## Authors

- Antonin Reitz `antonin.reitz@inria.fr`
- Aymeric Fromherz `aymeric.fromherz@inria.fr`
- Jonathan Protzenko `jonathan.protzenko+github@gmail.com`

