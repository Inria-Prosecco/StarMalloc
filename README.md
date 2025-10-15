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

