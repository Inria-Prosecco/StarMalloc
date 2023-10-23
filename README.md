# StarMalloc

A verified security-oriented general-purpose userspace memory allocator,
that can be used as a drop-in replacement for the libc allocator.
It is heavily inspired from hardened\_malloc's design.

The following symbols are/will be/will not be provided: except when explicitly mentioned, symbols are provided. ? indicates that no standard defining the corresponding symbol was found.
1. as part of C standard library
- malloc
- calloc
- realloc
- free
- aligned\_alloc (C11, TODO: check current implem)
- free\_sized (C23, TODO: refine)
- free\_aligned\_sized (C23, TODO: refine)

2. misc
- posix\_memalign (POSIX, TODO: provide it)
- malloc\_usable\_size (GNU)
- memalign (?, TODO: provide it)
- valloc (?, TODO: provide it)
- (deprecated) pvalloc (GNU, TODO: provide it)
- (deprecated) cfree (?, defined symbol as a fatal\_error, removed since glibc 2.26 (Debian oldoldstable glibc = 2.28, as of 2023-10-21))

## Build everything

`bash setup-all.sh`:
- build StarMalloc,
- clone mimalloc-bench inside `extern/mimalloc-bench`,
- build all of mimalloc-bench allocators + benches,
- install StarMalloc within mimalloc-bench dir (`extern/mimalloc-bench/extern/st`),
- tweak mimalloc-bench.

Then, lets bench StarMalloc (`st`) against the system allocator (`sys`) and hardened\_malloc (`hm`) on all benches (`allt`).
```
cd extern/mimalloc-bench/out/bench
bash ../../bench.sh sys hm st allt
```

## Build process

Requirements:
- `z3` in the `$PATH`,
- `FSTAR_HOME` environment variable set to F* installation path,
- `STEEL_HOME` environment variable set to Steel installation path,
- `KRML_HOME` environment variable set to KaRaMeL installation path,
- C compiler: `clang` or `gcc`.

Steps with corresponding Makefile build targets:
- `verify`: verification phase of F\*+Steel files, producing `obj/*.checked` files;
- `extract`: extraction phase of F\*+Steel files, producing `obj/*.krml` files then `dist/` C files;
- `lib`: produces `out/starmalloc.so`;
- (recommended) `hardened_lib`: produces `out/h_starmalloc.so`.

tl;dr:
- `make lib hardened_lib -j $CORES` produces `out/*.so` files;
- `OTHERFLAGS="--admit_smt_queries true" make lib hardened_lib -j $CORES` trick.

## Some tests

A few examples:
- `make test-alloc`: sequential basic local test,
- `make test-alloc2`: multithreaded basic local test,
- `LD_PRELOAD=out/h_starmalloc.so zathura` was empirically a good test (requires the zathura PDF reader).

## Benchmarks

### mimalloc-bench

mimalloc-bench is a memory allocators benchmarking suite.
Most of its benches are currently working with StarMalloc, including on a 64-core machine (it allowed us to catch bugs!).

### WIP: Firefox

All of this is very much WIP.
[ok] - Build Firefox with `--disable-jemalloc` flag.
[ok] - Test it with StarMalloc.
  - issue with posix\_memalign
  - expose all symbols
  - C++ stubs with fatal\_error
- Bench it wrt to other allocators.

## Properties of the allocator

Verified code:
- functional correctness 1: malloc returns NULL or an array of at least the requested size
- functional correctness 2: malloc returns a 16-bytes aligned array
- functional correctness 3: thread-safety (mutexes)
- (WIP) functional correctness 4: allocation size limited to `PTRDIFF_MAX` to avoid undefined behaviour
- memory safety
- (WIP?) deadlock-free(?)

C wrapper/low-level initialization:
- based on hardened\_malloc's init, relies on atomic instructions to avoid race conditions
- short, auditable
- (WIP) defensive programming
- (WIP) correct behaviour wrt fork syscall using pthread\_atfork hook

## Structure of the allocator

### Allocation process (malloc case)

malloc(size)
0. size <= PAGE\_SIZE (this bound has to be adjusted when using canaries), if so goto 10., otherwise goto 20.

10. within the arena corresponding to the thread, find corresponding size class
11. find a slab with at least one free slot
  - look for partial slabs
  - look for empty slabs
  - if there is none in these two categories, add slabs to the empty slabs list from the so-far unused memory space
12. find free slot position
13. update metadata, return corresponding pointer

20. ptr = mmap(size), check result
21. insert (ptr, size) into the AVL tree containing metadata
22. return corresponding pointer

### Deallocation process (free case)

free(ptr)
0. is the pointer within the very large contiguous memory regions containing adjacent arenas, which are containg adjacent size classes? if so goto 10., otherwise goto 20.

10. using pointer difference between ptr and the start of the slab region, find the corresponding arena
11. using pointer difference between ptr and the start of the arena, find the corresponding size class
12. using pointer difference between ptr and the start of the size class, find the corresponding slab
13. using pointer difference between ptr and the start of the slab, find the corresponding slot
14. check using slot metadata whether ptr corresponds to an actual allocation, if so goto 15., otherwise fail
15. update metadata

20. check whether corresponds to an actual allocation by looking for ptr in the metadata map (which is an AVL tree); if so goto 21., otherwise fail
21. corresponding size is now known; remove (ptr, size) from the map

## Security mechanisms of the allocator

- size classes + arenas
- out-of-band metadata
- no free lists/no size class cache
- zeroing on free
- zeroing check on allocation
- guard pages
- quarantine
- canaries

## CI

3 sorts of jobs:
1. Basic: on every push, try to build the project.
2. (WIP) Improved: on every push, test the project on all mimalloc-bench benches.
3. (WIP) PR development model, refresh dist/: track dist/ under version control, no PR should be merged without the build succeeding and dist/ being (automatically?) refreshed.
4. (WIP) nightly: every day, build StarMalloc main branch using bleeding-edge F\*, Steel, KaRaMeL, and compare on the same commit using the flake.lock dependencies versions.

## TODO
- F\*/Steel
  - remove last assume (t\_of casts...)
  - replace last sladmits with proper fatal error stubs
  - improve quarantine
  - initial large memory mappings should have `PROT_NONE` permissions
  - hidden page size
  - calloc: remove overflow risk

- C code
  - more memory-related errno checks wrt ENOMEM
  - limit allocation size to `PTRDIFF_MAX` (glibc behaviour)
  - fatal\_error if StarMalloc\_free fails
  - C++ stubs
  - [ok] pthread\_atfork hook
    - [ok] handwritten implementation
    - [sk] generated implementation(?)

- Makefile
  - debug flag/distinct debug targets (remove -g as default compilation flag)
  - compilation flags
    - limit visible symbols
    - -fhardened flag: FORTIFY\_SOURCE, stack-clash protection, etc
  - remaining warnings using -Wall -Wextra
    - -Wc++17-extensions (static\_assert with no message)
    - -Wunused (variable/parameter)

- hacl-star reuse:
  - use libmemzero
  - use cryptographic primitives for canaries

- PRs:
  - KaRaMeL: test for `size_t`
  - mimalloc-bench: install all allocators and benches using Nix

- CI:
  - dist/ auto-refresh, forcing PR usage
  - nightly
  - benches
    - mimalloc-bench (upstream nix first!)
    - Firefox
      - firefox build
      - firefox benchmark in headless mode, using local speedometer

- benches
  - fix mimalloc-bench/perf
    - rptest: missing memalign symbol
    - lua: bad-alloc, missing symbol?
    - rocksdb: missing posix\_memalign symbol
    - fix sh6bench/sh8bench exit statuses(?)
  - fix mimalloc-bench/security
  - large application: Firefox?
    - [ok] build Firefox
      So far, using a systemd-nspawn Arch Linux container (built from a systemd-nspawn Debian container, Ubuntu does not provide pacstrap; patch and pkgconf seem to be missing build dependencies of the firefox Arch Linux package), obtained a patched version of firefox 118.
    - [ok] use Firefox from container using xwayland
      Incompatibility between glibc versions of the build container (2.38) and my OS (2.37), need to use a Arch Linux container + some hackery to make it work.
    - [wip] use Firefox with StarMalloc
      - fix posix_memalign (currently works when removing this stub)
  - HardsHeap?
- cleaning
  - remove

## External repositories

- hardened\_malloc: https://github.com/GrapheneOS/hardened_malloc
- F\*: https://github.com/FStarLang/FStar
- Steel: https://github.com/FStarLang/steel
- KaRaMeL: https://github.com/FStarLang/karamel
- mimalloc-bench: https://github.com/daanx/mimalloc-bench
- NixOS: https://github.com/NixOS/nixpkgs
- [...]

## Authors

Antonin Reitz antonin.reitz@inria.fr
Aymeric Fromherz aymeric.fromherz@inria.fr
Jonathan Protzenko protz@microsoft.com

