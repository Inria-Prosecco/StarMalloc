# StarMalloc

A verified security-oriented general-purpose userspace memory allocator,
that can be used as a drop-in replacement for the libc allocator.
It is heavily inspired from hardened\_malloc's design.

The following symbols are/will be/will not be provided: except when explicitly mentioned, symbols are provided.
1. as part of C standard library
- malloc
- calloc
- realloc
- free
- aligned\_alloc (C11, TODO: check current implem)
- free\_sized (C23, TODO: refine)
- free\_aligned\_sized (C23, TODO: provide it)

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
- tweaks mimalloc-bench.

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

[...]

### WIP: Firefox

[...]

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

## CI

3 sorts of jobs:
1. Basic: on every push, try to build the project.
2. (WIP) Improved: on every push, test the project on all mimalloc-bench benches.
3. (WIP) PR development model, refresh dist/: track dist/ under version control, no PR should be merged without the build succeeding and dist/ being (automatically?) refreshed.
4. (WIP) nightly: every day, build StarMalloc main branch using bleeding-edge F\*, Steel, KaRaMeL, and compare on the same commit using the flake.lock dependencies versions.

## TODO
- remove last assume (t\_of casts...)
- replace last sladmits with proper fatal error stubs
- pthread\_atfork hook
- initial large memory mappings should have `PROT_NONE` permissions
- debug flag/distinct debug targets (remove -g as default compilation flag)
- compilation flags
  - limit visible symbols
  - -fhardened flag: FORTIFY\_SOURCE, stack-clash protection, etc
- use hacl-star libmemzero
- C defensive programming:
  - more memory-related errno checks wrt ENOMEM
  - limit allocation size to `PTRDIFF_MAX` (glibc behaviour)
  - calloc: remove overflow risk
  - fatal\_error if StarMalloc\_free fails
- C++ stubs
- remaining warnings using -Wall
  - -Wlogical-op-parentheses: krml fix?
  - -Wc++17-extensions (static\_assert with no message)
  - -Wunused
    - src/lib-alloc.c, free: replace init with enforce\_init
    - src/lib-alloc.c, free: StarMalloc\_free returned value
- PRs:
  - KaRaMeL: test for `size_t`
  - mimalloc-bench: install all allocators and benches using Nix
- CI: [...]
- benches
  - fix mimalloc-bench/perf
    - rptest: missing memalign symbol
    - lua: bad-alloc, missing symbol?
    - rocksdb: missing posix\_memalign symbol
    - fix sh6bench/sh8bench exit statuses(?)
  - fix mimalloc-bench/security
  - large application: Firefox?
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
[...]

