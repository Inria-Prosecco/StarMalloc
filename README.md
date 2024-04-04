# StarMalloc

A verified security-oriented general-purpose userspace memory allocator,
that can be used as a drop-in replacement for the libc allocator.
It is heavily inspired from [hardened\_malloc](https://github.com/GrapheneOS/hardened_malloc)'s design.

## Tested environments

As of 2024-02-05, Debian stable and current Arch Linux have been successfully tested.
That is, StarMalloc has been successfully tested on the [mimalloc-bench](https://github.com/daanx/mimalloc-bench) benchmark suite, so that its properties can be compared with many other allocators.
When building Firefox with appropriate flags (`--disable-jemalloc`), StarMalloc successfully replaces the shipped memory allocator.
Note: it can be necessary to set the `sysctl` `vm.max_map_count` to a higher than default value (e.g. 1048576 instead of 65536), as the guard pages security mechanism can lead to a large number of mappings.

## Performance

TODO

## Build

### Build process

Verifying StarMalloc and extracting C code from scratch requires dedicated software, that is: `z3` 4.8.5, and up-to-date versions of [FStar](https://github.com/FStarLang/FStar), [Steel](https://github.com/FStarLang/steel), [KaRaMeL](https://github.com/FStarLang/karamel),
with the addition of a C compiler (`clang` or `gcc`).

It is also possible to build StarMalloc as dynamic library only thanks to a C compiler, when relying on pre-extracted C files.

### Light build (using extracted C code)

`make light` will produce `out/starmalloc.so` out of pre-extracted C files (`dist/` directory).
StarMalloc can then be used this way: `LD_PRELOAD=out/starmalloc.so <program>`.
Note: some programs (e.g. Firefox or Chromium) use shipped allocators instead of the system (or environment) allocator.

### Verification build (verifying and extracting from scratch)

Requirements:
- `z3-4.8.5` is in the `$PATH`,
- `FSTAR_HOME` environment variable is set to F\* installation path,
- `STEEL_HOME` environment variable is set to Steel installation path,
- `KRML_HOME` environment variable is set to KaRaMeL installation path,
- a C compiler is in the `$PATH`: `clang` or `gcc`.

Steps with corresponding Makefile build targets:
- `verify`: verification phase of F\*+Steel files, producing `obj/*.checked` files;
- `extract`: extraction phase of F\*+Steel files, producing `obj/*.krml` files then `dist/` C files;
- `lib`: produces `out/starmalloc.so`.

Note: `make lib -j 4` requires roughly 16GB of RAM. zRAM and swap can of course be used to alleviate this hardware requirement.

tl;dr:
- `make lib -j $CORES` produces `out/*.so` files;
- `OTHERFLAGS="--admit_smt_queries true" make lib -j $CORES` allows one to skip most of the verification, e.g. in the case where SMT queries would fail.

### Complete build (verification build + preparing benchmarks)

`bash setup-all.sh`:
- build StarMalloc,
- clone mimalloc-bench inside `extern/mimalloc-bench`,
- build all of mimalloc-bench allocators + benches,
- install StarMalloc within mimalloc-bench dir (`extern/mimalloc-bench/extern/st`),
- tweak mimalloc-bench (ensuring all of the benches can be run by default).

As an exemple, to bench StarMalloc (`st`) against the system allocator (`sys`) and hardened\_malloc (`hm`) on all benches (`allt`), the following can then be used.
```
cd extern/mimalloc-bench/out/bench
bash ../../bench.sh sys hm st allt
```

All mimalloc-bench benchmarks should currently be working with StarMalloc. A Firefox build with the additional `--disable-jemalloc` flag allows one to test it when relying on StarMalloc with `LD_PRELOAD=out/starmalloc.so firefox`.
Firefox benchmarks such as JetStream2 have been successfully tested with StarMalloc.

## What does "verified" mean here? What are the properties of the allocator?

Verified means here that some functional correctness properties of the allocator have been proven to hold, in any supported configuration of the allocator (security mechanisms, number of arenas, ...):
- `malloc` returns `NULL` or an array of at least the requested size;
- `malloc` returns `NULL` or a 16-bytes aligned array, `aligned_alloc` returns `NULL` or an array aligned as requested
(caveat: no alignment larger than 4096 bytes is currently supported);
- `realloc(old_ptr, new_size)` returns `NULL` or, if `old_ptr` is different from the `NULL` pointer, an array in which the `min(old_size, new_size)` first bytes of `old_ptr` have been copied.

To lay the emphasis on this: no security property is formally proven, no security model is formally established, even though we would like to tackle this challenge in future work.

Other properties hold even though there are not formally proven:
- as it is developed using Steel, a concurrent separation logic (CSL) for F\*, StarMalloc is memory-safe;
- thanks to the use of a specific wrapper `with_lock` (TODO: merge) instead of manipulating mutexes manually, StarMalloc is deadlock-free.
Also, other common conventions are respected by StarMalloc, for example, allocation size is limited to `PTRDIFF_MAX` to avoid undefined behaviour on the end user side when comparing pointers pointing to parts of a same allocation.

The verified functional correctness properties are proven to be correct using F\*, Steel, the extraction using KaRaMeL is not.
Moreover, even though most of the resulting C code is extracted code, a small part of unverified C code remains.
It consists of:
- a C low-level initialization (with Thread Local Storage) that is based on hardened\_malloc's init, relies on C11 atomics to avoid race conditiions, quite short and hence reasonably auditable (this code also has to set a pthread\_atfork hook to ensure correct behaviour with respect to the fork system call);
- C glue between modelised OS system calls (mmap, munmap, madvise) and low-level utils (__builtin_mul_overflow, __builtin_ctzll, memcpy, memset (uintptr_t) casts).

## Structure of the allocator

### Allocation process (malloc case)

malloc(size)
- [0] size <= PAGE\_SIZE (this bound has to be adjusted when using canaries), if so goto 10., otherwise goto 20.
- [10] within the arena corresponding to the thread, find corresponding size class
- [11] find a slab with at least one free slot
  * look for partial slabs
  * look for empty slabs
  * if there is none in these two categories, add slabs to the empty slabs list from the so-far unused memory space
- [12] find free slot position
- [13] update metadata, return corresponding pointer
- [20] ptr = mmap(size), check result
- [21] insert (ptr, size) into the AVL tree containing metadata
- [22] return corresponding pointer

### Deallocation process (free case)

free(ptr)
- [0] is the pointer within the very large contiguous memory regions containing adjacent arenas, which are containg adjacent size classes? if so goto 10., otherwise goto 20.
- [10] using pointer difference between ptr and the start of the slab region, find the corresponding arena
- [11] using pointer difference between ptr and the start of the arena, find the corresponding size class
- [12] using pointer difference between ptr and the start of the size class, find the corresponding slab
- [13] using pointer difference between ptr and the start of the slab, find the corresponding slot
- [14] check using slot metadata whether ptr corresponds to an actual allocation, if so goto 15., otherwise fail
- [15] update metadata
- [20] check whether corresponds to an actual allocation by looking for ptr in the metadata map (which is an AVL tree); if so goto 21., otherwise fail
- [21] corresponding size is now known; remove (ptr, size) from the map

## Security mechanisms of the allocator

- size classes + arenas
- out-of-band metadata
- no free lists/no size class cache
- zeroing on free
- zeroing check on allocation
- guard pages
- quarantine
- canaries

## Provided symbols

The following symbols are provided:
1. as part of C standard library: malloc, calloc, realloc, free, aligned_alloc (C11), free_sized (C23, to be refined), free_aligned_sized (C23, to be refined);
2. other symbols: posix_memalign (POSIX), malloc_usable_size (GNU), memalign (seems to be quite standard).

pvalloc and valloc are not yet provided for compatibility purpose, cfree is not yet provided as a fatal error stub. (Note: The cfree has been removed since glibc 2.26, current Debian oldoldstable glibc = 2.28, as of 2024-02-05.)

## External repositories

- hardened\_malloc: https://github.com/GrapheneOS/hardened_malloc
- F\*: https://github.com/FStarLang/FStar
- Steel: https://github.com/FStarLang/steel
- KaRaMeL: https://github.com/FStarLang/karamel
- mimalloc-bench: https://github.com/daanx/mimalloc-bench
- NixOS: https://github.com/NixOS/nixpkgs
- [...]

## Authors

Antonin Reitz `antonin.reitz@inria.fr`
Aymeric Fromherz `aymeric.fromherz@inria.fr`
Jonathan Protzenko `protz@microsoft.com`
