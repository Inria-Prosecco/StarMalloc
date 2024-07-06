# Artifact Overview

## Introduction

This artifact is in support of OOPSLA'24 paper 590, StarMalloc: Verifying a Modern, Hardened Memory Allocator.

There are two independant parts in this artifact.
1. StarMalloc source is included as a proof artifact in order to support the paper's formal verification claims.
2. mimalloc-bench benchmarks are included in order to support the paper's experimental results.

This artifact is shipped as a VM, repurposing the ICFP 2024 artifact VM. The only VM tweaks are the following in the VM initialization script `script.sh`.
- By default, all host's cores should be used: otherwise, some benchmarks would be meaningless.
- By default, 16GiB is mapped to the VM instead of 4GiB. Please note that in case of insufficient RAM on the host, this setting can be tweaked and/or zRAM can be used.

Note: Firefox specific build is not included, as the VM does not include a graphical environment.

### List of the claims

1. Proof artifact
F\* is used as a proof assistant. More precisely, Steel is used in combination with F\*: it is a concurrent separation logic (CSL) embedded within F\*.
There are two sorts of files: `*.fst` files and `*.fsti` files. The latter are interface files used to define clear abstraction boundaries between modules.
As StarMalloc is written using a CSL, it is memory-safe.

Following the paper apparition order:
+ Allocator APIs (section 3.1): Main theorem of (functional) correctness, present in file `src/StarMalloc.fst`
+ `starseq` combinator and lemmas (section 3.2): `lib_misc/SteelStarSeqUtils.fsti`
+ `arraylist` datastructure (section 3.3): `lib_list/ArrayListGen.fsti`, named `varraylist` in code`
+ `starseq` is used for both slots and slabs (section 3.4):
  - slabs_sl, in `src/SlabsCommon.fsti`: `left_vprop` describing the state of the memory currently used, relies on `left_vprop2`, itself relying on `starseq`
  - slots_sl, in `src/SlotsAlloc.fst`: `slab_vprop` describing the state of one slab (and thus many slots), relies on `slab_vprop_aux`, itself relying on `starseq`
+ Reusing the Slab Allocator (section 3.4): `src/LargeAlloc.fst`, e.g. the `trees_malloc2` function reusing the slab allocator `SizeClass.allocate_size_class` function
+ Configurability (section 3.5): Generic size classes in `src/Config.fsti`, many configuration switches behind the interface

StarMalloc is already verified and extracted as part of the VM.
To reverify it from scratch: `make clean && make lib`. (`make lib -j 1` for systems with <=8 GiB of RAM, `make lib -j 3` for systems with <=16GiB of RAM, `make lib -j` otherwise).
Proofs based on SMT can be unstable, in case of error please try the following command: `OTHERFLAGS="--z3rlimit_factor 4" make lib` to raise timeouts.
Total time expected: ~30 minutes on a modern machine with 16GiB of RAM.

2. Experimental evaluation on mimalloc-bench
mimalloc-bench is an already existing memory allocator benchmarking suite.
The artifact VM contains a prebuilt version of mimalloc-bench.
We observe variance across machines, however the trends should be similar
Running all of the allocators on all of the benchmarks can be especially slow, requiring several hours outside of the VM.
A lighter version can be run using `bash ../../bench.sh sys hm st allt`, thus comparing 
the system allocator (glibc allocator, `sys`), hardened\_malloc (`hm`), and StarMalloc (`st`) on all of the benchmarks.

3. Firefox: as noted previously, a prebuilt version of Firefox with the required tweak (adding the `--disable-jemalloc` compilation flag) is not part of the artifact. Indeed, no graphical environment is part of the VM: as ICFP'24 submission guidelines put it, "Graphical environments in VMs are sometimes slow and unstable.". It has successfully been tested on Debian and Arch Linux with different Firefox versions throughout StarMalloc development.

## Hardware Dependencies

Only `x86_64-linux` environments have been tested: while other architectures could likely be used with QEMU, this could alter benchmarks.
Also, while 8/16GiB of RAM should be enough, 32GiB is recommended to speed up verification time.

## Getting Started Guide

We provide a full installed VM and sources.

- QEMU should be installed.
- Leveraging the ICFP 2024 artifact VM: `./start.sh` will start the VM.
- Once started, one can use SSH to connect to the VM: `ssh -p 5555 artifact@localhost`, the password is `password`.
- Structure of the artifact in `/home/artifact`:
  + verification software (F\*, Steel, KaRaMeL) is installed in `setup_verif`.
  + StarMalloc is installed in `starmalloc`.
  + mimalloc-bench is installed in `mimalloc-bench`.
- To assess whether everything should work as expected in a very short time: `pushd starmalloc && make test-artifact && popd` should not display any error.
- Internet access should not be required.

## Step by Step Instructins

### Proof artifact

`cd ~/starMalloc`

1. Proofs can be reverified: `make clean && make lib`. This can take quite some time, `make lib -j 1` should work on 8GiB systems, `make lib -j 3` should work on 16GiB systems and `make lib -j` on 32GiB systems.
2. Checking for admitted proofs:
  + check for `admit` keyword in `*.fst{,i}` files: there should not be any occurrence in proofs
  + same for `assume keyword`: only `assume val` declarations should contain the `assume` keyword in proofs, as these declarations model C code (such as syscalls)
3. Axioms with corresponding documentation are in the following files:
  + `src/ExternUtils.fst`: various compiler builtins/basic C code
  + `src/Mman.fst` and `src/Mman2.fst`: memory management
  + `src/MemoryTrap.fst`: memory permissions (guard pages and quarantine security mechanisms)
  + `src/ArrayAlignment.fst`: array alignment (e.g. with respect to pages)
  + `src/FatalError.fst`: context-specific wrappers of the C `fatal_error` function (see `c/fatal_error.{c,h}`)
  + `lib_avl_mono/Impl.Trees.Cast.M`: mainly casts axiomatization, required to reuse the slab allocator for the AVL tree's nodes used as large allocations metadata
4. Once verification is done, the extracted C code can be found in `dist/`. In its initial state, the VM includes the generated code.

### Benchmarks artifact

The instructions to reproduce the experimental evaluation (Section 6) are as follows.

`cd ~/mimalloc-bench`

- (if StarMalloc has been tweaked and rebuilt, `cp ~/starmalloc/out/starmalloc.so extern/st/` to benchmark the correct version)
- `cd out/bench`
- `bash ../../bench.sh sys hm st allt` to bench the system allocator, hardened_malloc and StarMalloc on all benchmarks
- Results should be copied into `benchres.csv`, which can be read in the following manner.
  + test/benchmark
  + allocator
  + time
  + RSS (resident set size)
  + time (user)
  + time (sys)
  + page faults
  + page reclaims
- Results in the paper have been normalized w.r.t. hardened_malloc.
- `bash ../../bench.sh -h` can be used to select other allocators and/or benchmarks
- (Not recommended) `bash ../../bench.sh alla allt` runs all allocators on all benchmarks, corresponding to the table in the appendix.

## Reusability Guide
StarMalloc and corresponding benches have been tested on recent versions of Arch Linux, Debian unstable and (at least partially) NixOS.

Components of the allocator should be reusable to build other allocators: the slab allocator is reused as part of the large allocator (AVL tree node allocation).
Configurability of the allocator (many options in `src/Config.fst` and `src/Config.fsti`) should help to reuse some security mechanisms or specific features in other contexts. The many librairies (bitmaps, AVL tree, arraylist, `starseq` combinator) could be used as building blocks for other verified low-level programming projects.

Finally, relying on the modular development organisation, it should be reasonable to add additional features such as security mechanisms, Android support or 16K page support.
