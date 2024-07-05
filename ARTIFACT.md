# Artifact Overview

## Introduction

This artifact is in support of OOPSLA 24 paper TODO

There are two independant parts in this artifact.
1. StarMalloc source is included as a proof artifact in order to support the paper's formal verification claims.
2. mimalloc-bench benchmarks are included in order to support the paper's experimental results.
3. TODO: Firefox?

This artifact is shipped as a VM, repurposing the ICFP 2024 artifact VM. The only VM tweak are the following in the VM initialization script:
- by default, all host's cores should be used: otherwise, some benchmarks would be meaningless;
- by default, 16GiB is mapped to the VM instead of 4GiB.(*)

(*) Please note that in case of insufficient RAM on the host, ZRAM can be used.

### List of the claims

Verified artifact, implemented in F\*-Steel
Experimental evaluation on mimalloc-bench
Integration with Firefox

1. Proof artifact claims
Quick presentation of F\*/CSL (fst/fsti files, Steel effect corresponds to the Steel framework with CSL guarantees)

+ Allocator APIs: Main theorem of correctness, present in file TODO
+ StarSeq combinator and lemmas -> Files/Folder
+ Using StarSeq -> Point to several uses
+ varraylist
+ Configurability (Section 3.5) -> Generic size classes in BLA, Config.fst

Reproducing claims: make TODO
Proofs based on SMT can be unstable, might need OTHERFLAGS="--z3rlimit_factor 4" to help on your machine
This reverifies proofs, and reruns extraction. Self-contained dist included
Total time expected : TODO

2. Run bla in mimalloc-bench, evaluated against ....
   We observe variance across machines, however the trends should be similar
   X especially slow, but you can run a lighter version omitting longer artifacts with X

3. Firefox TODO

---


1. Proof artifact claims
+ challenge 1: interaction with the OS
+ challenge 2: concurrency
+ challenge 3: configurability
+ challenge 4: non-local reasoning
+ challenge 5: efficient datastructure
+ challenge 6: iterating on verified implementatioN
TODO

+ val malloc -> StarMalloc
+ val dispath -> SlabsCommon
+ val starseq -> SteelStarSeqUtils
+ val slabs_sl ?
+ let slabs_sl ?
+ let is_list -> ALG

2. Experimental results
TODO

## Hardware Dependencies

Only `x86_64-linux` environments have been tested: while other architectures could likely be used with QEMU, this could alter benchmarks.
Also, while 16GiB of RAM should be enough, 32GiB is recommended to speed up verification time.

## Getting Started Guide

We provide both a fully installed VirtualBox and sources with a Nix script for StarMalloc

- QEMU should be installed.
- Leveraging the ICFP 2024 artifact VM: `./start.sh` will start the VM.
- Once started, one can use SSH to connect to the VM: `ssh -p 5555 artifact@localhost`, the password is `password`.
- Verification software is installed in `/home/artifact/setup_verif`.
- To assess whether everything should work as expected in a very short time: `make test-artifact` should not display any error.
- Internet access should be not be required.

TODO: Explain Nix and sources

## Step by Step Instructins

### Proof artifact

`cd ~/StarMalloc`

TODO: Do not claim, but present

Claims:
1. Proofs can be reverified: `make lib`. This can take quite some time, `make lib -j 1` should work on 8GiB systems, `make lib -j 3` should work on 16GiB systems and `make lib -j` on 32GiB systems.
2. Checking for admitted proofs:
  + `ag admit` should not yield any output, that is, no proof is admitted; TODO: there is output but irrelevant
  + `ag assume | grep -v "assume val"` should not yield any output, that is, no part of a proof is omitted, but some external functions are assumed to exist, e.g. syscalls.
3. Axioms with corresponding documentation are in the following files:
  + `src/Mman.fst`: memory-management axiomatization
  + TODO
4. Extracted files are up-to-date: once verification is done, `dist/` should still be up-to-date with respect to the git repository initial state. This can be checked using `git diff dist`.

### Benchmarks artifact


Claims:
1. StarMalloc i

`cd ~/S

## Getting Started Guide
Roughly two steps are required to check the artifact:
1. Proof artifact checks
2. Experimental results checks

## Step by Step Instructions
TODO

## Reusability Guide
StarMalloc and corresponding benches have been tested on recent versions of Arch Linux, Debian unstable and (partially) NixOS.

StarMalloc is a verified memory allocator that can be used as a drop-in replacement of the libc memory allocator, as the included proof artifact and various included benches should tend to indicate.
Furthermore, it is highly-configurable: the obtained security-oriented allocator (from the `dist/` C code) can be repurposed as a generic memory allocator by disabling security mechanisms.
Relying on the modular development organisation, it should be reasonable to add additional features such as security mechanisms or Android support.

Current main limitations may be the `x86_64-linux` requirement: there is planned work to adapt the allocator to MacOS and/or ARM environments, with a different page size (16K instead of currently-hardcoded 4K value).

## References

[1] https://proofartifacts.github.io/guidelines/index.html#guidelines-for-authors
[2] https://github.com/daanx/mimalloc-bench
[3] https://firefox-source-docs.mozilla.org/contributing/directory_structure.html or https://searchfox.org/mozilla-central/source

## Packaging references
- https://2024.splashcon.org/track/splash-2024-oopsla-artifacts#Call-for-Artifacts
- https://proofartifacts.github.io/guidelines/index.html#guidelines-for-authors
- https://icfp23.sigplan.org/track/icfp-2023-artifact-evaluation


