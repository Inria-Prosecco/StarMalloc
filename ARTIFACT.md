# Artifact Overview

## Introduction

The goal of this artifact is twofold:
1. following the proof artifact guidelines [1], supporting the stated formal verification claims in the paper ;
2. by allowing one to compare StarMalloc with other memory allocators using mimalloc-bench [2] and a specific version of Firefox [3], supporting the experimental results in the paper ;

### List of the claims

1. Proof artifact claims
TODO

2. Experimental results
TODO

## Hardware Dependencies
A `x86_64-linux` environment is required.
Experimental results were obtained on a Dell Precision 3581 featuring an Intel i5-13600H with 32GiB of RAM on Linux 6.6.
1. Proof verification should not require more than (TODO) of RAM with 1 job, and at most (TODO) of RAM using as much jobs as possible.
2. Experimental results should not require more than (TODO) of RAM.
  + mimalloc-bench allocators and benchmarks are already compiled, running benches should not require more than (TODO) of RAM
  + a specific version of Firefox (any standard build with the additional `--disable-jemalloc` flag) is already compiled, running benches should not require more than (TODO) of RAM

## Getting Started Guide
TODO: VM setup requirements, use the "artifact" user with no password

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


