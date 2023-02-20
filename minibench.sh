#!/bin/env sh
make lib
make hardened_lib
gcc bench/test-alloc2.c
echo
echo stdlib malloc
time ./a.out
echo starmalloc
time LD_PRELOAD=bench/starmalloc.so ./a.out
echo hardened starmalloc
time LD_PRELOAD=bench/h_starmalloc.so ./a.out
echo hardened_malloc
time LD_PRELOAD=hardened_malloc/out/libhardened_malloc.so ./a.out
