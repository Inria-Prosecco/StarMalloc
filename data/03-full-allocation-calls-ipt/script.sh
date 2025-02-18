#!/bin/env bash
# example: gcc test.c && bash script.sh ./a.out
gcc -O0 -fPIC -shared -pthread -lpthread -std=c17 hwlogmalloc.c -o malloc.so
#perf record -e intel_pt/cyc=1,ptw/u -- ...
#perf record -e intel_pt/cyc=1,ptw,fup_on_ptw/u -- ...
perf record -e intel_pt/branch=0,ptw,fup_on_ptw/u -- env LD_PRELOAD=./malloc.so $@
perf script --itrace=we -F+flags
#perf script --itrace=ixweypb -F+flags
#perf script --itrace=i1t -F +srcline -F +insn | xed -F insn: -I -64 | less
