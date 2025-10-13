# TranscrIPT

A hardware-based heap tracing prototype, partly inspired
by [logalloc](https://searchfox.org/firefox-main/source/memory/replace/logalloc/README).

## Requirements

Using it requires support for Intel Processor Tracing and the ptwrite instruction;
this can be checked using the following command, result should be 1.
```
cat /sys/devices/intel_pt/caps/ptwrite
```
Otherwise, perf supports emulated ptwrite, see `man perf-intel-pt`.

## Howto

Compiling `hwlogmalloc.c` into `hwlogmalloc.so` can be done using the following.
```
gcc -O3 -fPIC -shared -pthread -lpthread -std=c17 hwlogmalloc.c -o hwlogmalloc.so
```

Then, one can trace all memory management operations of a userspace application using the following.
```
perf record -e intel_pt/ptw=1,fup_on_ptw=0,branch=0/u -o /tmp/data.txt -- env LD_PRELOAD=./hwlogmalloc.so [...]
```
Please note that the path to `hwlogmalloc.so` may need to be adjusted. Also, by default,
`/tmp/data.txt` is used so that data is written in RAM to limit memory bandwidth issues
that can incur overhead, assuming `/tmp/` is a large in-RAM filesystem.

Using `LD_PRELOAD=./hwlogmalloc.so:./custom-malloc.so`, one can specify that the memory allocator
that should be used is `custom-malloc.so`: `hwlogmalloc.so` will redirect memory management
calls to it using some linking trick.

At this point, collected data under the form of an IPT trace can be decoded and compressed
on-the-fly using 
```
perf script --itrace=we -i=/tmp/data.txt | xz -e &> compressed-data.txt
```

Finally, the result can be parsed using the `parsing.py` script, that currently is fairly basic
and only demonstrates that it is doable to decode collected traces using the outlined method.
```
python parsing.py compressed-data.txt
```

A simple example of a malloc/free loop that can be used as a small test is provided in `test.c`.

## Some notes to improve reproducibility

All of the following may help.

- Using root instead of unprivileged user (related to process priority/niceness stuff?)
- Using a ramfs instead of writing everything on disk
- Hardware with a large amount of RAM for long processes
- Disabling TNT packets on hardware supporting it
