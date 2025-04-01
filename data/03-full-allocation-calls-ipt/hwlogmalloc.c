#define _GNU_SOURCE

#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdbool.h>

void log_ipt(uint64_t x)
__attribute__((noinline, noipa));
// this segfaults when the function is called as part of a shared library, interesting
//__attribute__((externally_visible, noipa, no_instrument_function, naked));

void log_ipt(uint64_t x) {
  __asm__ volatile("ptwriteq %rdi");
}

static bool _Atomic check_init = false;
static void* (*real_malloc)(size_t)=NULL;
static void (*real_free)(void*)=NULL;

static inline bool is_init(void) {
  bool b = atomic_load_explicit(&check_init, memory_order_acquire);
  return b;
}

// invariants to be preserved when adding other functions (e.g. calloc, realloc, etc)
// 1. before each allocation/deallocation primitive call, log_ipt(magic_value)
// 2. this magic value must be only used by the considered allocation/deallocation primitive
// 3. there must be one log_ipt call right after the considered allocation/deallocation primitive

// considered data:
// - full allocation/deallocation graph, with data on address reuse + allocation/deallocation arguments
// - execution time of each allocation/deallocation primitive depending on the arguments (e.g. the requested size)

static void init(void) {
  static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
  pthread_mutex_lock(&m);
  if (is_init()) {
    pthread_mutex_unlock(&m);
    return;
  }
  real_malloc = dlsym(RTLD_NEXT, "malloc");
  real_free = dlsym(RTLD_NEXT, "free");

  atomic_store_explicit(&check_init, true, memory_order_release);
  pthread_mutex_unlock(&m);
}


void* malloc(size_t size) {
  if(! is_init()) {
    init();
  }
  // execution start
  log_ipt((uint64_t) (-1L));
  log_ipt((uint64_t) size);
  void* p = real_malloc(size);
  // execution end
  log_ipt((uint64_t) p);
  return p;
}

void free(void* ptr) {
  if(! is_init()) {
    init();
  }
  // execution start
  log_ipt((uint64_t) (-2L));
  uint64_t ptr_as_u64 = (uint64_t) ((uintptr_t) ptr);
  real_free(ptr);
  // execution end
  log_ipt(ptr_as_u64);
}

