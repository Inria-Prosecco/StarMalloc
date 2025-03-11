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

static void init(void) {
  static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
  pthread_mutex_lock(&m);
  if (is_init()) {
    pthread_mutex_unlock(&m);
    return;
  }
  real_malloc = dlsym(RTLD_NEXT, "malloc");
  real_free = dlsym(RTLD_NEXT, "free");
  //log_ipt((uint64_t) real_malloc);
  //log_ipt((uint64_t) real_free);
  uint64_t x = -1;
  //log_ipt(x);

  atomic_store_explicit(&check_init, true, memory_order_release);
  pthread_mutex_unlock(&m);
  //if (NULL == real_malloc) {
  //  fprintf(stderr, "Error in `dlsym`: %s\n", dlerror());
  //}
}


void* malloc(size_t size) {
  if(! is_init()) {
    init();
  }

  void *p = NULL;
  log_ipt((uint64_t) 1UL);
  log_ipt((uint64_t) size);
  p = real_malloc(size);
  log_ipt((uint64_t) p);
  return p;
}

void free(void* ptr) {
  if(! is_init()) {
    init();
  }
  uint64_t ptr_as_u64 = (uint64_t) ((uintptr_t) ptr);
  log_ipt((uint64_t) 2UL);
  log_ipt(ptr_as_u64);
  real_free(ptr);
}
