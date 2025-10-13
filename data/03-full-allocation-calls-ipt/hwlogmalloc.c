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
// 1. the header must be logged before each allocation/deallocation primitive call
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
  //real_calloc = dlsym(RTLD_NEXT, "calloc");

  atomic_store_explicit(&check_init, true, memory_order_release);
  pthread_mutex_unlock(&m);
}

const bool use_ipt = true;

uint64_t encode_malloc_p1 (size_t size) {
  uint64_t v1 = ((uint64_t) (1UL << 63)) | ((uint64_t) size);
  return v1;
}
uint64_t encode_malloc_p2 (void* ptr) {
  uint64_t ptr_as_u64 = (uint64_t) ((uintptr_t) ptr);
  return ptr_as_u64;
}
uint64_t encode_free_p1 (){
  uint64_t v1 = (uint64_t) (1UL << 62);
  return v1;
}
uint64_t encode_free_p2 (void* ptr){
  uint64_t ptr_as_u64 = (uint64_t) ((uintptr_t) ptr);
  return ptr_as_u64;
}

void* malloc(size_t size) {
  if(! is_init()) {
    init();
  }
  // execution start
  if (use_ipt) {
    log_ipt(encode_malloc_p1(size));
  }
  void* ptr = real_malloc(size);
  // execution end
  if (use_ipt) {
    log_ipt(encode_malloc_p2(ptr));
  }
  return ptr;
}

void free(void* ptr) {
  if(! is_init()) {
    init();
  }
  // execution start
  if (use_ipt) {
    log_ipt(encode_free_p1());
  }
  real_free(ptr);
  // execution end
  if (use_ipt) {
    log_ipt(encode_free_p2(ptr));
  }
}

//void* calloc(size_t size1, size_t size2) {
//  if(! is_init()) {
//    init();
//  }
//  // execution start
//  uint64_t v1 = (1UL << 63) | (1UL << 62) | ((uint64_t) size1 << 30UL) | ((uint64_t) size2);
//  log_ipt(v1);
//  uint64_t ptr_as_u64 = (uint64_t) ((uintptr_t) ptr);
//  void* p = real_calloc(size1, size2);
//  // execution end
//  log_ipt((uint64_t) p);
//  return p;
//}
//
//void* realloc(void* ptr, size_t new_size) {
//
//  if(! is_init()) {
//    init();
//  }
//
//}
//
//
//

