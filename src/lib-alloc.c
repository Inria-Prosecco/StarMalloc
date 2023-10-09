#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdatomic.h>
#include "krmlinit.h"
#include "Config.h"
#include "StarMalloc.h"

#define N_ARENA 4

static uint32_t init_status = 0UL;
static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;

__attribute__((tls_model("initial-exec")))
static _Thread_local unsigned thread_arena = N_ARENA;
static atomic_uint thread_arena_counter = 0;

uint8_t* StarMalloc_memcpy_u8(uint8_t* dest, uint8_t* src, size_t n) {
  return (uint8_t*) memcpy((void*) dest, (void*) src, n);
}

uint8_t* StarMalloc_memset_u8(uint8_t* dest, uint8_t v, size_t n) {
  return (uint8_t*) memset((void*) dest, v, n);
}

void* malloc(size_t size) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  if (thread_arena == N_ARENA) {
    thread_arena = thread_arena_counter++ % N_ARENA;
  }
  return StarMalloc_malloc(thread_arena, size);
}

void* aligned_alloc(size_t alignment, size_t size) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  if (thread_arena == N_ARENA) {
    thread_arena = thread_arena_counter++ % N_ARENA;
  }
  return StarMalloc_aligned_alloc(thread_arena, alignment, size);
}

void free(void *ptr) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  //printf("free ptr: %p\n", ptr);
  bool b = StarMalloc_free(ptr);
  //printf("  result: %b\n");
  return;
}

void* realloc(void* ptr, size_t new_size) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  if (thread_arena == N_ARENA) {
    thread_arena = thread_arena_counter++ % N_ARENA;
  }
  //printf("ptr: %p, new_size: %lu\n", ptr, new_size);
  void* new_ptr = StarMalloc_realloc(thread_arena, ptr, new_size);
  //printf("  new_ptr: %p\n", new_ptr);
  return new_ptr;
}

void* calloc(size_t nb_elem, size_t size_elem) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  if (thread_arena == N_ARENA) {
    thread_arena = thread_arena_counter++ % N_ARENA;
  }
  uint8_t* ptr = StarMalloc_calloc(thread_arena, nb_elem, size_elem);
  return (void*) ptr;
}

size_t malloc_usable_size(void* ptr) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  return StarMalloc_getsize(ptr);
}
