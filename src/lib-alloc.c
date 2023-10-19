#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdatomic.h>
#include "krmlinit.h"
#include "Config.h"
#include "StarMalloc.h"
#include "internal/StarMalloc.h"

//TODO: remove, mark Config as const (correctness + performance)
#define N_ARENAS 4

__attribute__((tls_model("initial-exec")))
static _Thread_local unsigned thread_arena = N_ARENAS;
static atomic_uint thread_arena_counter = 0;

uint8_t* StarMalloc_memcpy_u8(uint8_t* dest, uint8_t* src, size_t n) {
  return (uint8_t*) memcpy((void*) dest, (void*) src, n);
}

uint8_t* StarMalloc_memset_u8(uint8_t* dest, uint8_t v, size_t n) {
  return (uint8_t*) memset((void*) dest, v, n);
}

static void* _Atomic slab_region_ptr;

// hm-alike initialization
static inline bool is_init(void) {
  void* ptr = atomic_load_explicit(&slab_region_ptr, memory_order_acquire);
  return ptr != NULL;
}

// hm-alike
static void init_slow_path(void) {
  static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
  pthread_mutex_lock(&m);
  if (is_init()) {
    pthread_mutex_unlock(&m);
    return;
  }
  krmlinit_globals();
  atomic_store_explicit(&slab_region_ptr, Main_Meta_sc_all.slab_region, memory_order_release);
  pthread_mutex_unlock(&m);
  // TODO: pthread_atfork
}

// hm-alike
static inline unsigned init(void) {
  unsigned arena = thread_arena;
  if (arena < N_ARENAS) {
    return arena;
  }
  thread_arena = arena = thread_arena_counter++ % N_ARENAS;
  if (!is_init ()) {
    init_slow_path();
  }
  return arena;
}

void* malloc(size_t size) {
  unsigned arena = init();
  return StarMalloc_malloc(arena, size);
}

void* aligned_alloc(size_t alignment, size_t size) {
  unsigned arena = init();
  return StarMalloc_aligned_alloc(arena, alignment, size);
}

void* calloc(size_t nb_elem, size_t size_elem) {
  unsigned arena = init();
  return StarMalloc_calloc(arena, nb_elem, size_elem);
}

void* realloc(void* ptr, size_t new_size) {
  unsigned arena = init();
  return StarMalloc_realloc(arena, ptr, new_size);
}

void free(void *ptr) {
  // use enforce_init
  unsigned arena = init();
  bool b = StarMalloc_free(ptr);
  //if (! b) {
  //  printf("free ptr: %p\n", ptr);
  //  assert (b);
  //}
  return;
}

size_t malloc_usable_size(void* ptr) {
  // not needed for correctness, but way faster
  if (ptr == NULL) {
    return 0;
  }
  // use enforce_init
  init();
  return StarMalloc_getsize(ptr);
}
