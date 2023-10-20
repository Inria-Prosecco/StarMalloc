#include <stdlib.h>
#include <stdatomic.h>

#include "krmlinit.h"
//TODO: mark Config_nb_arenas as const (correctness + performance)
//#include "Config.h"
#include "StarMalloc.h"
#include "internal/StarMalloc.h"
#include "fatal_error.h"

//TODO: remove, mark Config_nb_arenas as const (correctness + performance)
#define N_ARENAS 4

__attribute__((tls_model("initial-exec")))
static _Thread_local unsigned thread_arena = N_ARENAS;
static atomic_uint thread_arena_counter = 0;

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

// returned pointer not null => (
//   - 16-bytes aligned
//   - at least of the requested size
// )
void* malloc(size_t size) {
  unsigned arena = init();
  return StarMalloc_malloc(arena, size);
}

// returned pointer not null => (
//   - 16-bytes aligned
//   - at least of the requested size (nb_elem * size_elem)
//   - filled with zeroes for subarray corresponding to the requested size
// )
void* calloc(size_t nb_elem, size_t size_elem) {
  unsigned arena = init();
  return StarMalloc_calloc(arena, nb_elem, size_elem);
}

// [...]
void* realloc(void* ptr, size_t new_size) {
  unsigned arena = init();
  return StarMalloc_realloc(arena, ptr, new_size);
}

// noop if ptr is null
// deallocates previously allocated memory by (malloc / ...)
// UAF + DF = undefined
// TODO: ensure it stops the execution when the deallocation process fails
void free(void *ptr) {
  // use enforce_init
  unsigned arena = init();
  bool b = StarMalloc_free(ptr);
  //if (! b) {
  //  printf("free ptr: %p\n", ptr);
  //  fatal_error(...)
  //}
  return;
}

// returned value is the number of usable bytes
// in the block pointed to by ptr,
// a pointer to a block of memory allocated by (malloc / ...)
size_t malloc_usable_size(void* ptr) {
  // not needed for correctness, but way faster
  //if (ptr == NULL) {
  //  return 0;
  //}
  // use enforce_init
  init();
  return StarMalloc_getsize(ptr);
}

//aligned_alloc, posix_memalign, memalign
void* aligned_alloc(size_t alignment, size_t size) {
  unsigned arena = init();
  return StarMalloc_aligned_alloc(arena, alignment, size);
}

//TODO: refine this, free_sized is part of C23
void free_sized(void* ptr, size_t size) {
  free(ptr);
}

//TODO: metaprogrammation like aligned_alloc
int posix_memalign(void **memptr, size_t alignment, size_t size) {
  fatal_error ("posix_memalign not yet implemented");
  return 0;
}
//TODO: metaprogrammation like aligned_alloc
void *memalign(size_t alignment, size_t size) {
  fatal_error ("memalign not yet implemented");
  return NULL;
}

// TODO: wrapper using large_alloc
void *valloc(size_t size) {
  fatal_error ("valloc not yet implemented");
  return NULL;
}
// TODO: wrapper using large_alloc
void *pvalloc(size_t size) {
  fatal_error ("pvalloc not yet implemented");
  return NULL;
}

void cfree(void* ptr) {
  fatal_error ("cfree is not implemented: removed since glibc 2.26");
}

//later on
//TODO: C++ stubs
