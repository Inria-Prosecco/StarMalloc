#include <stdlib.h>
#include <stdio.h>
#include <stdatomic.h>

#define DEBUG 1

#ifdef DEBUG
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>
#endif

#include "krmlinit.h"
#include "Config.h"
#include "StarMalloc.h"
#include "internal/StarMalloc.h"
#include "fatal_error.h"

__attribute__((tls_model("initial-exec")))
static _Thread_local unsigned thread_arena = CONFIG_NB_ARENAS;
static atomic_uint thread_arena_counter = 0;

static void* _Atomic slab_region_ptr;

#ifdef DEBUG
static int fd = 0;
static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
#endif

static void full_lock(void) {
  pthread_mutex_lock(&metadata.lock);
  for (size_t i = 0; i < CONFIG_NB_ARENAS; i++) {
    for (size_t j = 0; j < CONFIG_NB_SIZE_CLASSES; j++) {
      pthread_mutex_lock(&Main_Meta_sc_all.size_classes[i * CONFIG_NB_SIZE_CLASSES + j].lock);
    }
  }
}

static void full_unlock(void) {
  pthread_mutex_unlock(&metadata.lock);
  for (size_t i = 0; i < CONFIG_NB_ARENAS; i++) {
    for (size_t j = 0; j < CONFIG_NB_SIZE_CLASSES; j++) {
      pthread_mutex_unlock(&Main_Meta_sc_all.size_classes[i * CONFIG_NB_SIZE_CLASSES + j].lock);
    }
  }
}

static void post_fork_child(void) {
  size_t status = 0;
  status += pthread_mutex_init(&metadata.lock, NULL);
  for (size_t i = 0; i < CONFIG_NB_ARENAS; i++) {
    for (size_t j = 0; j < CONFIG_NB_SIZE_CLASSES; j++) {
      status += pthread_mutex_init(&Main_Meta_sc_all.size_classes[i * CONFIG_NB_SIZE_CLASSES + j].lock, NULL);
    }
  }
  if (status) {
    fatal_error("fork child: mutexes initialization failed");
  }
}

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
  #ifdef DEBUG
  fd = open("temp.txt", O_WRONLY | O_TRUNC | O_CREAT, 0640);
  if (fd == -1) {
    fatal_error("log file could not be opened");
    return;
  }
  #endif
  pthread_mutex_unlock(&m);
  if (pthread_atfork(full_lock, full_unlock, post_fork_child)) {
    fatal_error("pthread_atfork failed");
  }
}

// hm-alike
static inline unsigned init(void) {
  unsigned arena = thread_arena;
  if (arena < CONFIG_NB_ARENAS) {
    return arena;
  }
  thread_arena = arena = thread_arena_counter++ % CONFIG_NB_ARENAS;
  if (!is_init ()) {
    init_slow_path();
  }
  return arena;
}

static inline void write_msg(size_t id_function, size_t p1, size_t p2, void* ptr) {
  #ifdef DEBUG
  pthread_mutex_lock(&m);
  char buffer[1024] = { 0 };
  switch (id_function) {
    case 0:
      snprintf(buffer, sizeof(buffer), "malloc: %zu\n", p1);
      break;
    case 1:
      snprintf(buffer, sizeof(buffer), "free: %p\n", ptr);
      break;
    case 2:
      snprintf(buffer, sizeof(buffer), "aligned_alloc: %zu/%zu\n", p1, p2);
      break;
    case 3:
      snprintf(buffer, sizeof(buffer), "calloc: %zu/%zu\n", p1, p2);
      break;
    case 4:
      snprintf(buffer, sizeof(buffer), "realloc: %p/%zu\n", ptr, p1);
      break;
    default:
      pthread_mutex_unlock(&m);
      return;
  }
  write(fd, buffer, sizeof(buffer));
  pthread_mutex_unlock(&m);
  #endif
  return;
}

// returned pointer not null => (
//   - 16-bytes aligned
//   - at least of the requested size
// )
__attribute__((visibility("default")))
void* malloc(size_t size) {
  unsigned arena = init();
  write_msg(0, size, 0, NULL);
  return StarMalloc_malloc(arena, size);
}

// returned pointer not null => (
//   - 16-bytes aligned
//   - at least of the requested size (nb_elem * size_elem)
//   - filled with zeroes for subarray corresponding to the requested size
// )
__attribute__((visibility("default")))
void* calloc(size_t nb_elem, size_t size_elem) {
  unsigned arena = init();
  write_msg(3, nb_elem, size_elem, NULL);
  return StarMalloc_calloc(arena, nb_elem, size_elem);
}

__attribute__((visibility("default")))
void* realloc(void* ptr, size_t new_size) {
  unsigned arena = init();
  write_msg(4, new_size, 0, ptr);
  return StarMalloc_realloc(arena, ptr, new_size);
}

// noop if ptr is null
// deallocates previously allocated memory by (malloc / ...)
// UAF + DF = undefined
// execution is stopped when the deallocation process fails
__attribute__((visibility("default")))
void free(void *ptr) {
  // TODO: use enforce_init instead
  init();
  write_msg(1, 0, 0, ptr);
  bool b = StarMalloc_free(ptr);
  if (! b) {
    printf("free ptr: %p\n", ptr);
    fatal_error("invalid free");
  }
  return;
}

// returned value is the number of usable bytes
// in the block pointed to by ptr,
// a pointer to a block of memory allocated by (malloc / ...)
__attribute__((visibility("default")))
size_t malloc_usable_size(void* ptr) {
  // not needed for correctness, but way faster
  //if (ptr == NULL) {
  //  return 0;
  //}
  // TODO: use enforce_init instead
  init();
  return StarMalloc_getsize(ptr);
}

//aligned_alloc, posix_memalign, memalign
__attribute__((visibility("default")))
void* aligned_alloc(size_t alignment, size_t size) {
  unsigned arena = init();
  write_msg(2, alignment, size, NULL);
  return StarMalloc_aligned_alloc(arena, alignment, size);
}

//TODO: refine this, free_sized is part of C23
__attribute__((visibility("default")))
void free_sized(void* ptr, size_t size) {
  free(ptr);
}

//TODO: refine this, free_sized is part of C23
__attribute__((visibility("default")))
void free_aligned_sized(void* ptr, size_t size) {
  free(ptr);
}

__attribute__((visibility("default")))
int posix_memalign(void **memptr, size_t alignment, size_t size) {
  void* ptr = aligned_alloc(alignment, size);
  *memptr = ptr;
  return 0;
}

__attribute__((visibility("default")))
void* memalign(size_t alignment, size_t size) {
  void* ptr = aligned_alloc(alignment, size);
  return ptr;
}

__attribute__((visibility("default")))
void *valloc(size_t size) {
  fatal_error ("valloc not yet implemented");
  return NULL;
}

__attribute__((visibility("default")))
void *pvalloc(size_t size) {
  fatal_error ("pvalloc not yet implemented");
  return NULL;
}

__attribute__((visibility("default")))
void cfree(void* ptr) {
  fatal_error ("cfree is not implemented: removed since glibc 2.26");
}

//later on
//TODO: C++ stubs
