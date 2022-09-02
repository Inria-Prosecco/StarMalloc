#include "config.h"
#include "lib-alloc0.h"
#include <stdint.h>
#include <pthread.h>
#include <stdatomic.h>

const uint64_t uint64_size = sizeof(uint64_t);
const uint64_t metadata_node_size = sizeof(Impl_Core_node__Aux_a);
const uint64_t allocated_size = ALLOCATED_SIZE;

/*
- (1) N_ARENA, N_THREADS arbitrary
- (2) each thread must keep the same arena throughout its execution,
as:
  - (correctness) free/realloc rely on accessing corresponding metadata
  - (security) arenas should be isolated
- (3) if N_THREADS > N_ARENA, two threads will have the same arena

design decisions:
- use of thread-local storage to attribute an arena to each thread (2)
- reduce contention: no global mutex but arena-specific mutex (3)
- initialization difficulties:
  - (a) metadatas1, metadatas2, metadata_ptrs, mutexes initialization
  - (b) thread arena attribution during init
- v0: arena identifier was attributed in lib-alloc.c, changed
- v1: 2 inits, one global (n_arena datas), one local (thread arena id)
- v2: 1 lazy init, one local (per thread) with corresponding arena data
  -> less contention
  -> less useless memory reservation
*/

// per-arena allocated metadata regions
static uint8_t* metadatas1[N_ARENA];
static uint8_t* metadatas2[N_ARENA];
// per-arena positions within these regions
static uint64_t metadatas_pos1[N_ARENA];
static uint64_t metadatas_pos2[N_ARENA];
// per-arena mutexes
static pthread_mutex_t mutexes[N_ARENA];
// per-arena roots of the metadata trees
static Impl_Core_node__Aux_a* metadata_ptrs[N_ARENA];

// global init: per-arena variables
//static uint64_t status = 0UL;
//static pthread_mutex_t init_mutex = PTHREAD_MUTEX_INITIALIZER;

// local init: per-thread arena identifier
static LOCAL_ATTR uint64_t status1 = 0UL;
static atomic_uint_least64_t thread_arena_counter = 0;
static LOCAL_ATTR uint64_t thread_arena = N_ARENA;
static pthread_mutex_t init_mutex1 = PTHREAD_MUTEX_INITIALIZER;
// during the local init: per-arena data is init, at most once
static uint64_t init_arena[N_ARENA];

void init1() {
  pthread_mutex_lock(&init_mutex1);
  if (! status1) {
    thread_arena = thread_arena_counter++ % N_ARENA;
    status1 += 1UL;
  }
  if (! init_arena[thread_arena]) {
    metadatas1[thread_arena] = Main_mmap(allocated_size, 3l);
    metadatas2[thread_arena] = Main_mmap(allocated_size, 3l);
    metadatas1[thread_arena][0];
    metadatas2[thread_arena][0];
    pthread_mutex_init(&mutexes[thread_arena], NULL);
    metadata_ptrs[thread_arena] = Main_create_leaf();
    init_arena[thread_arena] += 1UL;
  }
  pthread_mutex_unlock(&init_mutex1);
}

void lock() {
  if (! status1) init1();
  pthread_mutex_lock(&mutexes[thread_arena]);
}
void unlock() {
  pthread_mutex_unlock(&mutexes[thread_arena]);
}

void malloc_check1() {
  uint64_t pos = metadatas_pos1[thread_arena];
  if (pos + uint64_size >= allocated_size) {
    //puts("Mmap again 1.");
    metadatas1[thread_arena] = Main_mmap(allocated_size, 3l);
    metadatas_pos1[thread_arena] = 0UL;
  }
}

void malloc_check2() {
  uint64_t pos = metadatas_pos2[thread_arena];
  if (pos + metadata_node_size >= allocated_size) {
    //puts("Mmap again 2.");
    metadatas2[thread_arena] = Main_mmap(allocated_size, 3l);
    metadatas_pos2[thread_arena] = 0UL;
  }
}

uint64_t* Aux_trees_malloc(uint64_t v) {
  malloc_check1();
  uint64_t pos = metadatas_pos1[thread_arena];
  uint64_t* ptr = (uint64_t*) &metadatas1[thread_arena][pos];
  *ptr = v;
  metadatas_pos1[thread_arena] += uint64_size;
  return ptr;
}

Impl_Core_node__Aux_a* Aux_trees_malloc2(Impl_Core_node__Aux_a n) {
  malloc_check2();
  uint64_t pos = metadatas_pos2[thread_arena];
  Impl_Core_node__Aux_a* ptr = (Impl_Core_node__Aux_a*) &metadatas2[thread_arena][pos];
  *ptr = n;
  metadatas_pos2[thread_arena] += metadata_node_size;
  return ptr;
}

void Aux_trees_free(uint64_t* v) {}
void Aux_trees_free2(Impl_Core_node__Aux_a* n) {}

Impl_Core_node__Aux_a* get_metadata() {
  return metadata_ptrs[thread_arena];
}

void set_metadata(Impl_Core_node__Aux_a* metadata) {
  metadata_ptrs[thread_arena] = metadata;
}
