//#include "Main.h"
#include "lib-alloc0.h"
#include <stdint.h>
#include <pthread.h>
#include "config.h"
//#include <unistd.h>
#include <stdatomic.h>

// TODO: remove
// + related mutexes
// static pthread_mutex_t metadata_mutexes[N_ARENA];
// TODO: remove
// static pthread_mutex_t the_mutex;

const uint64_t uint64_size = sizeof(uint64_t);
const uint64_t metadata_node_size = sizeof(Impl_Core_node__Aux_a);
const uint64_t allocated_size = ALLOCATED_SIZE;

/*
- (1) N_ARENA, N_THREADS arbitrary
- (2) each thread must keep the same arena throughout its execution,
as we want arenas isolated
- (3) if N_THREADS > N_ARENA, two threads will have the same arena

design decisions:
- use of thread-local storage to attribute an arena to each thread (2)
- reduce contention: no global mutex but arena-specific mutex (3)
- initialization difficulties:
  - (a) metadatas1, metadatas2, metadata_ptrs, mutexes initialization
  - (b) thread arena attribution during init
  remarks
  - (a) must be done once, at most one thread can do it
    => currently, initial contention
    TODO: we can do better and remove it
  - (b) must be done once, any thread must do it
- initially, arena identifier was attributed in lib-alloc.c, changed


tests:
- test-alloc2 fails with:
  -(N_ARENA = 4, N_THREADS >= 64) (works with 32)
  -(N_ARENA = 8, N_THREADS >= 128) (works with 64)
- test-alloc3 fails
*/

// per-arena allocated metadata regions
static uint64_t* metadatas1[N_ARENA];
static Impl_Core_node__Aux_a* metadatas2[N_ARENA];
// per-arena positions within these regions
static uint64_t metadatas_pos1[N_ARENA];
static uint64_t metadatas_pos2[N_ARENA];
// per-arena mutexes
static pthread_mutex_t mutexes[N_ARENA];
// per-arena roots of the metadata trees
static Impl_Core_node__Aux_a* metadata_ptrs[N_ARENA];

// global init: per-arena variables
static uint64_t status = 0UL;
static pthread_mutex_t init_mutex = PTHREAD_MUTEX_INITIALIZER;

// local init: per-thread arena identifier
static LOCAL_ATTR uint64_t status1 = 0UL;
static atomic_uint_least64_t thread_arena_counter = 0;
static LOCAL_ATTR uint64_t thread_arena = N_ARENA;
static pthread_mutex_t init_mutex1 = PTHREAD_MUTEX_INITIALIZER;

void init1() {
  pthread_mutex_lock(&init_mutex1);
  if (status1) return;
  thread_arena = thread_arena_counter++ % N_ARENA;
  status1 = 1UL;
  pthread_mutex_unlock(&init_mutex1);
}

void init2() {
  pthread_mutex_lock(&init_mutex);
  if (status) return;
  for (size_t i = 0; i < N_ARENA; i++) {
    metadatas1[i] = Main_mmap(allocated_size, 3l);
    metadatas2[i] = Main_mmap(allocated_size, 3l);
    metadatas1[i][0];
    metadatas2[i][0];
    metadata_ptrs[i] = Main_create_leaf();
    pthread_mutex_init(&mutexes[i], NULL);
  }
  //pthread_mutex_init(&the_mutex, NULL);
  status = 1;
  pthread_mutex_unlock(&init_mutex);
}

void lock() {
  if (! status1) init1();
  if (! status) init2 ();
  pthread_mutex_lock(&mutexes[thread_arena]);
  //pthread_mutex_lock(&the_mutex);
}
void unlock() {
  pthread_mutex_unlock(&mutexes[thread_arena]);
  //pthread_mutex_unlock(&the_mutex);
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
  //lock_m();
  malloc_check1();
  uint64_t pos = metadatas_pos1[thread_arena];
  uint64_t* ptr = &metadatas1[thread_arena][pos];
  *ptr = v;
  metadatas_pos1[thread_arena] += sizeof(uint64_t);
  //unlock_m();
  return ptr;
}

Impl_Core_node__Aux_a* Aux_trees_malloc2(Impl_Core_node__Aux_a n) {
  //lock_m();
  malloc_check2();
  uint64_t pos = metadatas_pos2[thread_arena];
  Impl_Core_node__Aux_a* ptr = &metadatas2[thread_arena][pos];
  *ptr = n;
  metadatas_pos2[thread_arena] += sizeof(Impl_Core_node__Aux_a);
  //unlock_m();
  return ptr;
}

Impl_Core_node__Aux_a* get_metadata() {
  return metadata_ptrs[thread_arena];
}

void set_metadata(Impl_Core_node__Aux_a* metadata) {
  metadata_ptrs[thread_arena] = metadata;
}
