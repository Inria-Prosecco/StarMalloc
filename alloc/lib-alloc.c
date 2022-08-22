#include "Main.h"
//#include <stdbool.h>
#include <stdint.h>
#include <pthread.h>
//#include <stdatomic.h>
#include "config.h"
#include "lib-alloc0.h"

// WARNING:
// calling stdlib malloc before or inside the definition
// of this function, that is the only malloc version to be used
// will result in segfaults
// TODO:
// expose option to force reservation of the allocated memory
// htop: VIRT \neq RES
//static const unsigned n_arena = N_ARENA;
//static LOCAL_ATTR unsigned thread_arena = n_arena;
//static LOCAL_ATTR unsigned is_init = 0;
//static atomic_uint thread_arena_counter = 0;

void* malloc (size_t size) {
  //if (! is_init) {
  //  thread_arena = thread_arena_counter++ % n_arena;
  //  is_init = 1;
  //}
  //lock(thread_arena);
  void* allocated_block = NULL;
  lock();
#if BASIC
  allocated_block = Main_mmap(size, 3l);
#else
  void* ptr = NULL;
  ptr = get_metadata();
  K____Impl_Core_node__Aux_a__uint64_t r = Main_malloc(ptr, size);
  ptr = r.fst;
  set_metadata(ptr);
  allocated_block = (void*) r.snd;
#endif
  unlock();
  return allocated_block;
  //ptr = Main_mmap(size, 3l);
  //return ptr;
}

//uint64_t free_count = 0;
void free (void* ptr_to_block) {
  //if (! is_init) {
  //  thread_arena = thread_arena_counter++ % n_arena;
  //  is_init = 1;
  //}
  //free_count++;
  //lock();
  //void* ptr = get_metadata();
  //ptr = (void*) Main_free(ptr, (uint64_t) ptr_to_block);
  //set_metadata(ptr);
  //unlock();
  //if (f_cnt % 2 == 0)
  //  puts("a");
  //else
  //  puts("b");
}

//uint64_t size () {
//  return Main_size ();
//}

// required for realloc
// this small implementation is likely not very robust
//void* memcpy2 (void* dst, const void* src, long unsigned int cnt) {
//  //puts("C");
//  char* dst2 = (char*) dst;
//  char* src2 = (char*) src;
//  while (cnt) {
//    *(dst2++) = *(src2++);
//    cnt--;
//  }
//  //puts("D");
//}

// TODO: does not enforce zeroing
void* calloc(long unsigned int nb_elem, long unsigned int size_elem) {
  long unsigned int size = nb_elem * size_elem;
  void* ptr = malloc(size);
  return ptr;
}

void* realloc(void* ptr, size_t size) {
  // why the spec would allow this, seriously...
  //void* ptr2 = (void*) malloc (size);
  if (ptr == NULL) {
    return malloc(size);
  }
  void* ptr2 = (void*) malloc (size);
  //printf("src: %p\n", ptr);
  //printf("dst: %p\n", ptr2);
  // size is incorrect here,
  // need to know size of the previous allocation,
  // otherwise a bus error can be raised
  //puts("A");
  memcpy(ptr2, ptr, size);
  free(ptr);
  return ptr2;
}
//
//- bench les arbres avec alloc custom
//- variable globale côté Steel
