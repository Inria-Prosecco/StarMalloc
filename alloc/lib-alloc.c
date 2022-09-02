#include "Main.h"
#include <stdint.h>
#include <pthread.h>
#include "config.h"
#include "lib-alloc0.h"

// WARNING:
// calling stdlib malloc before or inside the definition
// of this function, that is the only malloc version to be used
// will result in segfaults
// TODO:
// expose option to force reservation of the allocated memory
// htop: VIRT \neq RES

uint64_t _size() {
  lock();
  void* ptr = get_metadata();
  uint64_t r = Main__size(ptr);
  unlock();
  return r;
}

void* malloc (size_t size) {
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

void free (void* ptr_to_block) {
  lock();
#if BASIC
#else
  void* ptr = get_metadata();
  ptr = (void*) Main_free(ptr, (uint64_t) ptr_to_block);
  set_metadata(ptr);
#endif
  unlock();
  return;
}

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
