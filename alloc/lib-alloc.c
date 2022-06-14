#include "Main.h"
#include <stdbool.h>
#include <stdint.h>
#include <pthread.h>


// WARNING:
// calling stdlib malloc before or inside the definition
// of this function, that is the only malloc version to be used
// will result in segfaults
// TODO:
// expose option to force reservation of the allocated memory
// htop: VIRT \neq RES


void* malloc (size_t size) {
  lock();
  void* ptr = (void*) Main_malloc(size);
  unlock();
  return ptr;
}

//uint64_t free_count = 0;
void free (void* ptr) {
  //free_count++;
  lock();
  Main_free(ptr);
  unlock();
  //if (f_cnt % 2 == 0)
  //  puts("a");
  //else
  //  puts("b");
}

uint64_t size () {
  return Main_size ();
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
