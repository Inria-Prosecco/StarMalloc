#include <stdint.h>
#include <stddef.h>
#include "krmlinit.h"
#include "StarMalloc.h"

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
static uint32_t init_status = 0UL;

void* malloc(size_t size) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  return StarMalloc_malloc(size);
}

void free(void *ptr) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  bool b = StarMalloc_free(ptr);
  return;
}

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
