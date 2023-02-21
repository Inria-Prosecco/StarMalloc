#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
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

uint8_t* memcpy_u8(uint8_t* dest, uint8_t* src, size_t n) {
  return (uint8_t*) memcpy((void*) dest, (void*) src, n);
}

void* malloc(size_t size) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  void* ptr = StarMalloc_malloc(size);
  //printf("malloc: %p, %lu\n", ptr, size);
  return StarMalloc_malloc(size);
}

void free(void *ptr) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  bool b = StarMalloc_free(ptr);
  //if (! b) {
  //  printf("free: %p\n", ptr);
  //  abort();
  //}
  return;
}

void* realloc(void* ptr, size_t new_size) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  if (ptr == NULL) {
    return malloc(new_size);
  } else {
    //printf("1/2\n");
    void* new_ptr = StarMalloc_realloc(ptr, new_size);
    //printf("2/2\n");
    return new_ptr;
  }
}

// TODO: does not enforce zeroing
void* calloc(long unsigned int nb_elem, long unsigned int size_elem) {
  long unsigned int size = nb_elem * size_elem;
  void* ptr = malloc(size);
  return ptr;
}
