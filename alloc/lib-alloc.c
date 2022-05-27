#include "Main.c"
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

// WARNING:
// calling stdlib malloc before or inside the definition
// of this function, that is the only malloc version to be used
// will result in segfaults
// TODO:
// expose option to force reservation of the allocated memory
// htop: VIRT \neq RES
void* malloc (size_t size) {
  volatile void* ptr = (void*) Main_malloc(size, 3l);
  *ptr;
  return ptr;
}

uint64_t free_count = 0;
void free (void* ptr) {
  free_count++;
  //if (f_cnt % 2 == 0)
  //  puts("a");
  //else
  //  puts("b");
}

// required for realloc
// this small implementation is likely not very robust
void* memcpy2 (void* dst, const void* src, long unsigned int cnt) {
  char* dst2 = (char*) dst;
  char* src2 = (char*) src;
  while (cnt) {
    *(dst2++) = *(src2++);
    cnt--;
  }
}

// TODO: does not enforce zeroing
void* calloc(long unsigned int nb_elem, long unsigned int size_elem) {
  long unsigned int size = nb_elem * size_elem;
  void* ptr = Main_malloc(size, 3l);
  return ptr;
}

void* realloc(void* ptr, size_t size) {
  // why the spec would allow this, seriously...
  if (ptr == NULL) {
    return malloc(size);
  }
  void* ptr2 = (void*) Main_malloc (size, 3l);
  memcpy2(ptr2, ptr, size);
  free(ptr);
  return ptr2;
}
