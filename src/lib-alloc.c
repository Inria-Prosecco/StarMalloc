#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include "krmlinit.h"
#include "StarMalloc.h"

static uint32_t init_status = 0UL;
static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;

uint8_t* StarMalloc_memcpy_u8(uint8_t* dest, uint8_t* src, size_t n) {
  return (uint8_t*) memcpy((void*) dest, (void*) src, n);
}

void* malloc(size_t size) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  return StarMalloc_malloc(size);
}

void free(void *ptr) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  //printf("free ptr: %p\n", ptr);
  bool b = StarMalloc_free(ptr);
  //printf("  result: %b\n");
  return;
}

void* realloc(void* ptr, size_t new_size) {
  if (! init_status) {
    pthread_mutex_lock(&m);
    krmlinit_globals();
    init_status=1UL;
    pthread_mutex_unlock(&m);
  }
  //printf("ptr: %p, new_size: %lu\n", ptr, new_size);
  void* new_ptr = StarMalloc_realloc(ptr, new_size);
  //printf("  new_ptr: %p\n", new_ptr);
  return new_ptr;
}

void* calloc(size_t nb_elem, size_t size_elem) {
  //if (! init_status) {
  //  pthread_mutex_lock(&m);
  //  krmlinit_globals();
  //  init_status=1UL;
  //  pthread_mutex_unlock(&m);
  //}
  size_t size = nb_elem * size_elem;
  void* ptr = malloc(size);
  //size_t approx_size = StarMalloc_getsize(ptr);
  //printf("size/approx_size: %lu/%lu\n", size, approx_size);
  memset(ptr, 0, size);
  //for (size_t i = 0; i < size; i++) {
  //  temp_ptr[i] = 0;
  //}
  return ptr;
}
