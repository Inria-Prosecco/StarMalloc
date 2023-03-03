#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include "krmlinit.h"
#include "StarMalloc.h"

static uint32_t init_status = 0UL;

uint8_t* StarMalloc_memcpy_u8(uint8_t* dest, uint8_t* src, size_t n) {
  return (uint8_t*) memcpy((void*) dest, (void*) src, n);
}

void* malloc(size_t size) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  return StarMalloc_malloc(size);
}

void free(void *ptr) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  bool b = StarMalloc_free(ptr);
  return;
}

void* realloc(void* ptr, size_t new_size) {
  if (! init_status) { krmlinit_globals(); init_status=1UL; }
  return StarMalloc_realloc(ptr, new_size);
}

/* TODO: does not enforce zeroing */
void* calloc(long unsigned int nb_elem, long unsigned int size_elem) {
  long unsigned int size = nb_elem * size_elem;
  void* ptr = malloc(size);
  return ptr;
}
