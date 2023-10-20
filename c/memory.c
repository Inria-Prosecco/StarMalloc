#include "memory.h"

#include <errno.h>
#include <sys/mman.h>
#include <assert.h>

#include "internal/StarMalloc.h"
#include "fatal_error.h"

uint8_t *mmap_init(size_t size) {
  void* ptr = mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE|MAP_NORESERVE, -1, 0);
  assert (ptr != NULL);
  return ptr;
}

uint8_t *mmap_noinit(size_t size) {
  return mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE, -1, 0);
}

uint8_t *mmap_u8(size_t len) {
  return (uint8_t*) mmap_noinit(len * sizeof(uint8_t));
}

void munmap_u8(uint8_t* ptr, size_t len) {
  bool b = munmap((void*) ptr, len);
  if (b && errno != ENOMEM) {
    fatal_error("non-ENOMEM munmap failure");
  }
  return;
}

uint8_t *mmap_u8_init(size_t len) {
  return (uint8_t*) mmap_init(len * sizeof(uint8_t));
}

uint64_t *mmap_u64_init(size_t len) {
  return (uint64_t*) mmap_init(len * sizeof(uint64_t));
}

ArrayList_cell *mmap_cell_status_init(size_t len) {
  return (ArrayList_cell*) mmap_init(len * sizeof(ArrayList_cell));
}

//TODO: to be removed
//uint32_t *mmap_ptr_u32() {
//  return (uint32_t*) mmap_init(sizeof(uint32_t));
//}

size_t *mmap_ptr_us_init() {
  return (size_t*) mmap_init(sizeof(size_t));
}

size_class* mmap_sc_init(size_t len) {
  return (size_class*) mmap_init(len * sizeof(size_class));
}

uint32_t* mmap_sizes_init (size_t len) {
  return (uint32_t*) mmap_init(len * sizeof(uint32_t));
}

void mmap_strict_trap (uint8_t* ptr, size_t len) {
  void* p = mmap((void*) ptr, len, PROT_NONE, MAP_ANONYMOUS|MAP_PRIVATE|MAP_FIXED, -1, 0);
  if (p == MAP_FAILED && errno != ENOMEM) {
    assert (false);
  }
  return;
}

void mmap_trap (uint8_t* ptr, size_t len) {
  int r = madvise((void*) ptr, len, MADV_DONTNEED);
  if (r && errno != ENOMEM) {
    assert (false);
  }
  return;
}


Impl_Trees_Types_node** mmap_ptr_metadata() {
  return (Impl_Trees_Types_node**) mmap_init(sizeof(Impl_Trees_Types_node*));
}
