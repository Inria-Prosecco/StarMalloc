#include "main-mmap.h"

#include <errno.h>
#include <sys/mman.h>
#include <assert.h>
#include "internal/AVL.h"
#include "internal/StarMalloc.h"

static const size_t page_size = 4096UL;
static const size_t max_slabs = 1024UL;

uint8_t *mmap_init(size_t size) {
  void* ptr = mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE|MAP_NORESERVE, -1, 0);
  assert (ptr != NULL);
  return ptr;
}

uint8_t *mmap_noinit(size_t size) {
  return mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE, -1, 0);
}

void munmap_u8(uint8_t* ptr, size_t len) {
  bool b = munmap((void*) ptr, len);
  assert (! b);
  return;
}

uint8_t *mmap_u8(size_t len) {
  return (uint8_t*) mmap_init(len * sizeof(uint8_t));
}

uint64_t *mmap_u64(size_t len) {
  return (uint64_t*) mmap_init(len * sizeof(uint64_t));
}

ArrayList_cell *mmap_cell_status(size_t len) {
  return (ArrayList_cell*) mmap_init(len * sizeof(ArrayList_cell));
}

uint32_t *mmap_ptr_u32() {
  return (uint32_t*) mmap_init(sizeof(uint32_t));
}

size_t *mmap_ptr_us() {
  return (size_t*) mmap_init(sizeof(size_t));
}

size_class* mmap_sc(size_t len) {
  return (size_class*) mmap_init(len * sizeof(size_class));
}

uint32_t* mmap_sizes (size_t len) {
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

void StarMalloc_malloc_zeroing_die(uint8_t* ptr) {
  assert (false);
}

bool StarMalloc_memcheck_u8(uint8_t* ptr, size_t len) {
  for (size_t i = 0; i < len; i++) {
    if (ptr[i] != 0) {
      return false;
    }
  }
  return true;
}

void SlotsFree_deallocate_zeroing(uint32_t sc, uint8_t* ptr) {
  size_t len = (size_t) sc;
  memset(ptr, 0, len);
}

uint32_t avl_data_size_aux = sizeof(Impl_Trees_Types_node);

Impl_Trees_Types_node* array_u8__to__ref_node(uint8_t* arr) {
  return (Impl_Trees_Types_node*) arr;
}
uint8_t* ref_node__to__array_u8(Impl_Trees_Types_node* r) {
  return (uint8_t*) r;
}

Impl_Trees_Types_node** mmap_ptr_metadata() {
  return (Impl_Trees_Types_node**) mmap_init(sizeof(Impl_Trees_Types_node*));
}
