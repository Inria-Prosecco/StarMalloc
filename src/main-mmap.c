#include "main-mmap.h"
#include <sys/mman.h>
#include <assert.h>
#include "internal/AVL.h"
#include "internal/StarMalloc.h"

static const size_t page_size = 4096UL;
static const size_t max_slabs = 1024UL;

uint8_t *mmap_init(size_t size) {
  void* ptr = mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE, -1, 0);
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

//TODO: check for mprotect return value
void mmap_trap (uint8_t* ptr, size_t len) {
  mprotect((void*) ptr, len, PROT_NONE);
  return;
}

uint64_t* Impl_Trees_Types_trees_malloc(uint64_t x) {
  uint64_t* ptr = mmap_u64(1);
  *ptr = x;
  return ptr;
}

Impl_Trees_Types_node* Impl_Trees_Types_trees_malloc2(Impl_Trees_Types_node x) {
  Impl_Trees_Types_node* ptr = (Impl_Trees_Types_node*) mmap_init(sizeof(Impl_Trees_Types_node));
  *ptr = x;
  return ptr;
}

void Impl_Trees_Types_trees_free(uint64_t* r) {
  return;
}

void Impl_Trees_Types_trees_free2(Impl_Trees_Types_node* r) {
  return;
}

Impl_Trees_Types_node** mmap_ptr_metadata() {
  return (Impl_Trees_Types_node**) mmap_init(sizeof(Impl_Trees_Types_node*));
}
