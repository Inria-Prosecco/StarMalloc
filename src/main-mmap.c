#include "main-mmap.h"
//#include "Mman.h"
#include "Aux.h"
#include <sys/mman.h>

static const size_t page_size = 4096UL;
static const size_t max_slabs = 1024UL;

uint8_t *mmap_s(size_t size) {
  return mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE, -1, 0);
  //return mmap((uint64_t)0U, len, 3l, (int32_t)33, (int32_t)-1, (uint32_t)0U);
  //return mmap(len);
}

uint8_t *mmap_u8(size_t len) {
  return (uint8_t*) mmap_s(len * sizeof(uint8_t));
}

uint64_t *mmap_u64(size_t len) {
  return (uint64_t*) mmap_s(len * sizeof(uint64_t));
}

ArrayList_cell *mmap_cell_status(size_t len) {
  return (ArrayList_cell*) mmap_s(len * sizeof(ArrayList_cell));
}

uint32_t *mmap_ptr_u32() {
  return (uint32_t*) mmap_s(sizeof(uint32_t));
}

size_t *mmap_ptr_us() {
  return (size_t*) mmap_s(sizeof(size_t));
}

uint64_t* Aux_trees_malloc(uint64_t x) {
  uint64_t* ptr = mmap_u64(1);
  *ptr = x;
  return ptr;
}

Impl_Core_node__Aux_a* Aux_trees_malloc2(Impl_Core_node__Aux_a x) {
  Impl_Core_node__Aux_a* ptr = mmap_s(sizeof(Impl_Core_node__Aux_a));
  *ptr = x;
  return ptr;
}

void Aux_trees_free(uint64_t* r) {
  return;
}

void Aux_trees_free2(Impl_Core_node__Aux_a* r) {
  return;
}

Impl_Core_node__Aux_a** mmap_ptr_metadata() {
  return (Impl_Core_node__Aux_a**) mmap_s(sizeof(Impl_Core_node__Aux_a*));
}
