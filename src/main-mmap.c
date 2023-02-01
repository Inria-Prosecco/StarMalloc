#include "main-mmap.h"
#include "MMan.h"

static const size_t page_size = 4096UL;
static const size_t max_slabs = 1024UL;

uint8_t *mmap_s(uint64_t len) {
  return mmap((uint64_t)0U, len, 3l, (int32_t)32, (int32_t)-1, (uint32_t)0U);
}

uint8_t *mmap_u8(size_t len) {
  return (uint8_t*) mmap_s(len * sizeof(uint8_t));
}

uint64_t *mmap_u64(size_t len) {
  return (uint64_t*) mmap_s(len * sizeof(uint64_t));
}

//static ArrayListGen_cell__int32_t *mmap_cell_status(size_t len) {
//  return (ArrayListGen_cell__int32_t*) mmap_s(len * sizeof(ArrayLisGent_cell__int32_t));
//}

uint32_t *mmap_ptr_u32() {
  return (uint32_t*) mmap_s(sizeof(uint32_t));
}

size_t *mmap_ptr_us() {
  return (size_t*) mmap_s(sizeof(size_t));
}
