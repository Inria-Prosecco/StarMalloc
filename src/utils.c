#include <stddef.h>
#include <stdint.h>
#include "Slabs.h"

uint32_t Utils2_ffs64(uint64_t x) {
  //return __builtin_ffsll(~x) - 1;
  return __builtin_ctzll(~x);
}

ptrdiff_t Utils2_ptrdiff(void* arr1, void* arr2) {
  ptrdiff_t r = arr1 - arr2;
  return r;
}
