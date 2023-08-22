#include <stddef.h>
#include <stdint.h>
#include "internal/StarMalloc.h"

uint32_t Utils2_ffs64(uint64_t x) {
  return __builtin_ctzll(~x);
}

uint64_t Impl_Trees_Types_cmp(
  Impl_Trees_Types_data x,
  Impl_Trees_Types_data y) {
  uintptr_t x_cast = (uintptr_t) x.fst;
  uintptr_t y_cast = (uintptr_t) y.fst;
  if (x_cast == y_cast) {
    return 0L;
  } else if (x_cast < y_cast) {
    return (-1L);
  } else {
    return 1L;
  }
}

size_t get_sizeof_avl_data_as_bytes(){
  return sizeof(Impl_Trees_Types_data);
}
