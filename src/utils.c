#include <stddef.h>
#include <stdint.h>
#include "internal/AVL.h"

uint32_t Utils2_ffs64(uint64_t x) {
  return __builtin_ctzll(~x);
}

uint64_t Impl_Trees_Types_cmp(
  Impl_Trees_Types_data x,
  Impl_Trees_Types_data y) {
  uint8_t* x_fst = x.fst;
  uint8_t* y_fst = y.fst;
  uintptr_t x_cast = (uintptr_t) x_fst;
  uintptr_t y_cast = (uintptr_t) y_fst;
  if (x_fst == y_fst) {
    return 0L;
  } else if (x_fst < y_fst) {
    return (-1L);
  } else {
    return 1L;
  }
}
