#include <stddef.h>
#include <stdint.h>
#include "internal/StarMalloc.h"
#include "fatal_error.h"

// glue
uint32_t Utils2_ffs64(uint64_t x) {
  return __builtin_ctzll(~x);
}

// glue
size_t StarMalloc_builtin_mul_overflow(size_t x, size_t y) {
  size_t z;
  int r = __builtin_mul_overflow(x, y, &z);
  if (r) {
    fatal_error("calloc requested size leads to overflow");
  }
  return z;
}

// required comparison using uintptr_t
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

// monomorphized (from void* to uint8_t*) glue
uint8_t* StarMalloc_memcpy_u8(uint8_t* dest, uint8_t* src, size_t n) {
  return (uint8_t*) memcpy((void*) dest, (void*) src, n);
}

// monomorphized (from void* to uint8_t*) glue
// TODO: memset can be optimized, use hacl-star libmemzero
uint8_t* StarMalloc_memset_u8(uint8_t* dest, uint8_t v, size_t n) {
  return (uint8_t*) memset((void*) dest, v, n);
}

// required casts
Impl_Trees_Types_node* Impl_Trees_Types_array_u8__to__ref_node(uint8_t* arr) {
  // see lib_avl_mono/Impl.Trees.Types.fst
  static_assert(sizeof(Impl_Trees_Types_node) <= 64);
  return (Impl_Trees_Types_node*) arr;
}
uint8_t* Impl_Trees_Types_ref_node__to__array_u8(Impl_Trees_Types_node* r) {
  return (uint8_t*) r;
}

// TODO: comment
void StarMalloc_malloc_zeroing_die(uint8_t* ptr) {
  //fatal_error("malloc_zeroing_die");
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
