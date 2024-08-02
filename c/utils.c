#include <stddef.h>
#include <stdint.h>
#include "internal/StarMalloc.h"
#include "fatal_error.h"

// glue
uint32_t ffs64(uint64_t x) {
  return __builtin_ctzll(~x);
}

uint32_t clz(uint64_t x) {
  return __builtin_clzll(x);
}

// glue
size_t builtin_mul_overflow(size_t x, size_t y) {
  size_t z;
  int r = __builtin_mul_overflow(x, y, &z);
  if (r) {
    fatal_error("calloc requested size leads to overflow");
  }
  return z;
}

static inline size_t align(size_t size, size_t align) {
    size_t mask = align - 1;
    return (size + mask) & ~mask;
}


size_t f(size_t size, uint32_t alignment, uint8_t* ptr) {
  size_t lead_size = align((uintptr_t)ptr, alignment) - (uintptr_t)ptr;
  return lead_size;
}

// required comparison using uintptr_t
uint64_t Impl_Trees_Cast_M_cmp(
  Impl_Trees_Cast_M_data_ x,
  Impl_Trees_Cast_M_data_ y) {
  uintptr_t x_cast = (uintptr_t) x.user_ptr;
  uintptr_t y_cast = (uintptr_t) y.user_ptr;
  if (x_cast == y_cast) {
    return 0L;
  } else if (x_cast < y_cast) {
    return (-1L);
  } else {
    return 1L;
  }
}

// monomorphized (from void* to uint8_t*) glue
uint8_t* memcpy_u8(uint8_t* dest, uint8_t* src, size_t n) {
  return (uint8_t*) memcpy((void*) dest, (void*) src, n);
}

// monomorphized (from void* to uint8_t*) glue
// TODO: compat, use hacl-star libmemzero
void apply_zeroing_u8(uint8_t* dest, size_t n) {
  explicit_bzero(dest, n);
  return;
}

bool check_zeroing_u8(uint8_t* ptr, size_t len) {
  for (size_t i = 0; i < len; i++) {
    if (ptr[i] != 0) {
      return false;
    }
  }
  return true;
}

// required casts
Impl_Trees_Cast_M_node* Impl_Trees_Cast_M_array_u8__to__ref_node(uint8_t* arr) {
  // see lib_avl_mono/Impl.Trees.Types.fst
  static_assert(sizeof(Impl_Trees_Cast_M_node) <= 128);
  return (Impl_Trees_Cast_M_node*) arr;
}
uint8_t* Impl_Trees_Cast_M_ref_node__to__array_u8(Impl_Trees_Cast_M_node* r) {
  return (uint8_t*) r;
}

void FatalError_die_from_avl_node_malloc_failure (Impl_Trees_Cast_M_node x, uint8_t* ptr) {
  fatal_error("large allocator: AVL node allocation failed");
}
void FatalError_die_from_avl_node_free_failure (uint8_t* ptr) {
  fatal_error("large allocator: AVL node deallocation failed");
}
void FatalError_die_from_malloc_zeroing_check_failure (uint8_t* ptr) {
  fatal_error("small allocator: malloc zeroing check failed");
}
void FatalError_die_from_realloc_invalid_previous_alloc (uint8_t* ptr) {
  fatal_error("realloc: invalid realloc");
}
void FatalError_die_from_realloc_free_failure (uint8_t* ptr) {
  fatal_error("realloc: invalid internal free");
}
