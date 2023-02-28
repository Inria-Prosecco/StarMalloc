#include <stddef.h>
#include <stdint.h>

uint32_t Utils2_ffs64(uint64_t x) {
  return __builtin_ctzll(~x);
}

/* TODO: to be removed */
uint64_t Impl_Trees_Types_ptr_to_u64(uint8_t* ptr) {
  return (uint64_t) ptr;
}
