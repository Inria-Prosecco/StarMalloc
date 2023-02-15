#include <stddef.h>
#include <stdint.h>

uint32_t Utils2_ffs64(uint64_t x) {
  //return __builtin_ffsll(~x) - 1;
  return __builtin_ctzll(~x);
}
