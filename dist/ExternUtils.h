// SPDX-License-Identifier: Apache-2.0


#ifndef __ExternUtils_H
#define __ExternUtils_H

#include "krmllib.h"

extern uint32_t ffs64(uint64_t x);

extern uint32_t clz(uint64_t x);

extern void apply_zeroing_u8(uint8_t *ptr, size_t n);

extern bool check_zeroing_u8(uint8_t *ptr, size_t n);

extern uint8_t *memcpy_u8(uint8_t *dest, uint8_t *src, size_t n);

extern size_t builtin_mul_overflow(size_t x, size_t y);


#define __ExternUtils_H_DEFINED
#endif
