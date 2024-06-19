// SPDX-License-Identifier: Apache-2.0


#ifndef __StarMalloc_H
#define __StarMalloc_H

#include "krmllib.h"

#include "Steel_SpinLock.h"
#include "SizeClass.h"
#include "Mman.h"
#include "ArrayList.h"

extern bool StarMalloc_memcheck_u8(uint8_t *ptr, size_t n);

extern uint8_t *StarMalloc_memset_u8(uint8_t *dest, uint8_t c, size_t n);

extern uint8_t *StarMalloc_memcpy_u8(uint8_t *dest, uint8_t *src, size_t n);

extern void StarMalloc_malloc_zeroing_die(uint8_t *ptr);

uint8_t *StarMalloc_malloc(size_t arena_id, size_t size);

uint8_t *StarMalloc_aligned_alloc(size_t arena_id, size_t alignment, size_t size);

bool StarMalloc_free(uint8_t *ptr);

size_t StarMalloc_getsize(uint8_t *ptr);

uint8_t *StarMalloc_realloc(size_t arena_id, uint8_t *ptr, size_t new_size);

extern size_t StarMalloc_builtin_mul_overflow(size_t x, size_t y);

uint8_t *StarMalloc_calloc(size_t arena_id, size_t size1, size_t size2);


#define __StarMalloc_H_DEFINED
#endif
