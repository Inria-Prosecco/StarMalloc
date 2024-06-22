// SPDX-License-Identifier: Apache-2.0


#ifndef __StarMalloc_H
#define __StarMalloc_H

#include "krmllib.h"

#include "Steel_SpinLock.h"
#include "SizeClassSelection.h"
#include "SizeClass.h"
#include "PtrdiffWrapper.h"
#include "Mman.h"
#include "ExternUtils.h"
#include "ArrayList.h"

extern void StarMalloc_malloc_zeroing_die(uint8_t *ptr);

uint8_t *StarMalloc_malloc(size_t arena_id, size_t size);

uint8_t *StarMalloc_aligned_alloc(size_t arena_id, size_t alignment, size_t size);

bool StarMalloc_free(uint8_t *ptr);

typedef struct K___size_t_bool_s
{
  size_t fst;
  bool snd;
}
K___size_t_bool;

K___size_t_bool StarMalloc_full_getsize(uint8_t *ptr);

size_t StarMalloc_getsize(uint8_t *ptr);

uint8_t *StarMalloc_realloc(size_t arena_id, uint8_t *ptr, size_t new_size);

uint8_t *StarMalloc_calloc(size_t arena_id, size_t size1, size_t size2);


#define __StarMalloc_H_DEFINED
#endif
