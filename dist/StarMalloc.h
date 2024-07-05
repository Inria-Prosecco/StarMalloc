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

extern size_t StarMalloc_threshold;

uint8_t *StarMalloc_malloc(size_t arena_id, size_t size);

uint8_t *StarMalloc_aligned_alloc(size_t arena_id, size_t alignment, size_t size);

bool StarMalloc_free(uint8_t *ptr);

size_t StarMalloc_getsize(uint8_t *ptr);

uint8_t *StarMalloc_realloc(size_t arena_id, uint8_t *ptr, size_t new_size);

uint8_t *StarMalloc_calloc(size_t arena_id, size_t size1, size_t size2);


#define __StarMalloc_H_DEFINED
#endif
