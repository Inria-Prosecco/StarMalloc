// SPDX-License-Identifier: Apache-2.0


#ifndef __internal_Slabs_H
#define __internal_Slabs_H

#include "krmllib.h"

#include "internal/Slots.h"
#include "internal/ArrayList.h"
#include "Utils2.h"
#include "MemoryTrap.h"
#include "Constants.h"
#include "ArrayList.h"

bool
SlabsFree_deallocate_slab(
  uint8_t *ptr,
  uint32_t size_class,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  uint64_t *md_bm_region_q,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs,
  size_t diff_
);

uint8_t
*SlabsAlloc_allocate_slab(
  uint32_t size_class,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  uint64_t *md_bm_region_q,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs
);


#define __internal_Slabs_H_DEFINED
#endif
