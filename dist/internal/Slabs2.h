// SPDX-License-Identifier: Apache-2.0


#ifndef __internal_Slabs2_H
#define __internal_Slabs2_H

#include "krmllib.h"

#include "internal/ArrayList.h"
#include "MemoryTrap.h"
#include "ExternUtils.h"
#include "ArrayList.h"

extern size_t SlabsCommon2_slab_region_size;

extern size_t SlabsCommon2_slab_size;

extern size_t SlabsCommon2_metadata_max_ex;

bool
SlabsFree2_deallocate_slab(
  uint8_t *ptr,
  uint32_t size_class,
  uint8_t *slab_region,
  bool *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs,
  size_t diff_
);

uint8_t
*SlabsAlloc2_allocate_slab(
  uint32_t size_class,
  uint8_t *slab_region,
  bool *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs
);


#define __internal_Slabs2_H_DEFINED
#endif
