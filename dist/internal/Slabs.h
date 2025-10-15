// SPDX-License-Identifier: Apache-2.0


#ifndef internal_Slabs_H
#define internal_Slabs_H

#include "krmllib.h"

#include "Constants.h"
#include "ArrayList.h"

bool
SlabsFree_deallocate_slab(
  uint8_t *ptr,
  Constants_sc_full_ sc,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs,
  size_t diff_
);

uint8_t
*SlabsAlloc_allocate_slab(
  Constants_sc_full_ sc,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs
);


#define internal_Slabs_H_DEFINED
#endif /* internal_Slabs_H */
