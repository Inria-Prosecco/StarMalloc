// SPDX-License-Identifier: Apache-2.0


#include "SizeClass.h"

#include "Constants.h"
#include "ArrayList.h"
#include "internal/Slabs.h"

uint8_t *SizeClass_allocate_size_class(SizeClass_size_class_struct_ scs)
{
  uint8_t
  *result =
    SlabsAlloc_allocate_slab(scs.size,
      scs.slab_region,
      scs.md_bm_region,
      scs.md_region,
      scs.md_count,
      scs.slabs_idxs);
  return result;
}

bool
SizeClass_deallocate_size_class(SizeClass_size_class_struct_ scs, uint8_t *ptr, size_t diff)
{
  bool
  b =
    SlabsFree_deallocate_slab(ptr,
      scs.size,
      scs.slab_region,
      scs.md_bm_region,
      scs.md_region,
      scs.md_count,
      scs.slabs_idxs,
      diff);
  return b;
}

