// SPDX-License-Identifier: Apache-2.0


#include "SizeClass.h"

#include "internal/Slabs2.h"
#include "internal/Slabs.h"

uint8_t *SizeClass_allocate_size_class_sc(SizeClass_size_class_struct_ scs)
{
  uint32_t ite;
  if (scs.size.tag == Constants_Sc)
    ite = scs.size.case_Sc;
  else
    ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  uint8_t
  *result =
    SlabsAlloc_allocate_slab(ite,
      scs.slab_region,
      scs.md_bm_region,
      scs.md_region,
      scs.md_count,
      scs.slabs_idxs);
  return result;
}

bool
SizeClass_deallocate_size_class_sc(SizeClass_size_class_struct_ scs, uint8_t *ptr, size_t diff)
{
  uint32_t ite;
  if (scs.size.tag == Constants_Sc)
    ite = scs.size.case_Sc;
  else
    ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  bool
  b =
    SlabsFree_deallocate_slab(ptr,
      ite,
      scs.slab_region,
      scs.md_bm_region,
      scs.md_region,
      scs.md_count,
      scs.slabs_idxs,
      diff);
  return b;
}

static uint8_t *allocate_size_class_sc_ex(SizeClass_size_class_struct_ scs)
{
  uint32_t ite;
  if (scs.size.tag == Constants_Sc_ex)
    ite = scs.size.case_Sc_ex;
  else
    ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  uint8_t
  *result =
    SlabsAlloc2_allocate_slab(ite,
      scs.slab_region,
      scs.md_bm_region_b,
      scs.md_region,
      scs.md_count,
      scs.slabs_idxs);
  return result;
}

static bool
deallocate_size_class_sc_ex(SizeClass_size_class_struct_ scs, uint8_t *ptr, size_t diff)
{
  uint32_t ite;
  if (scs.size.tag == Constants_Sc_ex)
    ite = scs.size.case_Sc_ex;
  else
    ite = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  bool
  b =
    SlabsFree2_deallocate_slab(ptr,
      ite,
      scs.slab_region,
      scs.md_bm_region_b,
      scs.md_region,
      scs.md_count,
      scs.slabs_idxs,
      diff);
  return b;
}

uint8_t *SizeClass_allocate_size_class(SizeClass_size_class_struct_ scs)
{
  if (scs.is_extended)
  {
    uint8_t *r = allocate_size_class_sc_ex(scs);
    return r;
  }
  else
  {
    uint8_t *r = SizeClass_allocate_size_class_sc(scs);
    return r;
  }
}

bool
SizeClass_deallocate_size_class(SizeClass_size_class_struct_ scs, uint8_t *ptr, size_t diff)
{
  if (scs.is_extended)
  {
    bool r = deallocate_size_class_sc_ex(scs, ptr, diff);
    return r;
  }
  else
  {
    bool r = SizeClass_deallocate_size_class_sc(scs, ptr, diff);
    return r;
  }
}

