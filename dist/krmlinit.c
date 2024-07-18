// SPDX-License-Identifier: Apache-2.0


#include "krmlinit.h"

#include "internal/StarMalloc.h"
#include "internal/Slabs2.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif

void krmlinit_globals(void)
{
  Main_metadata_max_ex = SlabsCommon2_metadata_max_ex;
  Main_sc_slab_region_size = SlabsCommon2_slab_region_size;
  Main_slab_region_size = Main_sc_slab_region_size * (size_t)32U * (size_t)4U;
  Impl_Trees_Types_init_mmap_md_slabs(&Impl_Trees_Types_metadata_slabs);
  init_mmap_md(&metadata);
  Main_Meta_sc_all = Main_Meta_init();
  uint32_t page_size = 32768U;
  StarMalloc_threshold = (size_t)page_size - (size_t)2U;
}

