// SPDX-License-Identifier: Apache-2.0


#include "krmlinit.h"

#include "internal/StarMalloc.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif

void krmlinit_globals(void)
{
  Impl_Trees_Types_init_mmap_md_slabs(&Impl_Trees_Types_metadata_slabs);
  init_mmap_md(&metadata);
  Main_Meta_sc_all = Main_Meta_init();
}

