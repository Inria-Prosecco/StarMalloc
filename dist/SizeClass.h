// SPDX-License-Identifier: Apache-2.0


#ifndef SizeClass_H
#define SizeClass_H

#include "krmllib.h"

#include "Constants.h"
#include "ArrayList.h"

typedef struct SizeClass_size_class_struct__s
{
  Constants_sc_full_ size;
  size_t *slabs_idxs;
  size_t *md_count;
  uint8_t *slab_region;
  uint64_t *md_bm_region;
  ArrayList_cell *md_region;
}
SizeClass_size_class_struct_;

typedef SizeClass_size_class_struct_ SizeClass_size_class_struct;

uint8_t *SizeClass_allocate_size_class(SizeClass_size_class_struct_ scs);

bool
SizeClass_deallocate_size_class(SizeClass_size_class_struct_ scs, uint8_t *ptr, size_t diff);


#define SizeClass_H_DEFINED
#endif /* SizeClass_H */
