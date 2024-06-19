// SPDX-License-Identifier: Apache-2.0


#ifndef __internal_Slots_H
#define __internal_Slots_H

#include "krmllib.h"

#include "Utils2.h"
#include "Bitmap5.h"

uint8_t *SlotsAlloc_allocate_slot(uint32_t size_class, uint64_t *md, uint8_t *arr);

bool
SlotsFree_deallocate_slot(
  uint32_t size_class,
  uint64_t *md,
  uint8_t *arr,
  uint8_t *ptr,
  size_t diff_
);


#define __internal_Slots_H_DEFINED
#endif
