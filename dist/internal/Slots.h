// SPDX-License-Identifier: Apache-2.0


#ifndef internal_Slots_H
#define internal_Slots_H

#include "krmllib.h"

#include "Constants.h"

uint8_t *SlotsAlloc_allocate_slot(Constants_sc_full_ size_class, uint64_t *md, uint8_t *arr);

bool
SlotsFree_deallocate_slot(
  Constants_sc_full_ size_class,
  uint64_t *md,
  uint8_t *arr,
  uint8_t *ptr,
  size_t diff_
);


#define internal_Slots_H_DEFINED
#endif /* internal_Slots_H */
