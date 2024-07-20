// SPDX-License-Identifier: Apache-2.0


#include "SlotsCommon.h"

uint8_t *SlotsCommon_slot_array(uint32_t size_class, uint8_t *arr, uint32_t pos)
{
  uint8_t *ptr = arr;
  uint32_t shift = pos * size_class;
  size_t shift_size_t = (size_t)shift;
  return ptr + shift_size_t;
}

