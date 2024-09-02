// SPDX-License-Identifier: Apache-2.0


#include "PtrdiffWrapper.h"

size_t PtrdiffWrapper_mmap_actual_size(size_t size)
{
  size_t rem = size % (size_t)4096U;
  if (rem != (size_t)0U)
    return size - rem + (size_t)4096U;
  else
    return size;
}

