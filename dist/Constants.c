// SPDX-License-Identifier: Apache-2.0


#include "Constants.h"

uint32_t Constants_page_size = 4096U;

uint32_t Constants_nb_slots(uint32_t size_class)
{
  return 4096U / size_class;
}

