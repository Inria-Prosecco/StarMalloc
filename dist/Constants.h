// SPDX-License-Identifier: Apache-2.0


#ifndef Constants_H
#define Constants_H

#include "krmllib.h"

extern uint32_t Constants_page_size;

extern uint32_t Constants_max_slab_size;

typedef struct Constants_sc_full__s
{
  uint32_t sc;
  uint32_t slab_size;
  size_t md_max;
}
Constants_sc_full_;


#define Constants_H_DEFINED
#endif /* Constants_H */
