// SPDX-License-Identifier: Apache-2.0


#ifndef __Constants_H
#define __Constants_H

#include "krmllib.h"

extern uint32_t Constants_page_size;

extern size_t Constants_max_sc_coef;

extern size_t Constants_sc_ex_slab_size;

typedef uint32_t Constants_sc_ex;

#define Constants_Sc 0
#define Constants_Sc_ex 1

typedef uint8_t Constants_sc_union_tags;

typedef struct Constants_sc_union_s
{
  Constants_sc_union_tags tag;
  union {
    uint32_t case_Sc;
    uint32_t case_Sc_ex;
  }
  ;
}
Constants_sc_union;

bool Constants_uu___is_Sc(Constants_sc_union projectee);

bool Constants_uu___is_Sc_ex(Constants_sc_union projectee);

uint32_t Constants_get_sc(Constants_sc_union scu);

uint32_t Constants_get_sc_ex(Constants_sc_union scu);


#define __Constants_H_DEFINED
#endif
