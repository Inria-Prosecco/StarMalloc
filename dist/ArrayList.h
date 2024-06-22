// SPDX-License-Identifier: Apache-2.0


#ifndef __ArrayList_H
#define __ArrayList_H

#include "krmllib.h"

typedef struct ArrayList_cell_s
{
  size_t prev;
  size_t next;
  uint32_t data;
}
ArrayList_cell;


#define __ArrayList_H_DEFINED
#endif
