// SPDX-License-Identifier: Apache-2.0


#ifndef ArrayList_H
#define ArrayList_H

#include "krmllib.h"

typedef struct ArrayList_cell_s
{
  size_t prev;
  size_t next;
  uint32_t data;
}
ArrayList_cell;


#define ArrayList_H_DEFINED
#endif /* ArrayList_H */
