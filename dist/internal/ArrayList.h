// SPDX-License-Identifier: Apache-2.0


#ifndef __internal_ArrayList_H
#define __internal_ArrayList_H

#include "krmllib.h"

#include "../ArrayList.h"

typedef struct ArrayListGen_tuple3_s
{
  size_t x;
  size_t y;
  size_t z;
}
ArrayListGen_tuple3;

typedef struct ArrayListGen_tuple2_s
{
  size_t x1;
  size_t y1;
}
ArrayListGen_tuple2;

uint32_t ArrayList_read_in_place(ArrayList_cell *r, size_t idx);

size_t ArrayList_remove(ArrayList_cell *r, size_t hd1, size_t idx);

void ArrayList_insert(ArrayList_cell *r, size_t hd, size_t idx, uint32_t v);

void
ArrayList_extend_insert(
  size_t n1,
  size_t n2,
  ArrayList_cell *r,
  size_t hd2,
  size_t hd3,
  size_t hd4,
  size_t hd5,
  size_t tl5,
  size_t sz5,
  size_t k,
  uint32_t v1
);


#define __internal_ArrayList_H_DEFINED
#endif
