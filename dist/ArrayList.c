// SPDX-License-Identifier: Apache-2.0


#include "internal/ArrayList.h"

uint32_t ArrayList_read_in_place(ArrayList_cell *r, size_t idx)
{
  ArrayList_cell res = r[idx];
  return res.data;
}

size_t ArrayList_remove(ArrayList_cell *r, size_t hd1, size_t idx)
{
  ArrayList_cell cell1 = r[idx];
  if (cell1.next != (size_t)16777217U)
  {
    ArrayList_cell next = r[cell1.next];
    ArrayList_cell next1 = { .prev = cell1.prev, .next = next.next, .data = next.data };
    r[cell1.next] = next1;
  }
  if (cell1.prev != (size_t)16777217U)
  {
    ArrayList_cell prev = r[cell1.prev];
    ArrayList_cell prev1 = { .prev = prev.prev, .next = cell1.next, .data = prev.data };
    r[cell1.prev] = prev1;
  }
  if (hd1 == idx)
    return cell1.next;
  else
    return hd1;
}

void ArrayList_insert(ArrayList_cell *r, size_t hd, size_t idx, uint32_t v)
{
  ArrayList_cell cell1 = { .prev = (size_t)16777217U, .next = hd, .data = v };
  r[idx] = cell1;
  if (hd != (size_t)16777217U)
  {
    ArrayList_cell cell2 = r[hd];
    ArrayList_cell cell3 = { .prev = idx, .next = cell2.next, .data = cell2.data };
    r[hd] = cell3;
  }
}

static void extend_insert__uint32_t(size_t n2, ArrayList_cell *r, size_t k, uint32_t v1)
{
  for (size_t i = (size_t)0U; i < n2; i++)
  {
    ArrayList_cell cell1 = { .prev = (size_t)16777217U, .next = k + i, .data = v1 };
    r[k + i + (size_t)1U] = cell1;
    if (k + i != (size_t)16777217U)
    {
      ArrayList_cell cell2 = r[k + i];
      ArrayList_cell cell3 = { .prev = k + i + (size_t)1U, .next = cell2.next, .data = cell2.data };
      r[k + i] = cell3;
    }
  }
}

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
)
{
  KRML_MAYBE_UNUSED_VAR(n1);
  KRML_MAYBE_UNUSED_VAR(hd2);
  KRML_MAYBE_UNUSED_VAR(hd3);
  KRML_MAYBE_UNUSED_VAR(hd4);
  KRML_MAYBE_UNUSED_VAR(hd5);
  KRML_MAYBE_UNUSED_VAR(tl5);
  KRML_MAYBE_UNUSED_VAR(sz5);
  extend_insert__uint32_t(n2, r, k, v1);
}

