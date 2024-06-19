// SPDX-License-Identifier: Apache-2.0


#include "Bitmap5.h"

bool Bitmap5_bm_get(uint64_t *arr, uint32_t k)
{
  uint32_t k1 = k / 64U;
  size_t k_index = (size_t)k1;
  uint32_t k2 = k % 64U;
  uint64_t x = arr[k_index];
  uint64_t r1 = x >> k2;
  uint64_t r2 = r1 & 1ULL;
  if (r2 == 1ULL)
    return true;
  else
    return false;
}

void Bitmap5_bm_set(uint64_t *arr, uint32_t k)
{
  uint32_t k1 = k / 64U;
  size_t k_index = (size_t)k1;
  uint32_t k2 = k % 64U;
  uint64_t x = arr[k_index];
  uint64_t a = 1ULL << k2;
  uint64_t r = a | x;
  arr[k_index] = r;
}

void Bitmap5_bm_unset(uint64_t *arr, uint32_t k)
{
  uint32_t k1 = k / 64U;
  size_t k_index = (size_t)k1;
  uint32_t k2 = k % 64U;
  uint64_t x = arr[k_index];
  uint64_t a = 1ULL << k2;
  uint64_t c = ~a;
  uint64_t r = c & x;
  arr[k_index] = r;
}

