// SPDX-License-Identifier: Apache-2.0


#include "SizeClassSelection.h"

#include "internal/Prims.h"

uint32_t SizeClassSelection_log2u64(uint64_t x)
{
  uint32_t r = clz(x);
  return 63U - r;
}

krml_checked_int_t SizeClassSelection_sort(krml_checked_int_t x)
{
  if (Prims_op_LessThanOrEqual(x, (krml_checked_int_t)1))
    return (krml_checked_int_t)0;
  else if (Prims_op_LessThanOrEqual(x, (krml_checked_int_t)26))
    return (krml_checked_int_t)1;
  else
    return (krml_checked_int_t)2;
}

uint32_t SizeClassSelection_inv_impl(uint32_t bound_input, uint32_t bound_len, uint32_t x)
{
  KRML_MAYBE_UNUSED_VAR(bound_input);
  KRML_MAYBE_UNUSED_VAR(bound_len);
  if (x <= 16U)
    return 0U;
  else if (x <= 32U)
    return 1U;
  else if (x <= 64U)
    return 2U;
  else if (x <= 4096U)
  {
    uint32_t x_as_u32 = x;
    uint64_t x_as_u64 = (uint64_t)x_as_u32;
    uint32_t log = SizeClassSelection_log2u64(x_as_u64);
    uint32_t align = 1U << log;
    uint32_t align2 = 1U << (log - 2U);
    uint32_t y0 = log - 6U;
    uint32_t v = align2 - 1U;
    uint32_t x_ = x_as_u32 - align + v;
    uint32_t z0 = x_ >> (log - 2U);
    uint32_t y = y0;
    uint32_t z = z0;
    return y * 4U + z + 2U;
  }
  else
  {
    uint32_t v = 4095U;
    uint32_t x_ = x + v;
    return (x_ >> 12U) + 25U;
  }
}

