// SPDX-License-Identifier: Apache-2.0


#include "internal/Slots.h"

#include "Utils2.h"
#include "ExternUtils.h"
#include "Constants.h"
#include "Bitmap5.h"

static uint8_t *slot_array(Constants_sc_full_ size_class, uint8_t *arr, uint32_t pos)
{
  uint8_t *ptr = arr;
  uint32_t shift = pos * size_class.sc;
  size_t shift_size_t = (size_t)shift;
  return ptr + shift_size_t;
}

static uint8_t
*get_slot_as_returned_value(Constants_sc_full_ size_class, uint8_t *arr, uint32_t pos)
{
  uint8_t *r = slot_array(size_class, arr, pos);
  return r;
}

static uint32_t get_free_slot(Constants_sc_full_ size_class, uint64_t *bitmap)
{
  uint32_t nb_slots_v = Utils2_nb_slots(size_class);
  uint32_t bound = nb_slots_v / 64U;
  uint32_t nb_slots_v_rem = nb_slots_v % 64U;
  uint32_t bound2;
  if (nb_slots_v_rem == 0U)
    bound2 = 64U;
  else
    bound2 = nb_slots_v_rem;
  uint64_t full = Utils2_full_n(bound2);
  uint64_t x1 = bitmap[0U];
  if (x1 == full && bound > 1U)
  {
    uint64_t x2 = bitmap[1U];
    if (x2 == 18446744073709551615ULL && bound > 2U)
    {
      uint64_t x3 = bitmap[2U];
      if (x3 == 18446744073709551615ULL && bound > 3U)
      {
        size_t i2 = (size_t)3U;
        uint64_t x = bitmap[i2];
        uint32_t r = ffs64(x);
        uint32_t r_ = 192U;
        return r + r_;
      }
      else
      {
        size_t i2 = (size_t)2U;
        uint64_t x = bitmap[i2];
        uint32_t r = ffs64(x);
        uint32_t r_ = 128U;
        return r + r_;
      }
    }
    else
    {
      size_t i2 = (size_t)1U;
      uint64_t x = bitmap[i2];
      uint32_t r = ffs64(x);
      uint32_t r_ = 64U;
      return r + r_;
    }
  }
  else
  {
    uint64_t x = bitmap[0U];
    uint32_t r = ffs64(x);
    return r;
  }
}

uint8_t *SlotsAlloc_allocate_slot(Constants_sc_full_ size_class, uint64_t *md, uint8_t *arr)
{
  uint32_t pos = get_free_slot(size_class, md);
  Bitmap5_bm_set(md, pos);
  uint8_t *r = get_slot_as_returned_value(size_class, arr, pos);
  uint8_t *r0 = r;
  return r0;
}

static bool deallocate_slot_aux0(Constants_sc_full_ size_class, uint32_t diff)
{
  size_t diff_sz = (size_t)diff;
  return diff_sz < Utils2_rounding(size_class);
}

static uint32_t deallocate_slot_aux1(Constants_sc_full_ size_class, uint32_t diff)
{
  return diff / size_class.sc;
}

static void deallocate_zeroing(Constants_sc_full_ size_class, uint8_t *ptr)
{
  apply_zeroing_u8(ptr, (size_t)size_class.sc);
}

static bool
deallocate_slot_(Constants_sc_full_ size_class, uint64_t *md, uint8_t *ptr, size_t diff_)
{
  uint32_t diff_u32 = (uint32_t)diff_;
  bool b = deallocate_slot_aux0(size_class, diff_u32);
  if (b)
  {
    uint32_t pos = deallocate_slot_aux1(size_class, diff_u32);
    bool b1 = Bitmap5_bm_get(md, pos);
    if (b1)
    {
      Bitmap5_bm_unset(md, pos);
      deallocate_zeroing(size_class, ptr);
      return true;
    }
    else
      return false;
  }
  else
    return false;
}

static bool fst__bool___(bool x)
{
  return x;
}

bool
SlotsFree_deallocate_slot(
  Constants_sc_full_ size_class,
  uint64_t *md,
  uint8_t *arr,
  uint8_t *ptr,
  size_t diff_
)
{
  KRML_MAYBE_UNUSED_VAR(arr);
  bool r = deallocate_slot_(size_class, md, ptr, diff_);
  if (fst__bool___(r))
    return fst__bool___(r);
  else
    return fst__bool___(r);
}

