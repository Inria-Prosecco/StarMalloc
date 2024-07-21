// SPDX-License-Identifier: Apache-2.0


#include "Utils2.h"

size_t Utils2_rounding(uint32_t size_class)
{
  return (size_t)(Constants_nb_slots(size_class) * size_class);
}

uint64_t Utils2_full_n_aux(uint32_t bound)
{
  uint64_t x1 = 1ULL << bound;
  return x1 - 1ULL;
}

uint64_t Utils2_full_n(uint32_t bound)
{
  if (bound == 64U)
    return 18446744073709551615ULL;
  else
  {
    uint64_t x1 = 1ULL << bound;
    return x1 - 1ULL;
  }
}

bool Utils2_is_empty_s(uint32_t size_class, uint64_t *md)
{
  uint32_t bound = Constants_nb_slots(size_class) / 64U;
  uint64_t v0 = md[0U];
  uint64_t v1 = md[1U];
  uint64_t v2 = md[2U];
  uint64_t v3 = md[3U];
  return
    v0
    == 0ULL
    && (bound <= 1U || v1 == 0ULL)
    && (bound <= 2U || v2 == 0ULL)
    && (bound <= 3U || v3 == 0ULL);
}

bool Utils2_is_empty_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q)
{
  uint32_t bound = Constants_nb_slots(size_class) / 64U;
  uint64_t v0 = md[0U];
  uint64_t v1 = md[1U];
  uint64_t v2 = md[2U];
  uint64_t v3 = md[3U];
  uint64_t v0q = md_q[0U];
  uint64_t v1q = md_q[1U];
  uint64_t v2q = md_q[2U];
  uint64_t v3q = md_q[3U];
  return
    (v0 | v0q)
    == 0ULL
    && (bound <= 1U || (v1 | v1q) == 0ULL)
    && (bound <= 2U || (v2 | v2q) == 0ULL)
    && (bound <= 3U || (v3 | v3q) == 0ULL);
}

bool Utils2_has_free_slot_s(uint32_t size_class, uint64_t *md)
{
  uint32_t nb_slots_v = Constants_nb_slots(size_class);
  uint32_t bound = nb_slots_v / 64U;
  uint32_t nb_slots_v_rem = nb_slots_v % 64U;
  uint32_t bound2;
  if (nb_slots_v_rem == 0U)
    bound2 = 64U;
  else
    bound2 = nb_slots_v_rem;
  uint64_t full = Utils2_full_n(bound2);
  uint64_t v0 = md[0U];
  uint64_t v1 = md[1U];
  uint64_t v2 = md[2U];
  uint64_t v3 = md[3U];
  return
    !(v0 == full)
    || (bound > 1U && !(v1 == 18446744073709551615ULL))
    || (bound > 2U && !(v2 == 18446744073709551615ULL))
    || (bound > 3U && !(v3 == 18446744073709551615ULL));
}

bool Utils2_has_free_slot_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q)
{
  uint32_t nb_slots_v = Constants_nb_slots(size_class);
  uint32_t bound = nb_slots_v / 64U;
  uint32_t nb_slots_v_rem = nb_slots_v % 64U;
  uint32_t bound2;
  if (nb_slots_v_rem == 0U)
    bound2 = 64U;
  else
    bound2 = nb_slots_v_rem;
  uint64_t full = Utils2_full_n(bound2);
  uint64_t v0 = md[0U];
  uint64_t v1 = md[1U];
  uint64_t v2 = md[2U];
  uint64_t v3 = md[3U];
  uint64_t v0q = md_q[0U];
  uint64_t v1q = md_q[1U];
  uint64_t v2q = md_q[2U];
  uint64_t v3q = md_q[3U];
  return
    !((v0 | v0q) == full)
    || (bound > 1U && !((v1 | v1q) == 18446744073709551615ULL))
    || (bound > 2U && !((v2 | v2q) == 18446744073709551615ULL))
    || (bound > 3U && !((v3 | v3q) == 18446744073709551615ULL));
}

bool Utils2_is_partial_s(uint32_t size_class, uint64_t *md)
{
  bool b1 = Utils2_has_free_slot_s(size_class, md);
  bool b2 = Utils2_is_empty_s(size_class, md);
  return b1 && !b2;
}

bool Utils2_is_partial_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q)
{
  bool b1 = Utils2_has_free_slot_s2(size_class, md, md_q);
  bool b2 = Utils2_is_empty_s2(size_class, md, md_q);
  return b1 && !b2;
}

bool Utils2_is_full_s(uint32_t size_class, uint64_t *md)
{
  bool b = Utils2_has_free_slot_s(size_class, md);
  return !b;
}

bool Utils2_is_full_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q)
{
  bool b = Utils2_has_free_slot_s2(size_class, md, md_q);
  return !b;
}

void Utils2_reset_to_empty(uint32_t size_class, uint64_t *md)
{
  KRML_MAYBE_UNUSED_VAR(size_class);
  md[0U] = 0ULL;
  md[1U] = 0ULL;
  md[2U] = 0ULL;
  md[3U] = 0ULL;
}

