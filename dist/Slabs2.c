// SPDX-License-Identifier: Apache-2.0


#include "internal/Slabs2.h"

#include "internal/ArrayList.h"

typedef bool *slab_metadata;

static uint8_t *allocate_slot(uint8_t *arr, bool *md)
{
  bool b = md[0U];
  md[0U] = !b;
  return arr;
}

static bool deallocate_slot(bool *md)
{
  md[0U] = false;
  return true;
}

static void intro_slab_vprop_empty(uint32_t size_class, uint8_t *arr)
{
  mmap_strict_trap(arr + (size_t)size_class, (size_t)4096U * (size_t)64U - (size_t)size_class);
}

typedef struct tuple4_s
{
  size_t x;
  size_t y;
  size_t z;
  size_t w;
}
tuple4;

static tuple4
update_quarantine2_aux(
  ArrayList_cell *md_region,
  size_t idx1,
  size_t idx5,
  size_t idx6,
  size_t idx7
)
{
  ArrayList_cell cell = md_region[idx6];
  if (cell.next != (size_t)16777217U)
  {
    ArrayList_cell next = md_region[cell.next];
    ArrayList_cell next1 = { .prev = cell.prev, .next = next.next, .data = next.data };
    md_region[cell.next] = next1;
  }
  size_t tl_ = cell.prev;
  if (cell.prev != (size_t)16777217U)
  {
    ArrayList_cell prev = md_region[cell.prev];
    ArrayList_cell prev1 = { .prev = prev.prev, .next = cell.next, .data = prev.data };
    md_region[cell.prev] = prev1;
  }
  size_t hd_;
  if (idx5 == idx6)
    hd_ = cell.next;
  else
    hd_ = idx5;
  size_t sz_ = idx7 - (size_t)1U;
  ArrayListGen_tuple3 idxs = { .x = hd_, .y = tl_, .z = sz_ };
  ArrayList_insert(md_region, idx1, idx6, 0U);
  return ((tuple4){ .x = idx6, .y = idxs.x, .z = idxs.y, .w = idxs.z });
}

static tuple4
update_quarantine2(
  ArrayList_cell *md_region,
  size_t idx1,
  size_t idx5,
  size_t idx6,
  size_t idx7
)
{
  if (idx7 < (size_t)1024U)
    return ((tuple4){ .x = idx1, .y = idx5, .z = idx6, .w = idx7 });
  else
  {
    tuple4 idxs = update_quarantine2_aux(md_region, idx1, idx5, idx6, idx7);
    return idxs;
  }
}

static void update_quarantine3_aux(uint32_t size_class, uint8_t *slab_region, tuple4 idxs)
{
  size_t idx = idxs.x;
  uint8_t *ptr = slab_region;
  size_t shift_size_t = idx * ((size_t)4096U * (size_t)64U);
  mmap_untrap(ptr + shift_size_t, (size_t)size_class);
}

static void
update_quarantine3(uint32_t size_class, uint8_t *slab_region, size_t idx7, tuple4 idxs)
{
  if (!(idx7 < (size_t)1024U))
    update_quarantine3_aux(size_class, slab_region, idxs);
}

static void
deallocate_slab_aux_1_quarantine(
  uint32_t size_class,
  uint8_t *slab_region,
  ArrayList_cell *md_region,
  size_t *r_idxs,
  size_t idx1,
  size_t idx3,
  size_t idx5,
  size_t idx6,
  size_t idx7,
  size_t pos
)
{
  tuple4 idxs = update_quarantine2(md_region, idx1, idx5, idx6, idx7);
  size_t v = ArrayList_remove(md_region, idx3, pos);
  size_t idx3_ = v;
  ArrayList_cell cell = { .prev = (size_t)16777217U, .next = idxs.y, .data = 4U };
  md_region[pos] = cell;
  if (idxs.y != (size_t)16777217U)
  {
    ArrayList_cell cell1 = md_region[idxs.y];
    ArrayList_cell cell2 = { .prev = pos, .next = cell1.next, .data = cell1.data };
    md_region[idxs.y] = cell2;
  }
  size_t tl_;
  if (idxs.y == (size_t)16777217U)
    tl_ = pos;
  else
    tl_ = idxs.z;
  size_t sz_ = idxs.w + (size_t)1U;
  ArrayListGen_tuple2 idxs_ = { .x1 = tl_, .y1 = sz_ };
  update_quarantine3(size_class, slab_region, idx7, idxs);
  r_idxs[0U] = idxs.x;
  r_idxs[2U] = idx3_;
  r_idxs[4U] = pos;
  r_idxs[5U] = idxs_.x1;
  r_idxs[6U] = idxs_.y1;
}

typedef struct __Prims_dtuple2__bool_____Prims_dtuple2__uint8_t_____s
{
  bool *fst;
  uint8_t *snd;
}
__Prims_dtuple2__bool_____Prims_dtuple2__uint8_t____;

static uint8_t
*snd__Prims_dtuple2__bool_____Prims_dtuple2__uint8_t____(
  __Prims_dtuple2__bool_____Prims_dtuple2__uint8_t____ x
)
{
  return x.snd;
}

bool
SlabsFree2_deallocate_slab(
  uint8_t *ptr,
  uint32_t size_class,
  uint8_t *slab_region,
  bool *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs,
  size_t diff_
)
{
  KRML_MAYBE_UNUSED_VAR(ptr);
  size_t md_count_v_ = *md_count;
  size_t idx1_ = r_idxs[0U];
  size_t idx3_ = r_idxs[2U];
  size_t idx5_ = r_idxs[4U];
  size_t idx6_ = r_idxs[5U];
  size_t idx7_ = r_idxs[6U];
  size_t pos = diff_ / ((size_t)4096U * (size_t)64U);
  if (pos < md_count_v_)
  {
    uint32_t status1 = ArrayList_read_in_place(md_region, pos);
    if (status1 == 2U)
    {
      bool *ptr10 = md_bm_region;
      size_t shift_size_t0 = pos;
      bool b = deallocate_slot(ptr10 + shift_size_t0);
      if (b)
      {
        bool *ptr10 = md_bm_region;
        size_t shift_size_t0 = pos;
        uint8_t *ptr1 = slab_region;
        size_t shift_size_t = pos * ((size_t)4096U * (size_t)64U);
        apply_zeroing_u8(snd__Prims_dtuple2__bool_____Prims_dtuple2__uint8_t____((
              (__Prims_dtuple2__bool_____Prims_dtuple2__uint8_t____){
                .fst = ptr10 + shift_size_t0,
                .snd = ptr1 + shift_size_t
              }
            )),
          (size_t)size_class);
        deallocate_slab_aux_1_quarantine(size_class,
          slab_region,
          md_region,
          r_idxs,
          idx1_,
          idx3_,
          idx5_,
          idx6_,
          idx7_,
          pos);
        return b;
      }
      else
        return b;
    }
    else if (status1 == 1U)
      return false;
    else
      return false;
  }
  else
    return false;
}

static void
allocate_slab_aux_3_3_2(
  uint32_t size_class,
  uint8_t *slab_region,
  bool *md_bm_region,
  size_t md_count_v
)
{
  KRML_MAYBE_UNUSED_VAR(md_bm_region);
  uint8_t *ptr = slab_region;
  size_t shift_size_t = md_count_v * ((size_t)4096U * (size_t)64U);
  intro_slab_vprop_empty(size_class, ptr + shift_size_t);
}

static void
allocate_slab_aux_3_3(
  uint32_t size_class,
  uint8_t *slab_region,
  bool *md_bm_region,
  size_t md_count_v
)
{
  allocate_slab_aux_3_3_2(size_class, slab_region, md_bm_region, md_count_v);
}

static void
allocate_slab_aux_3(
  uint32_t size_class,
  uint8_t *slab_region,
  bool *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs,
  size_t md_count_v,
  size_t idx1
)
{
  ArrayList_insert(md_region, idx1, md_count_v, 0U);
  allocate_slab_aux_3_3(size_class, slab_region, md_bm_region, md_count_v);
  size_t v = *md_count;
  *md_count = v + (size_t)1U;
  r_idxs[0U] = md_count_v;
}

typedef struct bounded_tuple__s
{
  size_t x;
  size_t y;
  size_t z;
  size_t w;
}
bounded_tuple_;

static bounded_tuple_
allocate_slab_aux_4_aux1(
  ArrayList_cell *md_region,
  size_t idx1,
  size_t idx5,
  size_t idx6,
  size_t idx7
)
{
  ArrayList_cell cell = md_region[idx6];
  if (cell.next != (size_t)16777217U)
  {
    ArrayList_cell next = md_region[cell.next];
    ArrayList_cell next1 = { .prev = cell.prev, .next = next.next, .data = next.data };
    md_region[cell.next] = next1;
  }
  size_t tl_ = cell.prev;
  if (cell.prev != (size_t)16777217U)
  {
    ArrayList_cell prev = md_region[cell.prev];
    ArrayList_cell prev1 = { .prev = prev.prev, .next = cell.next, .data = prev.data };
    md_region[cell.prev] = prev1;
  }
  size_t hd_;
  if (idx5 == idx6)
    hd_ = cell.next;
  else
    hd_ = idx5;
  size_t sz_ = idx7 - (size_t)1U;
  ArrayListGen_tuple3 idxs = { .x = hd_, .y = tl_, .z = sz_ };
  ArrayList_insert(md_region, idx1, idx6, 0U);
  return ((bounded_tuple_){ .x = idx6, .y = idxs.x, .z = idxs.y, .w = idxs.z });
}

static void
allocate_slab_aux_4_aux2(uint32_t size_class, uint8_t *slab_region, bounded_tuple_ idxs)
{
  uint8_t *ptr = slab_region;
  size_t shift_size_t = idxs.x * ((size_t)4096U * (size_t)64U);
  mmap_untrap(ptr + shift_size_t, (size_t)size_class);
}

static bounded_tuple_
allocate_slab_aux_4(
  uint32_t size_class,
  uint8_t *slab_region,
  ArrayList_cell *md_region,
  size_t *r_idxs,
  size_t idx1,
  size_t idx5,
  size_t idx6,
  size_t idx7
)
{
  bounded_tuple_ r = allocate_slab_aux_4_aux1(md_region, idx1, idx5, idx6, idx7);
  allocate_slab_aux_4_aux2(size_class, slab_region, r);
  r_idxs[0U] = r.x;
  r_idxs[4U] = r.y;
  r_idxs[5U] = r.z;
  r_idxs[6U] = r.w;
  return r;
}

uint8_t
*SlabsAlloc2_allocate_slab(
  uint32_t size_class,
  uint8_t *slab_region,
  bool *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs
)
{
  size_t md_count_v_ = *md_count;
  size_t idx1_ = r_idxs[0U];
  size_t idx3_ = r_idxs[2U];
  size_t idx5_ = r_idxs[4U];
  size_t idx6_ = r_idxs[5U];
  size_t idx7_ = r_idxs[6U];
  if (idx1_ != (size_t)16777217U)
  {
    uint8_t *ptr0 = slab_region;
    size_t shift_size_t0 = idx1_ * ((size_t)4096U * (size_t)64U);
    bool *ptr = md_bm_region;
    size_t shift_size_t = idx1_;
    uint8_t *r = allocate_slot(ptr0 + shift_size_t0, ptr + shift_size_t);
    size_t idx1_0 = ArrayList_remove(md_region, idx1_, idx1_);
    ArrayList_insert(md_region, idx3_, idx1_, 2U);
    r_idxs[0U] = idx1_0;
    r_idxs[2U] = idx1_;
    uint8_t *r0 = r;
    return r0;
  }
  else
  {
    bool b = idx7_ >= (size_t)256U;
    if (b)
    {
      bounded_tuple_
      idxs =
        allocate_slab_aux_4(size_class,
          slab_region,
          md_region,
          r_idxs,
          idx1_,
          idx5_,
          idx6_,
          idx7_);
      uint8_t *ptr0 = slab_region;
      size_t shift_size_t0 = idxs.x * ((size_t)4096U * (size_t)64U);
      bool *ptr = md_bm_region;
      size_t shift_size_t = idxs.x;
      uint8_t *r = allocate_slot(ptr0 + shift_size_t0, ptr + shift_size_t);
      size_t idx1_ = ArrayList_remove(md_region, idxs.x, idxs.x);
      ArrayList_insert(md_region, idx3_, idxs.x, 2U);
      r_idxs[0U] = idx1_;
      r_idxs[2U] = idxs.x;
      uint8_t *r0 = r;
      return r0;
    }
    else
    {
      size_t md_count_v_0 = *md_count;
      bool b1 = md_count_v_0 + (size_t)1U <= (size_t)262144U;
      if (b1)
      {
        allocate_slab_aux_3(size_class,
          slab_region,
          md_bm_region,
          md_region,
          md_count,
          r_idxs,
          md_count_v_,
          idx1_);
        uint8_t *ptr0 = slab_region;
        size_t shift_size_t0 = md_count_v_ * ((size_t)4096U * (size_t)64U);
        bool *ptr = md_bm_region;
        size_t shift_size_t = md_count_v_;
        uint8_t *r = allocate_slot(ptr0 + shift_size_t0, ptr + shift_size_t);
        size_t idx1_ = ArrayList_remove(md_region, md_count_v_, md_count_v_);
        ArrayList_insert(md_region, idx3_, md_count_v_, 2U);
        r_idxs[0U] = idx1_;
        r_idxs[2U] = md_count_v_;
        uint8_t *r0 = r;
        return r0;
      }
      else
        return NULL;
    }
  }
}

