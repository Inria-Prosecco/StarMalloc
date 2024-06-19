// SPDX-License-Identifier: Apache-2.0


#include "internal/Slabs.h"

#include "internal/Slots.h"
#include "internal/ArrayList.h"

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

static void update_quarantine3_aux(uint8_t *slab_region, tuple4 idxs)
{
  size_t idx = idxs.x;
  uint8_t *ptr = slab_region;
  size_t page_size_t = (size_t)4096U;
  size_t shift_size_t = idx * page_size_t;
  mmap_untrap(ptr + shift_size_t, (size_t)4096U);
}

static void update_quarantine3(uint8_t *slab_region, size_t idx7, tuple4 idxs)
{
  if (!(idx7 < (size_t)1024U))
    update_quarantine3_aux(slab_region, idxs);
}

bool
SlabsFree_deallocate_slab(
  uint8_t *ptr,
  uint32_t size_class,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs,
  size_t diff_
)
{
  size_t md_count_v_ = *md_count;
  size_t idx1_ = r_idxs[0U];
  size_t idx2_ = r_idxs[1U];
  size_t idx3_ = r_idxs[2U];
  size_t idx5_ = r_idxs[4U];
  size_t idx6_ = r_idxs[5U];
  size_t idx7_ = r_idxs[6U];
  size_t pos = diff_ / (size_t)4096U;
  size_t pos2 = diff_ % (size_t)4096U;
  if (pos < md_count_v_)
  {
    uint32_t status1 = ArrayList_read_in_place(md_region, pos);
    if (status1 == 2U)
    {
      uint64_t *ptr10 = md_bm_region;
      size_t shift_size_t0 = pos * (size_t)4U;
      uint8_t *ptr11 = slab_region;
      size_t page_size_t0 = (size_t)4096U;
      size_t shift_size_t1 = pos * page_size_t0;
      bool
      b =
        SlotsFree_deallocate_slot(size_class,
          ptr10 + shift_size_t0,
          ptr11 + shift_size_t1,
          ptr,
          pos2);
      if (b)
      {
        uint64_t *ptr1 = md_bm_region;
        size_t shift_size_t = pos * (size_t)4U;
        bool r1 = Utils2_is_empty_s(size_class, ptr1 + shift_size_t);
        bool cond = r1;
        if (cond)
        {
          uint8_t *ptr1 = slab_region;
          size_t page_size_t = (size_t)4096U;
          size_t shift_size_t = pos * page_size_t;
          mmap_trap(ptr1 + shift_size_t, (size_t)4096U);
          tuple4 idxs = update_quarantine2(md_region, idx1_, idx5_, idx6_, idx7_);
          size_t v = ArrayList_remove(md_region, idx3_, pos);
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
          update_quarantine3(slab_region, idx7_, idxs);
          r_idxs[0U] = idxs.x;
          r_idxs[2U] = idx3_;
          r_idxs[4U] = pos;
          r_idxs[5U] = idxs_.x1;
          r_idxs[6U] = idxs_.y1;
          return b;
        }
        else
        {
          size_t v = ArrayList_remove(md_region, idx3_, pos);
          size_t idx3_ = v;
          ArrayList_insert(md_region, idx2_, pos, 1U);
          r_idxs[2U] = idx3_;
          r_idxs[1U] = pos;
          return b;
        }
      }
      else
        return b;
    }
    else if (status1 == 1U)
    {
      uint64_t *ptr10 = md_bm_region;
      size_t shift_size_t0 = pos * (size_t)4U;
      uint8_t *ptr11 = slab_region;
      size_t page_size_t0 = (size_t)4096U;
      size_t shift_size_t1 = pos * page_size_t0;
      bool
      b =
        SlotsFree_deallocate_slot(size_class,
          ptr10 + shift_size_t0,
          ptr11 + shift_size_t1,
          ptr,
          pos2);
      if (b)
      {
        uint64_t *ptr1 = md_bm_region;
        size_t shift_size_t = pos * (size_t)4U;
        bool r1 = Utils2_is_empty_s(size_class, ptr1 + shift_size_t);
        bool cond = r1;
        if (cond)
        {
          uint8_t *ptr1 = slab_region;
          size_t page_size_t = (size_t)4096U;
          size_t shift_size_t = pos * page_size_t;
          mmap_trap(ptr1 + shift_size_t, (size_t)4096U);
          tuple4 idxs = update_quarantine2(md_region, idx1_, idx5_, idx6_, idx7_);
          size_t v = ArrayList_remove(md_region, idx2_, pos);
          size_t idx2_ = v;
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
          update_quarantine3(slab_region, idx7_, idxs);
          r_idxs[0U] = idxs.x;
          r_idxs[1U] = idx2_;
          r_idxs[4U] = pos;
          r_idxs[5U] = idxs_.x1;
          r_idxs[6U] = idxs_.y1;
          return b;
        }
        else
          return b;
      }
      else
        return b;
    }
    else
      return false;
  }
  else
    return false;
}

static void allocate_slab_aux_3_3_2_2(uint8_t *slab_region, size_t md_count_v)
{
  uint8_t *ptr = slab_region;
  size_t page_size_t = (size_t)4096U;
  size_t shift_size_t = (md_count_v + (size_t)1U) * page_size_t;
  mmap_strict_trap(ptr + shift_size_t, (size_t)4096U);
}

static void allocate_slab_aux_3_3_2(uint8_t *slab_region, size_t md_count_v)
{
  allocate_slab_aux_3_3_2_2(slab_region, md_count_v);
}

static void allocate_slab_aux_3_3(uint8_t *slab_region, size_t md_count_v)
{
  allocate_slab_aux_3_3_2(slab_region, md_count_v);
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

static void allocate_slab_aux_4_aux2(uint8_t *slab_region, bounded_tuple_ idxs)
{
  uint8_t *ptr = slab_region;
  size_t page_size_t = (size_t)4096U;
  size_t shift_size_t = idxs.x * page_size_t;
  mmap_untrap(ptr + shift_size_t, (size_t)4096U);
}

static bounded_tuple_
allocate_slab_aux_4(
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
  allocate_slab_aux_4_aux2(slab_region, r);
  r_idxs[0U] = r.x;
  r_idxs[4U] = r.y;
  r_idxs[5U] = r.z;
  r_idxs[6U] = r.w;
  return r;
}

uint8_t
*SlabsAlloc_allocate_slab(
  uint32_t size_class,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs
)
{
  size_t md_count_v_ = *md_count;
  size_t idx1_ = r_idxs[0U];
  size_t idx2_ = r_idxs[1U];
  size_t idx3_ = r_idxs[2U];
  size_t idx4_ = r_idxs[3U];
  size_t idx5_ = r_idxs[4U];
  size_t idx6_ = r_idxs[5U];
  size_t idx7_ = r_idxs[6U];
  if (idx2_ != (size_t)16777217U)
  {
    uint64_t *ptr0 = md_bm_region;
    size_t shift_size_t0 = idx2_ * (size_t)4U;
    uint8_t *ptr1 = slab_region;
    size_t page_size_t = (size_t)4096U;
    size_t shift_size_t1 = idx2_ * page_size_t;
    uint8_t *r = SlotsAlloc_allocate_slot(size_class, ptr0 + shift_size_t0, ptr1 + shift_size_t1);
    uint64_t *ptr = md_bm_region;
    size_t shift_size_t = idx2_ * (size_t)4U;
    bool r1 = Utils2_is_full_s(size_class, ptr + shift_size_t);
    bool cond = r1;
    if (cond)
    {
      size_t v = ArrayList_remove(md_region, idx2_, idx2_);
      size_t idx2_0 = v;
      ArrayList_insert(md_region, idx3_, idx2_, 2U);
      r_idxs[1U] = idx2_0;
      r_idxs[2U] = idx2_;
    }
    uint8_t *r0 = r;
    return r0;
  }
  else if (idx1_ != (size_t)16777217U)
  {
    uint64_t *ptr0 = md_bm_region;
    size_t shift_size_t0 = idx1_ * (size_t)4U;
    uint8_t *ptr1 = slab_region;
    size_t page_size_t = (size_t)4096U;
    size_t shift_size_t1 = idx1_ * page_size_t;
    uint8_t *r = SlotsAlloc_allocate_slot(size_class, ptr0 + shift_size_t0, ptr1 + shift_size_t1);
    uint64_t *ptr = md_bm_region;
    size_t shift_size_t = idx1_ * (size_t)4U;
    bool r1 = Utils2_is_full_s(size_class, ptr + shift_size_t);
    bool cond = r1;
    if (cond)
    {
      size_t idx1_0 = ArrayList_remove(md_region, idx1_, idx1_);
      ArrayList_insert(md_region, idx3_, idx1_, 2U);
      r_idxs[0U] = idx1_0;
      r_idxs[2U] = idx1_;
      return r;
    }
    else
    {
      size_t idx1_0 = ArrayList_remove(md_region, idx1_, idx1_);
      ArrayList_insert(md_region, idx2_, idx1_, 1U);
      r_idxs[0U] = idx1_0;
      r_idxs[1U] = idx1_;
      return r;
    }
  }
  else
  {
    bool b = idx7_ >= (size_t)256U;
    if (b)
    {
      bounded_tuple_
      idxs = allocate_slab_aux_4(slab_region, md_region, r_idxs, idx1_, idx5_, idx6_, idx7_);
      uint64_t *ptr0 = md_bm_region;
      size_t shift_size_t0 = idxs.x * (size_t)4U;
      uint8_t *ptr1 = slab_region;
      size_t page_size_t = (size_t)4096U;
      size_t shift_size_t1 = idxs.x * page_size_t;
      uint8_t *r = SlotsAlloc_allocate_slot(size_class, ptr0 + shift_size_t0, ptr1 + shift_size_t1);
      uint64_t *ptr = md_bm_region;
      size_t shift_size_t = idxs.x * (size_t)4U;
      bool r1 = Utils2_is_full_s(size_class, ptr + shift_size_t);
      bool cond = r1;
      if (cond)
      {
        size_t idx1_ = ArrayList_remove(md_region, idxs.x, idxs.x);
        ArrayList_insert(md_region, idx3_, idxs.x, 2U);
        r_idxs[0U] = idx1_;
        r_idxs[2U] = idxs.x;
        return r;
      }
      else
      {
        size_t idx1_ = ArrayList_remove(md_region, idxs.x, idxs.x);
        ArrayList_insert(md_region, idx2_, idxs.x, 1U);
        r_idxs[0U] = idx1_;
        r_idxs[1U] = idxs.x;
        return r;
      }
    }
    else
    {
      size_t md_count_v_0 = *md_count;
      bool b1 = md_count_v_0 + (size_t)2U <= (size_t)16777216U;
      if (b1)
      {
        ArrayList_insert(md_region, idx1_, md_count_v_, 0U);
        ArrayList_extend_insert((size_t)2U,
          (size_t)0U,
          md_region,
          idx2_,
          idx3_,
          idx4_,
          idx5_,
          idx6_,
          idx7_,
          md_count_v_,
          0U);
        ArrayList_insert(md_region, idx4_, md_count_v_ + (size_t)2U - (size_t)1U, 3U);
        allocate_slab_aux_3_3(slab_region, md_count_v_);
        size_t v = *md_count;
        *md_count = v + (size_t)2U;
        r_idxs[0U] = v + (size_t)2U - (size_t)2U;
        r_idxs[3U] = v + (size_t)2U - (size_t)1U;
        uint64_t *ptr0 = md_bm_region;
        size_t shift_size_t0 = (md_count_v_ + (size_t)2U - (size_t)2U) * (size_t)4U;
        uint8_t *ptr1 = slab_region;
        size_t page_size_t = (size_t)4096U;
        size_t shift_size_t1 = (md_count_v_ + (size_t)2U - (size_t)2U) * page_size_t;
        uint8_t
        *r = SlotsAlloc_allocate_slot(size_class, ptr0 + shift_size_t0, ptr1 + shift_size_t1);
        uint64_t *ptr = md_bm_region;
        size_t shift_size_t = (md_count_v_ + (size_t)2U - (size_t)2U) * (size_t)4U;
        bool r1 = Utils2_is_full_s(size_class, ptr + shift_size_t);
        bool cond = r1;
        if (cond)
        {
          size_t
          idx1_ =
            ArrayList_remove(md_region,
              md_count_v_ + (size_t)2U - (size_t)2U,
              md_count_v_ + (size_t)2U - (size_t)2U);
          ArrayList_insert(md_region, idx3_, md_count_v_ + (size_t)2U - (size_t)2U, 2U);
          r_idxs[0U] = idx1_;
          r_idxs[2U] = md_count_v_ + (size_t)2U - (size_t)2U;
          return r;
        }
        else
        {
          size_t
          idx1_ =
            ArrayList_remove(md_region,
              md_count_v_ + (size_t)2U - (size_t)2U,
              md_count_v_ + (size_t)2U - (size_t)2U);
          ArrayList_insert(md_region, idx2_, md_count_v_ + (size_t)2U - (size_t)2U, 1U);
          r_idxs[0U] = idx1_;
          r_idxs[1U] = md_count_v_ + (size_t)2U - (size_t)2U;
          return r;
        }
      }
      else
        return NULL;
    }
  }
}

