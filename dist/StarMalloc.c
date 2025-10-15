// SPDX-License-Identifier: Apache-2.0


#include "internal/StarMalloc.h"

#include "Steel_SpinLock.h"
#include "SizeClassSelection.h"
#include "SizeClass.h"
#include "PtrdiffWrapper.h"
#include "Mman.h"
#include "ExternUtils.h"
#include "Constants.h"
#include "ArrayList.h"

uint32_t Impl_Trees_Cast_M_avl_data_size = 64U;

extern int64_t Impl_Trees_Cast_M_cmp(Impl_Trees_Cast_M_data uu___, Impl_Trees_Cast_M_data x0);

extern uint8_t *Impl_Trees_Cast_M_ref_node__to__array_u8(Impl_Trees_Cast_M_node *x);

extern Impl_Trees_Cast_M_node *Impl_Trees_Cast_M_array_u8__to__ref_node(uint8_t *arr);

static void init_idxs(size_t *r_idxs)
{
  r_idxs[0U] = (size_t)16777217U;
  r_idxs[1U] = (size_t)16777217U;
  r_idxs[2U] = (size_t)16777217U;
  r_idxs[3U] = (size_t)16777217U;
  r_idxs[4U] = (size_t)16777217U;
  r_idxs[5U] = (size_t)16777217U;
  r_idxs[6U] = (size_t)0U;
}

static size_t full_slab_region_size = (size_t)12919261626368U;

static void
init_size_class(
  size_t k,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  ArrayList_cell *md_region,
  size_class *size_classes,
  const Constants_sc_full_ *sizes
)
{
  Constants_sc_full_ size = sizes[k];
  static_assert(UINT32_MAX <= SIZE_MAX);
  uint8_t *slab_region_ = slab_region + (size_t)16777216U * (size_t)4096U * k;
  uint64_t *md_bm_region_ = md_bm_region + (size_t)67108864U * k;
  ArrayList_cell *md_region_ = md_region + (size_t)16777216U * k;
  size_t *r_idxs = mmap_array_us_init((size_t)7U);
  init_idxs(r_idxs);
  size_t *md_count = mmap_ptr_us_init();
  *md_count = (size_t)0U;
  SizeClass_size_class_struct_
  scs =
    {
      .size = size, .slabs_idxs = r_idxs, .md_count = md_count, .slab_region = slab_region_,
      .md_bm_region = md_bm_region_, .md_region = md_region_
    };
  SizeClass_size_class_struct_ data = scs;
  Steel_SpinLock_new_lock(&size_classes[k].lock);
  size_classes[k].data = data;
}

Constants_sc_full_ Impl_Trees_Types_sc_avl;

void Impl_Trees_Types_init_mmap_md_slabs(Impl_Trees_Types_mmap_md_slabs *ret)
{
  size_t slab_region_size = (size_t)16777216U * (size_t)4096U;
  uint8_t *slab_region = mmap_u8_init(slab_region_size);
  size_t md_bm_region_size = (size_t)67108864U;
  size_t md_region_size = (size_t)16777216U;
  uint64_t *md_bm_region = mmap_u64_init(md_bm_region_size);
  ArrayList_cell *md_region = mmap_cell_status_init(md_region_size);
  size_t *r_idxs = mmap_array_us_init((size_t)7U);
  init_idxs(r_idxs);
  size_t *md_count = mmap_ptr_us_init();
  *md_count = (size_t)0U;
  SizeClass_size_class_struct_
  scs =
    {
      .size = Impl_Trees_Types_sc_avl, .slabs_idxs = r_idxs, .md_count = md_count,
      .slab_region = slab_region, .md_bm_region = md_bm_region, .md_region = md_region
    };
  SizeClass_size_class_struct_ scs0 = scs;
  Steel_SpinLock_new_lock(&ret->lock);
  ret->slab_region = slab_region;
  ret->scs = scs0;
}

Impl_Trees_Types_mmap_md_slabs Impl_Trees_Types_metadata_slabs;

extern Impl_Trees_Cast_M_node
*FatalError_die_from_avl_node_malloc_failure(Impl_Trees_Cast_M_node x, uint8_t *ptr);

extern void FatalError_die_from_avl_node_free_failure(uint8_t *ptr);

extern void FatalError_die_from_malloc_zeroing_check_failure(uint8_t *ptr);

extern void FatalError_die_from_realloc_invalid_previous_alloc(uint8_t *ptr);

extern void FatalError_die_from_realloc_free_failure(uint8_t *ptr);

extern Impl_Trees_Cast_M_node **mmap_ptr_metadata_init(void);

bool Impl_BST_M_member(Impl_Trees_Cast_M_node *ptr, Impl_Trees_Cast_M_data v)
{
  if (ptr == NULL)
    return false;
  else
  {
    Impl_Trees_Cast_M_node node = *ptr;
    Impl_Trees_Cast_M_data data = node.data;
    int64_t delta = Impl_Trees_Cast_M_cmp(v, data);
    if (delta == (int64_t)0)
      return true;
    else if (delta < (int64_t)0)
    {
      bool b = Impl_BST_M_member(node.left, v);
      return b;
    }
    else
    {
      bool b = Impl_BST_M_member(node.right, v);
      return b;
    }
  }
}

static Impl_Trees_Cast_M_node *rotate_left_right(Impl_Trees_Cast_M_node *ptr)
{
  Impl_Trees_Cast_M_node x_node = *ptr;
  Impl_Trees_Cast_M_data x = x_node.data;
  Impl_Trees_Cast_M_node z_node = *x_node.left;
  Impl_Trees_Cast_M_data z = z_node.data;
  Impl_Trees_Cast_M_node y_node = *z_node.right;
  Impl_Trees_Cast_M_data y = y_node.data;
  uint64_t s10;
  if (z_node.left == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.left;
    s10 = node.size;
  }
  uint64_t s20;
  if (y_node.left == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.left;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (z_node.left == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.left;
    h10 = node.height;
  }
  uint64_t h20;
  if (y_node.left == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.left;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Cast_M_node
  n = { .data = z, .left = z_node.left, .right = y_node.left, .size = s, .height = h };
  *x_node.left = n;
  Impl_Trees_Cast_M_node *new_z = x_node.left;
  uint64_t s11;
  if (y_node.right == NULL)
    s11 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.right;
    s11 = node.size;
  }
  uint64_t s21;
  if (x_node.right == NULL)
    s21 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.right;
    s21 = node.size;
  }
  uint64_t s0 = s11 + s21 + 1ULL;
  uint64_t h11;
  if (y_node.right == NULL)
    h11 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.right;
    h11 = node.height;
  }
  uint64_t h21;
  if (x_node.right == NULL)
    h21 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.right;
    h21 = node.height;
  }
  uint64_t ite1;
  if (h11 > h21)
    ite1 = h11;
  else
    ite1 = h21;
  uint64_t h0 = ite1 + 1ULL;
  Impl_Trees_Cast_M_node
  n0 = { .data = x, .left = y_node.right, .right = x_node.right, .size = s0, .height = h0 };
  *ptr = n0;
  Impl_Trees_Cast_M_node *new_x = ptr;
  uint64_t s1;
  if (new_z == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_z;
    s1 = node.size;
  }
  uint64_t s2;
  if (new_x == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_x;
    s2 = node.size;
  }
  uint64_t s3 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (new_z == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_z;
    h1 = node.height;
  }
  uint64_t h2;
  if (new_x == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_x;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h3 = ite + 1ULL;
  Impl_Trees_Cast_M_node
  n1 = { .data = y, .left = new_z, .right = new_x, .size = s3, .height = h3 };
  *z_node.right = n1;
  Impl_Trees_Cast_M_node *new_y = z_node.right;
  return new_y;
}

static Impl_Trees_Cast_M_node *rotate_right_left(Impl_Trees_Cast_M_node *ptr)
{
  Impl_Trees_Cast_M_node x_node = *ptr;
  Impl_Trees_Cast_M_data x = x_node.data;
  Impl_Trees_Cast_M_node z_node = *x_node.right;
  Impl_Trees_Cast_M_data z = z_node.data;
  Impl_Trees_Cast_M_node y_node = *z_node.left;
  Impl_Trees_Cast_M_data y = y_node.data;
  uint64_t s10;
  if (x_node.left == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.left;
    s10 = node.size;
  }
  uint64_t s20;
  if (y_node.left == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.left;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (x_node.left == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.left;
    h10 = node.height;
  }
  uint64_t h20;
  if (y_node.left == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.left;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Cast_M_node
  n = { .data = x, .left = x_node.left, .right = y_node.left, .size = s, .height = h };
  *ptr = n;
  Impl_Trees_Cast_M_node *new_x = ptr;
  uint64_t s11;
  if (y_node.right == NULL)
    s11 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.right;
    s11 = node.size;
  }
  uint64_t s21;
  if (z_node.right == NULL)
    s21 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.right;
    s21 = node.size;
  }
  uint64_t s0 = s11 + s21 + 1ULL;
  uint64_t h11;
  if (y_node.right == NULL)
    h11 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *y_node.right;
    h11 = node.height;
  }
  uint64_t h21;
  if (z_node.right == NULL)
    h21 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.right;
    h21 = node.height;
  }
  uint64_t ite1;
  if (h11 > h21)
    ite1 = h11;
  else
    ite1 = h21;
  uint64_t h0 = ite1 + 1ULL;
  Impl_Trees_Cast_M_node
  n0 = { .data = z, .left = y_node.right, .right = z_node.right, .size = s0, .height = h0 };
  *x_node.right = n0;
  Impl_Trees_Cast_M_node *new_z = x_node.right;
  uint64_t s1;
  if (new_x == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_x;
    s1 = node.size;
  }
  uint64_t s2;
  if (new_z == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_z;
    s2 = node.size;
  }
  uint64_t s3 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (new_x == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_x;
    h1 = node.height;
  }
  uint64_t h2;
  if (new_z == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_z;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h3 = ite + 1ULL;
  Impl_Trees_Cast_M_node
  n1 = { .data = y, .left = new_x, .right = new_z, .size = s3, .height = h3 };
  *z_node.left = n1;
  Impl_Trees_Cast_M_node *new_y = z_node.left;
  return new_y;
}

static Impl_Trees_Cast_M_node *rotate_left(Impl_Trees_Cast_M_node *ptr)
{
  Impl_Trees_Cast_M_node x_node = *ptr;
  Impl_Trees_Cast_M_data x = x_node.data;
  Impl_Trees_Cast_M_node z_node = *x_node.right;
  Impl_Trees_Cast_M_data z = z_node.data;
  uint64_t s10;
  if (x_node.left == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.left;
    s10 = node.size;
  }
  uint64_t s20;
  if (z_node.left == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.left;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (x_node.left == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.left;
    h10 = node.height;
  }
  uint64_t h20;
  if (z_node.left == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.left;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Cast_M_node
  n = { .data = x, .left = x_node.left, .right = z_node.left, .size = s, .height = h };
  *ptr = n;
  Impl_Trees_Cast_M_node *new_subnode = ptr;
  uint64_t s1;
  if (new_subnode == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_subnode;
    s1 = node.size;
  }
  uint64_t s2;
  if (z_node.right == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.right;
    s2 = node.size;
  }
  uint64_t s0 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (new_subnode == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_subnode;
    h1 = node.height;
  }
  uint64_t h2;
  if (z_node.right == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.right;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h0 = ite + 1ULL;
  Impl_Trees_Cast_M_node
  n0 = { .data = z, .left = new_subnode, .right = z_node.right, .size = s0, .height = h0 };
  *x_node.right = n0;
  Impl_Trees_Cast_M_node *new_node = x_node.right;
  return new_node;
}

static Impl_Trees_Cast_M_node *rotate_right(Impl_Trees_Cast_M_node *ptr)
{
  Impl_Trees_Cast_M_node x_node = *ptr;
  Impl_Trees_Cast_M_data x = x_node.data;
  Impl_Trees_Cast_M_node z_node = *x_node.left;
  Impl_Trees_Cast_M_data z = z_node.data;
  uint64_t s10;
  if (z_node.right == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.right;
    s10 = node.size;
  }
  uint64_t s20;
  if (x_node.right == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.right;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (z_node.right == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.right;
    h10 = node.height;
  }
  uint64_t h20;
  if (x_node.right == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *x_node.right;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Cast_M_node
  n = { .data = x, .left = z_node.right, .right = x_node.right, .size = s, .height = h };
  *ptr = n;
  Impl_Trees_Cast_M_node *new_subnode = ptr;
  uint64_t s1;
  if (z_node.left == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.left;
    s1 = node.size;
  }
  uint64_t s2;
  if (new_subnode == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_subnode;
    s2 = node.size;
  }
  uint64_t s0 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (z_node.left == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *z_node.left;
    h1 = node.height;
  }
  uint64_t h2;
  if (new_subnode == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *new_subnode;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h0 = ite + 1ULL;
  Impl_Trees_Cast_M_node
  n0 = { .data = z, .left = z_node.left, .right = new_subnode, .size = s0, .height = h0 };
  *x_node.left = n0;
  Impl_Trees_Cast_M_node *new_node = x_node.left;
  return new_node;
}

static bool is_balanced_local(Impl_Trees_Cast_M_node *ptr)
{
  if (ptr == NULL)
    return true;
  else
  {
    Impl_Trees_Cast_M_node node = *ptr;
    uint64_t lh;
    if (node.left == NULL)
      lh = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *node.left;
      lh = node1.height;
    }
    uint64_t rh;
    if (node.right == NULL)
      rh = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *node.right;
      rh = node1.height;
    }
    bool b1 = rh + 1ULL >= lh;
    bool b2 = lh + 1ULL >= rh;
    return b1 && b2;
  }
}

static Impl_Trees_Cast_M_node *rebalance_avl(Impl_Trees_Cast_M_node *ptr)
{
  if (is_balanced_local(ptr))
    return ptr;
  else
  {
    Impl_Trees_Cast_M_node node = *ptr;
    uint64_t lh;
    if (node.left == NULL)
      lh = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *node.left;
      lh = node1.height;
    }
    uint64_t rh;
    if (node.right == NULL)
      rh = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *node.right;
      rh = node1.height;
    }
    if (lh > rh + 1ULL)
    {
      Impl_Trees_Cast_M_node l_node = *node.left;
      uint64_t llh;
      if (l_node.left == NULL)
        llh = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *l_node.left;
        llh = node1.height;
      }
      uint64_t lrh;
      if (l_node.right == NULL)
        lrh = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *l_node.right;
        lrh = node1.height;
      }
      if (lrh > llh)
        return rotate_left_right(ptr);
      else
        return rotate_right(ptr);
    }
    else if (rh > lh + 1ULL)
    {
      Impl_Trees_Cast_M_node r_node = *node.right;
      uint64_t rlh;
      if (r_node.left == NULL)
        rlh = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *r_node.left;
        rlh = node1.height;
      }
      uint64_t rrh;
      if (r_node.right == NULL)
        rrh = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *r_node.right;
        rrh = node1.height;
      }
      if (rlh > rrh)
        return rotate_right_left(ptr);
      else
        return rotate_left(ptr);
    }
    else
      return ptr;
  }
}

Impl_Trees_Cast_M_node
*Impl_AVL_M_insert_avl(
  Impl_Trees_Cast_M_node *(*f1)(Impl_Trees_Cast_M_node x0),
  void (*f2)(Impl_Trees_Cast_M_node *x0),
  bool r,
  Impl_Trees_Cast_M_node *ptr,
  Impl_Trees_Cast_M_data new_data
)
{
  if (ptr == NULL)
  {
    Impl_Trees_Cast_M_node *l = NULL;
    Impl_Trees_Cast_M_node *r1 = NULL;
    uint64_t sr = 1ULL;
    uint64_t hr = 1ULL;
    Impl_Trees_Cast_M_node
    n = { .data = new_data, .left = l, .right = r1, .size = sr, .height = hr };
    Impl_Trees_Cast_M_node *ptr1 = f1(n);
    return ptr1;
  }
  else
  {
    Impl_Trees_Cast_M_node node = *ptr;
    int64_t delta = Impl_Trees_Cast_M_cmp(node.data, new_data);
    if (delta == (int64_t)0)
      if (r)
      {
        Impl_Trees_Cast_M_node
        new_node =
          {
            .data = new_data, .left = node.left, .right = node.right, .size = node.size,
            .height = node.height
          };
        *ptr = new_node;
        return ptr;
      }
      else
        return ptr;
    else if (delta > (int64_t)0)
    {
      Impl_Trees_Cast_M_node *new_left = Impl_AVL_M_insert_avl(f1, f2, r, node.left, new_data);
      uint64_t s1;
      if (new_left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (node.right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (new_left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (node.right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Cast_M_node
      n = { .data = node.data, .left = new_left, .right = node.right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Cast_M_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
    else
    {
      Impl_Trees_Cast_M_node *new_right = Impl_AVL_M_insert_avl(f1, f2, r, node.right, new_data);
      uint64_t s1;
      if (node.left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (new_right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (node.left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (new_right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Cast_M_node
      n = { .data = node.data, .left = node.left, .right = new_right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Cast_M_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
  }
}

Impl_AVL_M_result
Impl_AVL_M_remove_leftmost_avl(
  Impl_Trees_Cast_M_node *(*f1)(Impl_Trees_Cast_M_node x0),
  void (*f2)(Impl_Trees_Cast_M_node *x0),
  Impl_Trees_Cast_M_node *ptr
)
{
  Impl_Trees_Cast_M_node node = *ptr;
  if (node.left == NULL)
  {
    Impl_Trees_Cast_M_data data = node.data;
    f2(ptr);
    return ((Impl_AVL_M_result){ .ptr = node.right, .data = data });
  }
  else
  {
    Impl_AVL_M_result r0 = Impl_AVL_M_remove_leftmost_avl(f1, f2, node.left);
    uint64_t s1;
    if (r0.ptr == NULL)
      s1 = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *r0.ptr;
      s1 = node1.size;
    }
    uint64_t s2;
    if (node.right == NULL)
      s2 = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *node.right;
      s2 = node1.size;
    }
    uint64_t s = s1 + s2 + 1ULL;
    uint64_t h1;
    if (r0.ptr == NULL)
      h1 = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *r0.ptr;
      h1 = node1.height;
    }
    uint64_t h2;
    if (node.right == NULL)
      h2 = 0ULL;
    else
    {
      Impl_Trees_Cast_M_node node1 = *node.right;
      h2 = node1.height;
    }
    uint64_t ite;
    if (h1 > h2)
      ite = h1;
    else
      ite = h2;
    uint64_t h = ite + 1ULL;
    Impl_Trees_Cast_M_node
    n = { .data = node.data, .left = r0.ptr, .right = node.right, .size = s, .height = h };
    *ptr = n;
    Impl_Trees_Cast_M_node *new_ptr = ptr;
    Impl_Trees_Cast_M_node *new_ptr1 = rebalance_avl(new_ptr);
    return ((Impl_AVL_M_result){ .ptr = new_ptr1, .data = r0.data });
  }
}

Impl_Trees_Cast_M_node
*Impl_AVL_M_delete_avl(
  Impl_Trees_Cast_M_node *(*f1)(Impl_Trees_Cast_M_node x0),
  void (*f2)(Impl_Trees_Cast_M_node *x0),
  Impl_Trees_Cast_M_node *ptr,
  Impl_Trees_Cast_M_data data_to_rm
)
{
  if (ptr == NULL)
    return ptr;
  else
  {
    Impl_Trees_Cast_M_node node = *ptr;
    int64_t delta = Impl_Trees_Cast_M_cmp(data_to_rm, node.data);
    if (delta == (int64_t)0)
    {
      Impl_Trees_Cast_M_node node1 = *ptr;
      if (node1.right == NULL)
      {
        f2(ptr);
        return node1.left;
      }
      else if (node1.left == NULL)
      {
        f2(ptr);
        return node1.right;
      }
      else
      {
        Impl_AVL_M_result r0 = Impl_AVL_M_remove_leftmost_avl(f1, f2, node1.right);
        uint64_t s1;
        if (node1.left == NULL)
          s1 = 0ULL;
        else
        {
          Impl_Trees_Cast_M_node node2 = *node1.left;
          s1 = node2.size;
        }
        uint64_t s2;
        if (r0.ptr == NULL)
          s2 = 0ULL;
        else
        {
          Impl_Trees_Cast_M_node node2 = *r0.ptr;
          s2 = node2.size;
        }
        uint64_t s = s1 + s2 + 1ULL;
        uint64_t h1;
        if (node1.left == NULL)
          h1 = 0ULL;
        else
        {
          Impl_Trees_Cast_M_node node2 = *node1.left;
          h1 = node2.height;
        }
        uint64_t h2;
        if (r0.ptr == NULL)
          h2 = 0ULL;
        else
        {
          Impl_Trees_Cast_M_node node2 = *r0.ptr;
          h2 = node2.height;
        }
        uint64_t ite;
        if (h1 > h2)
          ite = h1;
        else
          ite = h2;
        uint64_t h = ite + 1ULL;
        Impl_Trees_Cast_M_node
        n = { .data = r0.data, .left = node1.left, .right = r0.ptr, .size = s, .height = h };
        *ptr = n;
        Impl_Trees_Cast_M_node *new_ptr = ptr;
        Impl_Trees_Cast_M_node *new_ptr1 = rebalance_avl(new_ptr);
        return new_ptr1;
      }
    }
    else if (delta < (int64_t)0)
    {
      Impl_Trees_Cast_M_node *new_left = Impl_AVL_M_delete_avl(f1, f2, node.left, data_to_rm);
      uint64_t s1;
      if (new_left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (node.right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (new_left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (node.right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Cast_M_node
      n = { .data = node.data, .left = new_left, .right = node.right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Cast_M_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
    else
    {
      Impl_Trees_Cast_M_node *new_right = Impl_AVL_M_delete_avl(f1, f2, node.right, data_to_rm);
      uint64_t s1;
      if (node.left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (new_right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (node.left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *node.left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (new_right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Cast_M_node node1 = *new_right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Cast_M_node
      n = { .data = node.data, .left = node.left, .right = new_right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Cast_M_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
  }
}

static size_t snd__Prims_dtuple2__uint8_t_____size_t(Impl_Trees_Cast_M_data x)
{
  return x.snd;
}

FStar_Pervasives_Native_option__size_t
Map_M_find(Impl_Trees_Cast_M_node *ptr, Impl_Trees_Cast_M_data v)
{
  if (ptr == NULL)
    return ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
  else
  {
    Impl_Trees_Cast_M_node node = *ptr;
    int64_t delta = Impl_Trees_Cast_M_cmp(v, node.data);
    if (delta == (int64_t)0)
    {
      size_t r = snd__Prims_dtuple2__uint8_t_____size_t(node.data);
      return
        ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = r });
    }
    else if (delta < (int64_t)0)
    {
      FStar_Pervasives_Native_option__size_t r = Map_M_find(node.left, v);
      return r;
    }
    else
    {
      FStar_Pervasives_Native_option__size_t r = Map_M_find(node.right, v);
      return r;
    }
  }
}

void init_mmap_md(mmap_md *ret)
{
  Impl_Trees_Cast_M_node **ptr = mmap_ptr_metadata_init();
  Impl_Trees_Cast_M_node *tree = NULL;
  *ptr = tree;
  Steel_SpinLock_new_lock(&ret->lock);
  ret->data = ptr;
}

mmap_md metadata;

static Impl_Trees_Cast_M_node *trees_malloc2(Impl_Trees_Cast_M_node x)
{
  Steel_SpinLock_acquire(&Impl_Trees_Types_metadata_slabs.lock);
  uint8_t *ptr = SizeClass_allocate_size_class(Impl_Trees_Types_metadata_slabs.scs);
  Impl_Trees_Cast_M_node *r0;
  if (ptr == NULL)
  {
    Impl_Trees_Cast_M_node *r = FatalError_die_from_avl_node_malloc_failure(x, ptr);
    r0 = r;
  }
  else
  {
    Impl_Trees_Cast_M_node *r_ = Impl_Trees_Cast_M_array_u8__to__ref_node(ptr);
    *r_ = x;
    r0 = r_;
  }
  Steel_SpinLock_release(&Impl_Trees_Types_metadata_slabs.lock);
  Impl_Trees_Cast_M_node *r = r0;
  return r;
}

static void trees_free2(Impl_Trees_Cast_M_node *r)
{
  Steel_SpinLock_acquire(&Impl_Trees_Types_metadata_slabs.lock);
  uint8_t *ptr = Impl_Trees_Cast_M_ref_node__to__array_u8(r);
  uint8_t *pt0 = ptr;
  uint8_t *pt1 = Impl_Trees_Types_metadata_slabs.slab_region;
  ptrdiff_t diff = pt0 - pt1;
  size_t diff_sz = (size_t)diff;
  bool b = SizeClass_deallocate_size_class(Impl_Trees_Types_metadata_slabs.scs, ptr, diff_sz);
  if (!b)
    FatalError_die_from_avl_node_free_failure(ptr);
  Steel_SpinLock_release(&Impl_Trees_Types_metadata_slabs.lock);
}

static uint8_t *large_malloc(size_t size)
{
  Steel_SpinLock_acquire(&metadata.lock);
  Impl_Trees_Cast_M_node *md_v0 = *metadata.data;
  uint64_t md_size;
  if (md_v0 == NULL)
    md_size = 0ULL;
  else
  {
    Impl_Trees_Cast_M_node node = *md_v0;
    md_size = node.size;
  }
  uint8_t *r;
  if (md_size < 18446744073709551615ULL)
  {
    Impl_Trees_Cast_M_node *md_v = *metadata.data;
    uint8_t *ptr0 = mmap_u8(size);
    uint8_t *ptr;
    if (ptr0 == NULL)
      ptr = ptr0;
    else
    {
      size_t size_ = PtrdiffWrapper_mmap_actual_size(size);
      bool b = Impl_BST_M_member(md_v, ((Impl_Trees_Cast_M_data){ .fst = ptr0, .snd = size_ }));
      if (b)
        ptr = NULL;
      else
      {
        Impl_Trees_Cast_M_node
        *md_v_ =
          Impl_AVL_M_insert_avl(trees_malloc2,
            trees_free2,
            false,
            md_v,
            ((Impl_Trees_Cast_M_data){ .fst = ptr0, .snd = size_ }));
        *metadata.data = md_v_;
        ptr = ptr0;
      }
    }
    r = ptr;
  }
  else
    r = NULL;
  Steel_SpinLock_release(&metadata.lock);
  uint8_t *r0 = r;
  return r0;
}

static bool uu___is_Some__size_t(FStar_Pervasives_Native_option__size_t projectee)
{
  if (projectee.tag == FStar_Pervasives_Native_Some)
    return true;
  else
    return false;
}

static bool large_free(uint8_t *ptr)
{
  Steel_SpinLock_acquire(&metadata.lock);
  Impl_Trees_Cast_M_node *md_v = *metadata.data;
  Impl_Trees_Cast_M_data k_elem = { .fst = ptr, .snd = (size_t)0U };
  FStar_Pervasives_Native_option__size_t size = Map_M_find(md_v, k_elem);
  bool r;
  if (uu___is_Some__size_t(size))
  {
    size_t size1;
    if (size.tag == FStar_Pervasives_Native_Some)
      size1 = size.v;
    else
      size1 = KRML_EABORT(size_t, "unreachable (pattern matches are exhaustive in F*)");
    munmap_u8(ptr, size1);
    Impl_Trees_Cast_M_node
    *md_v_ =
      Impl_AVL_M_delete_avl(trees_malloc2,
        trees_free2,
        md_v,
        ((Impl_Trees_Cast_M_data){ .fst = ptr, .snd = size1 }));
    *metadata.data = md_v_;
    r = true;
  }
  else
    r = false;
  Steel_SpinLock_release(&metadata.lock);
  bool b = r;
  return b;
}

static size_t large_getsize_aux(Impl_Trees_Cast_M_node **metadata1, uint8_t *ptr)
{
  Impl_Trees_Cast_M_node *md_v = *metadata1;
  FStar_Pervasives_Native_option__size_t
  size = Map_M_find(md_v, ((Impl_Trees_Cast_M_data){ .fst = ptr, .snd = (size_t)0U }));
  if (uu___is_Some__size_t(size))
    if (size.tag == FStar_Pervasives_Native_Some)
      return size.v;
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else
    return (size_t)0U;
}

static size_t large_getsize(uint8_t *ptr)
{
  Steel_SpinLock_acquire(&metadata.lock);
  size_t r = large_getsize_aux(metadata.data, ptr);
  Steel_SpinLock_release(&metadata.lock);
  size_t r0 = r;
  return r0;
}

static const
Constants_sc_full_
sizes[188U] =
  {
    { .sc = 16U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 32U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 64U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 80U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 96U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 112U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 128U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 160U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 192U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 224U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 256U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 320U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 384U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 448U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 512U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 640U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 768U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 896U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1024U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1280U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1536U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1792U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2048U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2560U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3072U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3584U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 4096U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 5120U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 6144U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 7168U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 8192U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 10240U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 12288U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 14336U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 16384U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 20480U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 24576U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 28672U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 32768U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 40960U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 49152U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 57344U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 65536U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 81920U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 98304U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 114688U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 131072U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 16U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 32U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 64U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 80U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 96U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 112U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 128U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 160U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 192U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 224U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 256U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 320U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 384U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 448U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 512U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 640U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 768U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 896U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1024U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1280U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1536U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1792U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2048U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2560U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3072U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3584U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 4096U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 5120U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 6144U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 7168U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 8192U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 10240U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 12288U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 14336U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 16384U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 20480U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 24576U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 28672U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 32768U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 40960U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 49152U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 57344U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 65536U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 81920U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 98304U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 114688U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 131072U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 16U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 32U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 64U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 80U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 96U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 112U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 128U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 160U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 192U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 224U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 256U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 320U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 384U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 448U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 512U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 640U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 768U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 896U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1024U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1280U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1536U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1792U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2048U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2560U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3072U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3584U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 4096U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 5120U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 6144U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 7168U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 8192U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 10240U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 12288U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 14336U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 16384U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 20480U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 24576U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 28672U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 32768U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 40960U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 49152U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 57344U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 65536U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 81920U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 98304U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 114688U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 131072U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 16U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 32U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 64U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 80U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 96U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 112U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 128U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 160U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 192U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 224U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 256U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 320U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 384U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 448U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 512U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 640U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 768U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 896U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1024U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1280U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1536U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 1792U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2048U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 2560U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3072U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 3584U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 4096U, .slab_size = 4096U, .md_max = (size_t)16777216U },
    { .sc = 5120U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 6144U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 7168U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 8192U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 10240U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 12288U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 14336U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 16384U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 20480U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 24576U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 28672U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 32768U, .slab_size = 32768U, .md_max = (size_t)2097152U },
    { .sc = 40960U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 49152U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 57344U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 65536U, .slab_size = 65536U, .md_max = (size_t)1048576U },
    { .sc = 81920U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 98304U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 114688U, .slab_size = 131072U, .md_max = (size_t)524288U },
    { .sc = 131072U, .slab_size = 131072U, .md_max = (size_t)524288U }
  };

Main_Meta_size_classes_all Main_Meta_init(void)
{
  uint8_t *slab_region = mmap_u8_init((size_t)16777216U * (size_t)4096U * (size_t)188U);
  uint64_t *md_bm_region = mmap_u64_init((size_t)12616466432U);
  ArrayList_cell *md_region = mmap_cell_status_init((size_t)3154116608U);
  size_class *size_classes = mmap_sc_init((size_t)188U);
  init_size_class((size_t)0U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)1U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)2U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)3U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)4U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)5U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)6U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)7U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)8U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)9U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)10U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)11U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)12U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)13U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)14U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)15U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)16U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)17U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)18U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)19U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)20U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)21U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)22U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)23U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)24U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)25U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)26U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)27U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)28U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)29U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)30U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)31U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)32U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)33U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)34U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)35U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)36U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)37U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)38U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)39U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)40U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)41U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)42U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)43U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)44U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)45U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)46U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)47U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)48U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)49U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)50U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)51U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)52U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)53U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)54U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)55U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)56U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)57U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)58U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)59U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)60U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)61U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)62U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)63U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)64U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)65U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)66U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)67U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)68U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)69U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)70U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)71U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)72U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)73U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)74U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)75U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)76U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)77U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)78U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)79U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)80U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)81U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)82U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)83U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)84U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)85U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)86U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)87U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)88U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)89U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)90U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)91U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)92U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)93U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)94U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)95U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)96U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)97U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)98U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)99U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)100U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)101U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)102U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)103U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)104U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)105U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)106U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)107U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)108U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)109U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)110U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)111U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)112U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)113U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)114U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)115U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)116U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)117U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)118U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)119U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)120U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)121U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)122U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)123U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)124U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)125U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)126U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)127U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)128U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)129U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)130U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)131U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)132U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)133U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)134U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)135U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)136U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)137U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)138U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)139U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)140U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)141U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)142U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)143U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)144U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)145U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)146U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)147U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)148U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)149U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)150U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)151U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)152U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)153U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)154U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)155U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)156U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)157U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)158U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)159U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)160U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)161U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)162U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)163U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)164U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)165U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)166U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)167U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)168U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)169U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)170U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)171U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)172U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)173U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)174U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)175U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)176U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)177U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)178U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)179U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)180U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)181U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)182U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)183U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)184U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)185U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)186U, slab_region, md_bm_region, md_region, size_classes, sizes);
  init_size_class((size_t)187U, slab_region, md_bm_region, md_region, size_classes, sizes);
  return
    ((Main_Meta_size_classes_all){ .size_classes = size_classes, .slab_region = slab_region });
}

Main_Meta_size_classes_all Main_Meta_sc_all;

static uint8_t *allocate_size_class(SizeClass_size_class_struct_ scs)
{
  uint8_t *r = SizeClass_allocate_size_class(scs);
  return r;
}

static uint8_t *slab_malloc(size_t arena_id, uint32_t bytes)
{
  uint32_t r0 = SizeClassSelection_inv_impl(bytes + 2U);
  size_t i = (size_t)r0;
  Constants_sc_full_ size = sizes[arena_id * (size_t)47U + i];
  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + i].lock);
  uint8_t
  *r = allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + i].data);
  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + i].lock);
  uint8_t *ptr = r;
  uint8_t *ptr0 = ptr;
  if (!(ptr0 == NULL))
  {
    ptr0[(size_t)(size.sc - 2U)] = 42U;
    ptr0[(size_t)(size.sc - 1U)] = 23U;
  }
  return ptr0;
}

static uint8_t *slab_aligned_alloc(size_t arena_id, uint32_t alignment, uint32_t bytes)
{
  Constants_sc_full_ size = sizes[arena_id * (size_t)47U + (size_t)0U];
  bool b = size.slab_size % size.sc == 0U;
  if (b && bytes <= size.sc - 2U && alignment <= size.sc)
  {
    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)0U].lock);
    uint8_t
    *r =
      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)0U].data);
    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)0U].lock);
    uint8_t *ptr = r;
    uint8_t *r0 = ptr;
    if (!(r0 == NULL))
    {
      r0[(size_t)(size.sc - 2U)] = 42U;
      r0[(size_t)(size.sc - 1U)] = 23U;
    }
    return r0;
  }
  else
  {
    Constants_sc_full_ size1 = sizes[arena_id * (size_t)47U + (size_t)1U];
    bool b1 = size1.slab_size % size1.sc == 0U;
    if (b1 && bytes <= size1.sc - 2U && alignment <= size1.sc)
    {
      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)1U].lock);
      uint8_t
      *r =
        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)1U].data);
      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)1U].lock);
      uint8_t *ptr = r;
      uint8_t *r0 = ptr;
      if (!(r0 == NULL))
      {
        r0[(size_t)(size1.sc - 2U)] = 42U;
        r0[(size_t)(size1.sc - 1U)] = 23U;
      }
      return r0;
    }
    else
    {
      Constants_sc_full_ size2 = sizes[arena_id * (size_t)47U + (size_t)2U];
      bool b2 = size2.slab_size % size2.sc == 0U;
      if (b2 && bytes <= size2.sc - 2U && alignment <= size2.sc)
      {
        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)2U].lock);
        uint8_t
        *r =
          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)2U].data);
        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)2U].lock);
        uint8_t *ptr = r;
        uint8_t *r0 = ptr;
        if (!(r0 == NULL))
        {
          r0[(size_t)(size2.sc - 2U)] = 42U;
          r0[(size_t)(size2.sc - 1U)] = 23U;
        }
        return r0;
      }
      else
      {
        Constants_sc_full_ size3 = sizes[arena_id * (size_t)47U + (size_t)3U];
        bool b3 = size3.slab_size % size3.sc == 0U;
        if (b3 && bytes <= size3.sc - 2U && alignment <= size3.sc)
        {
          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)3U].lock);
          uint8_t
          *r =
            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)3U].data);
          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)3U].lock);
          uint8_t *ptr = r;
          uint8_t *r0 = ptr;
          if (!(r0 == NULL))
          {
            r0[(size_t)(size3.sc - 2U)] = 42U;
            r0[(size_t)(size3.sc - 1U)] = 23U;
          }
          return r0;
        }
        else
        {
          Constants_sc_full_ size4 = sizes[arena_id * (size_t)47U + (size_t)4U];
          bool b4 = size4.slab_size % size4.sc == 0U;
          if (b4 && bytes <= size4.sc - 2U && alignment <= size4.sc)
          {
            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                (size_t)4U].lock);
            uint8_t
            *r =
              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U + (size_t)4U].data);
            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                (size_t)4U].lock);
            uint8_t *ptr = r;
            uint8_t *r0 = ptr;
            if (!(r0 == NULL))
            {
              r0[(size_t)(size4.sc - 2U)] = 42U;
              r0[(size_t)(size4.sc - 1U)] = 23U;
            }
            return r0;
          }
          else
          {
            Constants_sc_full_ size5 = sizes[arena_id * (size_t)47U + (size_t)5U];
            bool b5 = size5.slab_size % size5.sc == 0U;
            if (b5 && bytes <= size5.sc - 2U && alignment <= size5.sc)
            {
              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                  (size_t)5U].lock);
              uint8_t
              *r =
                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                    (size_t)5U].data);
              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                  (size_t)5U].lock);
              uint8_t *ptr = r;
              uint8_t *r0 = ptr;
              if (!(r0 == NULL))
              {
                r0[(size_t)(size5.sc - 2U)] = 42U;
                r0[(size_t)(size5.sc - 1U)] = 23U;
              }
              return r0;
            }
            else
            {
              Constants_sc_full_ size6 = sizes[arena_id * (size_t)47U + (size_t)6U];
              bool b6 = size6.slab_size % size6.sc == 0U;
              if (b6 && bytes <= size6.sc - 2U && alignment <= size6.sc)
              {
                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                    (size_t)6U].lock);
                uint8_t
                *r =
                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                      (size_t)6U].data);
                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                    (size_t)6U].lock);
                uint8_t *ptr = r;
                uint8_t *r0 = ptr;
                if (!(r0 == NULL))
                {
                  r0[(size_t)(size6.sc - 2U)] = 42U;
                  r0[(size_t)(size6.sc - 1U)] = 23U;
                }
                return r0;
              }
              else
              {
                Constants_sc_full_ size7 = sizes[arena_id * (size_t)47U + (size_t)7U];
                bool b7 = size7.slab_size % size7.sc == 0U;
                if (b7 && bytes <= size7.sc - 2U && alignment <= size7.sc)
                {
                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                      (size_t)7U].lock);
                  uint8_t
                  *r =
                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                        (size_t)7U].data);
                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                      (size_t)7U].lock);
                  uint8_t *ptr = r;
                  uint8_t *r0 = ptr;
                  if (!(r0 == NULL))
                  {
                    r0[(size_t)(size7.sc - 2U)] = 42U;
                    r0[(size_t)(size7.sc - 1U)] = 23U;
                  }
                  return r0;
                }
                else
                {
                  Constants_sc_full_ size8 = sizes[arena_id * (size_t)47U + (size_t)8U];
                  bool b8 = size8.slab_size % size8.sc == 0U;
                  if (b8 && bytes <= size8.sc - 2U && alignment <= size8.sc)
                  {
                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                        (size_t)8U].lock);
                    uint8_t
                    *r =
                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                          (size_t)8U].data);
                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                        (size_t)8U].lock);
                    uint8_t *ptr = r;
                    uint8_t *r0 = ptr;
                    if (!(r0 == NULL))
                    {
                      r0[(size_t)(size8.sc - 2U)] = 42U;
                      r0[(size_t)(size8.sc - 1U)] = 23U;
                    }
                    return r0;
                  }
                  else
                  {
                    Constants_sc_full_ size9 = sizes[arena_id * (size_t)47U + (size_t)9U];
                    bool b9 = size9.slab_size % size9.sc == 0U;
                    if (b9 && bytes <= size9.sc - 2U && alignment <= size9.sc)
                    {
                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                          (size_t)9U].lock);
                      uint8_t
                      *r =
                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                            (size_t)9U].data);
                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                          (size_t)9U].lock);
                      uint8_t *ptr = r;
                      uint8_t *r0 = ptr;
                      if (!(r0 == NULL))
                      {
                        r0[(size_t)(size9.sc - 2U)] = 42U;
                        r0[(size_t)(size9.sc - 1U)] = 23U;
                      }
                      return r0;
                    }
                    else
                    {
                      Constants_sc_full_ size10 = sizes[arena_id * (size_t)47U + (size_t)10U];
                      bool b10 = size10.slab_size % size10.sc == 0U;
                      if (b10 && bytes <= size10.sc - 2U && alignment <= size10.sc)
                      {
                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U
                          + (size_t)10U].lock);
                        uint8_t
                        *r =
                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U +
                              (size_t)10U].data);
                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)47U
                          + (size_t)10U].lock);
                        uint8_t *ptr = r;
                        uint8_t *r0 = ptr;
                        if (!(r0 == NULL))
                        {
                          r0[(size_t)(size10.sc - 2U)] = 42U;
                          r0[(size_t)(size10.sc - 1U)] = 23U;
                        }
                        return r0;
                      }
                      else
                      {
                        Constants_sc_full_ size11 = sizes[arena_id * (size_t)47U + (size_t)11U];
                        bool b11 = size11.slab_size % size11.sc == 0U;
                        if (b11 && bytes <= size11.sc - 2U && alignment <= size11.sc)
                        {
                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id *
                              (size_t)47U
                            + (size_t)11U].lock);
                          uint8_t
                          *r =
                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)47U
                              + (size_t)11U].data);
                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id *
                              (size_t)47U
                            + (size_t)11U].lock);
                          uint8_t *ptr = r;
                          uint8_t *r0 = ptr;
                          if (!(r0 == NULL))
                          {
                            r0[(size_t)(size11.sc - 2U)] = 42U;
                            r0[(size_t)(size11.sc - 1U)] = 23U;
                          }
                          return r0;
                        }
                        else
                        {
                          Constants_sc_full_ size12 = sizes[arena_id * (size_t)47U + (size_t)12U];
                          bool b12 = size12.slab_size % size12.sc == 0U;
                          if (b12 && bytes <= size12.sc - 2U && alignment <= size12.sc)
                          {
                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id *
                                (size_t)47U
                              + (size_t)12U].lock);
                            uint8_t
                            *r =
                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id *
                                  (size_t)47U
                                + (size_t)12U].data);
                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id *
                                (size_t)47U
                              + (size_t)12U].lock);
                            uint8_t *ptr = r;
                            uint8_t *r0 = ptr;
                            if (!(r0 == NULL))
                            {
                              r0[(size_t)(size12.sc - 2U)] = 42U;
                              r0[(size_t)(size12.sc - 1U)] = 23U;
                            }
                            return r0;
                          }
                          else
                          {
                            Constants_sc_full_ size13 = sizes[arena_id * (size_t)47U + (size_t)13U];
                            bool b13 = size13.slab_size % size13.sc == 0U;
                            if (b13 && bytes <= size13.sc - 2U && alignment <= size13.sc)
                            {
                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id *
                                  (size_t)47U
                                + (size_t)13U].lock);
                              uint8_t
                              *r =
                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id *
                                    (size_t)47U
                                  + (size_t)13U].data);
                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id *
                                  (size_t)47U
                                + (size_t)13U].lock);
                              uint8_t *ptr = r;
                              uint8_t *r0 = ptr;
                              if (!(r0 == NULL))
                              {
                                r0[(size_t)(size13.sc - 2U)] = 42U;
                                r0[(size_t)(size13.sc - 1U)] = 23U;
                              }
                              return r0;
                            }
                            else
                            {
                              Constants_sc_full_
                              size14 = sizes[arena_id * (size_t)47U + (size_t)14U];
                              bool b14 = size14.slab_size % size14.sc == 0U;
                              if (b14 && bytes <= size14.sc - 2U && alignment <= size14.sc)
                              {
                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id *
                                    (size_t)47U
                                  + (size_t)14U].lock);
                                uint8_t
                                *r =
                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id *
                                      (size_t)47U
                                    + (size_t)14U].data);
                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id *
                                    (size_t)47U
                                  + (size_t)14U].lock);
                                uint8_t *ptr = r;
                                uint8_t *r0 = ptr;
                                if (!(r0 == NULL))
                                {
                                  r0[(size_t)(size14.sc - 2U)] = 42U;
                                  r0[(size_t)(size14.sc - 1U)] = 23U;
                                }
                                return r0;
                              }
                              else
                              {
                                Constants_sc_full_
                                size15 = sizes[arena_id * (size_t)47U + (size_t)15U];
                                bool b15 = size15.slab_size % size15.sc == 0U;
                                if (b15 && bytes <= size15.sc - 2U && alignment <= size15.sc)
                                {
                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id *
                                      (size_t)47U
                                    + (size_t)15U].lock);
                                  uint8_t
                                  *r =
                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id *
                                        (size_t)47U
                                      + (size_t)15U].data);
                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id *
                                      (size_t)47U
                                    + (size_t)15U].lock);
                                  uint8_t *ptr = r;
                                  uint8_t *r0 = ptr;
                                  if (!(r0 == NULL))
                                  {
                                    r0[(size_t)(size15.sc - 2U)] = 42U;
                                    r0[(size_t)(size15.sc - 1U)] = 23U;
                                  }
                                  return r0;
                                }
                                else
                                {
                                  Constants_sc_full_
                                  size16 = sizes[arena_id * (size_t)47U + (size_t)16U];
                                  bool b16 = size16.slab_size % size16.sc == 0U;
                                  if (b16 && bytes <= size16.sc - 2U && alignment <= size16.sc)
                                  {
                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id *
                                        (size_t)47U
                                      + (size_t)16U].lock);
                                    uint8_t
                                    *r =
                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id *
                                          (size_t)47U
                                        + (size_t)16U].data);
                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id *
                                        (size_t)47U
                                      + (size_t)16U].lock);
                                    uint8_t *ptr = r;
                                    uint8_t *r0 = ptr;
                                    if (!(r0 == NULL))
                                    {
                                      r0[(size_t)(size16.sc - 2U)] = 42U;
                                      r0[(size_t)(size16.sc - 1U)] = 23U;
                                    }
                                    return r0;
                                  }
                                  else
                                  {
                                    Constants_sc_full_
                                    size17 = sizes[arena_id * (size_t)47U + (size_t)17U];
                                    bool b17 = size17.slab_size % size17.sc == 0U;
                                    if (b17 && bytes <= size17.sc - 2U && alignment <= size17.sc)
                                    {
                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)47U
                                        + (size_t)17U].lock);
                                      uint8_t
                                      *r =
                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id *
                                            (size_t)47U
                                          + (size_t)17U].data);
                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)47U
                                        + (size_t)17U].lock);
                                      uint8_t *ptr = r;
                                      uint8_t *r0 = ptr;
                                      if (!(r0 == NULL))
                                      {
                                        r0[(size_t)(size17.sc - 2U)] = 42U;
                                        r0[(size_t)(size17.sc - 1U)] = 23U;
                                      }
                                      return r0;
                                    }
                                    else
                                    {
                                      Constants_sc_full_
                                      size18 = sizes[arena_id * (size_t)47U + (size_t)18U];
                                      bool b18 = size18.slab_size % size18.sc == 0U;
                                      if (b18 && bytes <= size18.sc - 2U && alignment <= size18.sc)
                                      {
                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)47U
                                          + (size_t)18U].lock);
                                        uint8_t
                                        *r =
                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)47U
                                            + (size_t)18U].data);
                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)47U
                                          + (size_t)18U].lock);
                                        uint8_t *ptr = r;
                                        uint8_t *r0 = ptr;
                                        if (!(r0 == NULL))
                                        {
                                          r0[(size_t)(size18.sc - 2U)] = 42U;
                                          r0[(size_t)(size18.sc - 1U)] = 23U;
                                        }
                                        return r0;
                                      }
                                      else
                                      {
                                        Constants_sc_full_
                                        size19 = sizes[arena_id * (size_t)47U + (size_t)19U];
                                        bool b19 = size19.slab_size % size19.sc == 0U;
                                        if
                                        (b19 && bytes <= size19.sc - 2U && alignment <= size19.sc)
                                        {
                                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)47U
                                            + (size_t)19U].lock);
                                          uint8_t
                                          *r =
                                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)47U
                                              + (size_t)19U].data);
                                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)47U
                                            + (size_t)19U].lock);
                                          uint8_t *ptr = r;
                                          uint8_t *r0 = ptr;
                                          if (!(r0 == NULL))
                                          {
                                            r0[(size_t)(size19.sc - 2U)] = 42U;
                                            r0[(size_t)(size19.sc - 1U)] = 23U;
                                          }
                                          return r0;
                                        }
                                        else
                                        {
                                          Constants_sc_full_
                                          size20 = sizes[arena_id * (size_t)47U + (size_t)20U];
                                          bool b20 = size20.slab_size % size20.sc == 0U;
                                          if
                                          (b20 && bytes <= size20.sc - 2U && alignment <= size20.sc)
                                          {
                                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)47U
                                              + (size_t)20U].lock);
                                            uint8_t
                                            *r =
                                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)47U
                                                + (size_t)20U].data);
                                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)47U
                                              + (size_t)20U].lock);
                                            uint8_t *ptr = r;
                                            uint8_t *r0 = ptr;
                                            if (!(r0 == NULL))
                                            {
                                              r0[(size_t)(size20.sc - 2U)] = 42U;
                                              r0[(size_t)(size20.sc - 1U)] = 23U;
                                            }
                                            return r0;
                                          }
                                          else
                                          {
                                            Constants_sc_full_
                                            size21 = sizes[arena_id * (size_t)47U + (size_t)21U];
                                            bool b21 = size21.slab_size % size21.sc == 0U;
                                            if
                                            (
                                              b21 && bytes <= size21.sc - 2U &&
                                                alignment <= size21.sc
                                            )
                                            {
                                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)47U
                                                + (size_t)21U].lock);
                                              uint8_t
                                              *r =
                                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)47U
                                                  + (size_t)21U].data);
                                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)47U
                                                + (size_t)21U].lock);
                                              uint8_t *ptr = r;
                                              uint8_t *r0 = ptr;
                                              if (!(r0 == NULL))
                                              {
                                                r0[(size_t)(size21.sc - 2U)] = 42U;
                                                r0[(size_t)(size21.sc - 1U)] = 23U;
                                              }
                                              return r0;
                                            }
                                            else
                                            {
                                              Constants_sc_full_
                                              size22 = sizes[arena_id * (size_t)47U + (size_t)22U];
                                              bool b22 = size22.slab_size % size22.sc == 0U;
                                              if
                                              (
                                                b22 && bytes <= size22.sc - 2U &&
                                                  alignment <= size22.sc
                                              )
                                              {
                                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)47U
                                                  + (size_t)22U].lock);
                                                uint8_t
                                                *r =
                                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)47U
                                                    + (size_t)22U].data);
                                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)47U
                                                  + (size_t)22U].lock);
                                                uint8_t *ptr = r;
                                                uint8_t *r0 = ptr;
                                                if (!(r0 == NULL))
                                                {
                                                  r0[(size_t)(size22.sc - 2U)] = 42U;
                                                  r0[(size_t)(size22.sc - 1U)] = 23U;
                                                }
                                                return r0;
                                              }
                                              else
                                              {
                                                Constants_sc_full_
                                                size23 = sizes[arena_id * (size_t)47U + (size_t)23U];
                                                bool b23 = size23.slab_size % size23.sc == 0U;
                                                if
                                                (
                                                  b23 && bytes <= size23.sc - 2U &&
                                                    alignment <= size23.sc
                                                )
                                                {
                                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)47U
                                                    + (size_t)23U].lock);
                                                  uint8_t
                                                  *r =
                                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)47U
                                                      + (size_t)23U].data);
                                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)47U
                                                    + (size_t)23U].lock);
                                                  uint8_t *ptr = r;
                                                  uint8_t *r0 = ptr;
                                                  if (!(r0 == NULL))
                                                  {
                                                    r0[(size_t)(size23.sc - 2U)] = 42U;
                                                    r0[(size_t)(size23.sc - 1U)] = 23U;
                                                  }
                                                  return r0;
                                                }
                                                else
                                                {
                                                  Constants_sc_full_
                                                  size24 =
                                                    sizes[arena_id * (size_t)47U + (size_t)24U];
                                                  bool b24 = size24.slab_size % size24.sc == 0U;
                                                  if
                                                  (
                                                    b24 && bytes <= size24.sc - 2U &&
                                                      alignment <= size24.sc
                                                  )
                                                  {
                                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)47U
                                                      + (size_t)24U].lock);
                                                    uint8_t
                                                    *r =
                                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)47U
                                                        + (size_t)24U].data);
                                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)47U
                                                      + (size_t)24U].lock);
                                                    uint8_t *ptr = r;
                                                    uint8_t *r0 = ptr;
                                                    if (!(r0 == NULL))
                                                    {
                                                      r0[(size_t)(size24.sc - 2U)] = 42U;
                                                      r0[(size_t)(size24.sc - 1U)] = 23U;
                                                    }
                                                    return r0;
                                                  }
                                                  else
                                                  {
                                                    Constants_sc_full_
                                                    size25 =
                                                      sizes[arena_id * (size_t)47U + (size_t)25U];
                                                    bool b25 = size25.slab_size % size25.sc == 0U;
                                                    if
                                                    (
                                                      b25 && bytes <= size25.sc - 2U &&
                                                        alignment <= size25.sc
                                                    )
                                                    {
                                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)47U
                                                        + (size_t)25U].lock);
                                                      uint8_t
                                                      *r =
                                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)47U
                                                          + (size_t)25U].data);
                                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)47U
                                                        + (size_t)25U].lock);
                                                      uint8_t *ptr = r;
                                                      uint8_t *r0 = ptr;
                                                      if (!(r0 == NULL))
                                                      {
                                                        r0[(size_t)(size25.sc - 2U)] = 42U;
                                                        r0[(size_t)(size25.sc - 1U)] = 23U;
                                                      }
                                                      return r0;
                                                    }
                                                    else
                                                    {
                                                      Constants_sc_full_
                                                      size26 =
                                                        sizes[arena_id * (size_t)47U + (size_t)26U];
                                                      bool b26 = size26.slab_size % size26.sc == 0U;
                                                      if
                                                      (
                                                        b26 && bytes <= size26.sc - 2U &&
                                                          alignment <= size26.sc
                                                      )
                                                      {
                                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)47U
                                                          + (size_t)26U].lock);
                                                        uint8_t
                                                        *r =
                                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                            * (size_t)47U
                                                            + (size_t)26U].data);
                                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)47U
                                                          + (size_t)26U].lock);
                                                        uint8_t *ptr = r;
                                                        uint8_t *r0 = ptr;
                                                        if (!(r0 == NULL))
                                                        {
                                                          r0[(size_t)(size26.sc - 2U)] = 42U;
                                                          r0[(size_t)(size26.sc - 1U)] = 23U;
                                                        }
                                                        return r0;
                                                      }
                                                      else
                                                      {
                                                        Constants_sc_full_
                                                        size27 =
                                                          sizes[arena_id * (size_t)47U + (size_t)27U];
                                                        bool
                                                        b27 = size27.slab_size % size27.sc == 0U;
                                                        if
                                                        (
                                                          b27 && bytes <= size27.sc - 2U &&
                                                            alignment <= size27.sc
                                                        )
                                                        {
                                                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                            * (size_t)47U
                                                            + (size_t)27U].lock);
                                                          uint8_t
                                                          *r =
                                                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                              * (size_t)47U
                                                              + (size_t)27U].data);
                                                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                            * (size_t)47U
                                                            + (size_t)27U].lock);
                                                          uint8_t *ptr = r;
                                                          uint8_t *r0 = ptr;
                                                          if (!(r0 == NULL))
                                                          {
                                                            r0[(size_t)(size27.sc - 2U)] = 42U;
                                                            r0[(size_t)(size27.sc - 1U)] = 23U;
                                                          }
                                                          return r0;
                                                        }
                                                        else
                                                        {
                                                          Constants_sc_full_
                                                          size28 =
                                                            sizes[arena_id * (size_t)47U +
                                                              (size_t)28U];
                                                          bool
                                                          b28 = size28.slab_size % size28.sc == 0U;
                                                          if
                                                          (
                                                            b28 && bytes <= size28.sc - 2U &&
                                                              alignment <= size28.sc
                                                          )
                                                          {
                                                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                              * (size_t)47U
                                                              + (size_t)28U].lock);
                                                            uint8_t
                                                            *r =
                                                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                * (size_t)47U
                                                                + (size_t)28U].data);
                                                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                              * (size_t)47U
                                                              + (size_t)28U].lock);
                                                            uint8_t *ptr = r;
                                                            uint8_t *r0 = ptr;
                                                            if (!(r0 == NULL))
                                                            {
                                                              r0[(size_t)(size28.sc - 2U)] = 42U;
                                                              r0[(size_t)(size28.sc - 1U)] = 23U;
                                                            }
                                                            return r0;
                                                          }
                                                          else
                                                          {
                                                            Constants_sc_full_
                                                            size29 =
                                                              sizes[arena_id * (size_t)47U +
                                                                (size_t)29U];
                                                            bool
                                                            b29 = size29.slab_size % size29.sc == 0U;
                                                            if
                                                            (
                                                              b29 && bytes <= size29.sc - 2U &&
                                                                alignment <= size29.sc
                                                            )
                                                            {
                                                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                * (size_t)47U
                                                                + (size_t)29U].lock);
                                                              uint8_t
                                                              *r =
                                                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                  * (size_t)47U
                                                                  + (size_t)29U].data);
                                                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                * (size_t)47U
                                                                + (size_t)29U].lock);
                                                              uint8_t *ptr = r;
                                                              uint8_t *r0 = ptr;
                                                              if (!(r0 == NULL))
                                                              {
                                                                r0[(size_t)(size29.sc - 2U)] = 42U;
                                                                r0[(size_t)(size29.sc - 1U)] = 23U;
                                                              }
                                                              return r0;
                                                            }
                                                            else
                                                            {
                                                              Constants_sc_full_
                                                              size30 =
                                                                sizes[arena_id * (size_t)47U +
                                                                  (size_t)30U];
                                                              bool
                                                              b30 =
                                                                size30.slab_size % size30.sc == 0U;
                                                              if
                                                              (
                                                                b30 && bytes <= size30.sc - 2U &&
                                                                  alignment <= size30.sc
                                                              )
                                                              {
                                                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                  * (size_t)47U
                                                                  + (size_t)30U].lock);
                                                                uint8_t
                                                                *r =
                                                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                    * (size_t)47U
                                                                    + (size_t)30U].data);
                                                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                  * (size_t)47U
                                                                  + (size_t)30U].lock);
                                                                uint8_t *ptr = r;
                                                                uint8_t *r0 = ptr;
                                                                if (!(r0 == NULL))
                                                                {
                                                                  r0[(size_t)(size30.sc - 2U)] = 42U;
                                                                  r0[(size_t)(size30.sc - 1U)] = 23U;
                                                                }
                                                                return r0;
                                                              }
                                                              else
                                                              {
                                                                Constants_sc_full_
                                                                size31 =
                                                                  sizes[arena_id * (size_t)47U +
                                                                    (size_t)31U];
                                                                bool
                                                                b31 =
                                                                  size31.slab_size % size31.sc == 0U;
                                                                if
                                                                (
                                                                  b31 && bytes <= size31.sc - 2U &&
                                                                    alignment <= size31.sc
                                                                )
                                                                {
                                                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                    * (size_t)47U
                                                                    + (size_t)31U].lock);
                                                                  uint8_t
                                                                  *r =
                                                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                      * (size_t)47U
                                                                      + (size_t)31U].data);
                                                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                    * (size_t)47U
                                                                    + (size_t)31U].lock);
                                                                  uint8_t *ptr = r;
                                                                  uint8_t *r0 = ptr;
                                                                  if (!(r0 == NULL))
                                                                  {
                                                                    r0[(size_t)(size31.sc - 2U)] =
                                                                      42U;
                                                                    r0[(size_t)(size31.sc - 1U)] =
                                                                      23U;
                                                                  }
                                                                  return r0;
                                                                }
                                                                else
                                                                {
                                                                  Constants_sc_full_
                                                                  size32 =
                                                                    sizes[arena_id * (size_t)47U +
                                                                      (size_t)32U];
                                                                  bool
                                                                  b32 =
                                                                    size32.slab_size % size32.sc ==
                                                                      0U;
                                                                  if
                                                                  (
                                                                    b32 && bytes <= size32.sc - 2U
                                                                    && alignment <= size32.sc
                                                                  )
                                                                  {
                                                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                      * (size_t)47U
                                                                      + (size_t)32U].lock);
                                                                    uint8_t
                                                                    *r =
                                                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                        * (size_t)47U
                                                                        + (size_t)32U].data);
                                                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                      * (size_t)47U
                                                                      + (size_t)32U].lock);
                                                                    uint8_t *ptr = r;
                                                                    uint8_t *r0 = ptr;
                                                                    if (!(r0 == NULL))
                                                                    {
                                                                      r0[(size_t)(size32.sc - 2U)] =
                                                                        42U;
                                                                      r0[(size_t)(size32.sc - 1U)] =
                                                                        23U;
                                                                    }
                                                                    return r0;
                                                                  }
                                                                  else
                                                                  {
                                                                    Constants_sc_full_
                                                                    size33 =
                                                                      sizes[arena_id * (size_t)47U +
                                                                        (size_t)33U];
                                                                    bool
                                                                    b33 =
                                                                      size33.slab_size % size33.sc
                                                                      == 0U;
                                                                    if
                                                                    (
                                                                      b33 && bytes <= size33.sc - 2U
                                                                      && alignment <= size33.sc
                                                                    )
                                                                    {
                                                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                        * (size_t)47U
                                                                        + (size_t)33U].lock);
                                                                      uint8_t
                                                                      *r =
                                                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                          * (size_t)47U
                                                                          + (size_t)33U].data);
                                                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                        * (size_t)47U
                                                                        + (size_t)33U].lock);
                                                                      uint8_t *ptr = r;
                                                                      uint8_t *r0 = ptr;
                                                                      if (!(r0 == NULL))
                                                                      {
                                                                        r0[(size_t)(size33.sc - 2U)]
                                                                        = 42U;
                                                                        r0[(size_t)(size33.sc - 1U)]
                                                                        = 23U;
                                                                      }
                                                                      return r0;
                                                                    }
                                                                    else
                                                                    {
                                                                      Constants_sc_full_
                                                                      size34 =
                                                                        sizes[arena_id * (size_t)47U
                                                                        + (size_t)34U];
                                                                      bool
                                                                      b34 =
                                                                        size34.slab_size % size34.sc
                                                                        == 0U;
                                                                      if
                                                                      (
                                                                        b34 &&
                                                                          bytes <= size34.sc - 2U
                                                                        && alignment <= size34.sc
                                                                      )
                                                                      {
                                                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                          * (size_t)47U
                                                                          + (size_t)34U].lock);
                                                                        uint8_t
                                                                        *r =
                                                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                            * (size_t)47U
                                                                            + (size_t)34U].data);
                                                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                          * (size_t)47U
                                                                          + (size_t)34U].lock);
                                                                        uint8_t *ptr = r;
                                                                        uint8_t *r0 = ptr;
                                                                        if (!(r0 == NULL))
                                                                        {
                                                                          r0[(size_t)(size34.sc - 2U)]
                                                                          = 42U;
                                                                          r0[(size_t)(size34.sc - 1U)]
                                                                          = 23U;
                                                                        }
                                                                        return r0;
                                                                      }
                                                                      else
                                                                      {
                                                                        Constants_sc_full_
                                                                        size35 =
                                                                          sizes[arena_id *
                                                                            (size_t)47U
                                                                          + (size_t)35U];
                                                                        bool
                                                                        b35 =
                                                                          size35.slab_size %
                                                                            size35.sc
                                                                          == 0U;
                                                                        if
                                                                        (
                                                                          b35 &&
                                                                            bytes <= size35.sc - 2U
                                                                          && alignment <= size35.sc
                                                                        )
                                                                        {
                                                                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                            * (size_t)47U
                                                                            + (size_t)35U].lock);
                                                                          uint8_t
                                                                          *r =
                                                                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                              * (size_t)47U
                                                                              + (size_t)35U].data);
                                                                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                            * (size_t)47U
                                                                            + (size_t)35U].lock);
                                                                          uint8_t *ptr = r;
                                                                          uint8_t *r0 = ptr;
                                                                          if (!(r0 == NULL))
                                                                          {
                                                                            r0[(size_t)(size35.sc -
                                                                              2U)]
                                                                            = 42U;
                                                                            r0[(size_t)(size35.sc -
                                                                              1U)]
                                                                            = 23U;
                                                                          }
                                                                          return r0;
                                                                        }
                                                                        else
                                                                        {
                                                                          Constants_sc_full_
                                                                          size36 =
                                                                            sizes[arena_id *
                                                                              (size_t)47U
                                                                            + (size_t)36U];
                                                                          bool
                                                                          b36 =
                                                                            size36.slab_size %
                                                                              size36.sc
                                                                            == 0U;
                                                                          if
                                                                          (
                                                                            b36 &&
                                                                              bytes <=
                                                                                size36.sc - 2U
                                                                            &&
                                                                              alignment <= size36.sc
                                                                          )
                                                                          {
                                                                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                              * (size_t)47U
                                                                              + (size_t)36U].lock);
                                                                            uint8_t
                                                                            *r =
                                                                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                * (size_t)47U
                                                                                + (size_t)36U].data);
                                                                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                              * (size_t)47U
                                                                              + (size_t)36U].lock);
                                                                            uint8_t *ptr = r;
                                                                            uint8_t *r0 = ptr;
                                                                            if (!(r0 == NULL))
                                                                            {
                                                                              r0[(size_t)(size36.sc
                                                                              - 2U)]
                                                                              = 42U;
                                                                              r0[(size_t)(size36.sc
                                                                              - 1U)]
                                                                              = 23U;
                                                                            }
                                                                            return r0;
                                                                          }
                                                                          else
                                                                          {
                                                                            Constants_sc_full_
                                                                            size37 =
                                                                              sizes[arena_id *
                                                                                (size_t)47U
                                                                              + (size_t)37U];
                                                                            bool
                                                                            b37 =
                                                                              size37.slab_size %
                                                                                size37.sc
                                                                              == 0U;
                                                                            if
                                                                            (
                                                                              b37 &&
                                                                                bytes <=
                                                                                  size37.sc - 2U
                                                                              &&
                                                                                alignment <=
                                                                                  size37.sc
                                                                            )
                                                                            {
                                                                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                * (size_t)47U
                                                                                + (size_t)37U].lock);
                                                                              uint8_t
                                                                              *r =
                                                                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                  * (size_t)47U
                                                                                  + (size_t)37U].data);
                                                                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                * (size_t)47U
                                                                                + (size_t)37U].lock);
                                                                              uint8_t *ptr = r;
                                                                              uint8_t *r0 = ptr;
                                                                              if (!(r0 == NULL))
                                                                              {
                                                                                r0[(size_t)(size37.sc
                                                                                - 2U)]
                                                                                = 42U;
                                                                                r0[(size_t)(size37.sc
                                                                                - 1U)]
                                                                                = 23U;
                                                                              }
                                                                              return r0;
                                                                            }
                                                                            else
                                                                            {
                                                                              Constants_sc_full_
                                                                              size38 =
                                                                                sizes[arena_id *
                                                                                  (size_t)47U
                                                                                + (size_t)38U];
                                                                              bool
                                                                              b38 =
                                                                                size38.slab_size %
                                                                                  size38.sc
                                                                                == 0U;
                                                                              if
                                                                              (
                                                                                b38 &&
                                                                                  bytes <=
                                                                                    size38.sc - 2U
                                                                                &&
                                                                                  alignment <=
                                                                                    size38.sc
                                                                              )
                                                                              {
                                                                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                  * (size_t)47U
                                                                                  + (size_t)38U].lock);
                                                                                uint8_t
                                                                                *r =
                                                                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                    * (size_t)47U
                                                                                    + (size_t)38U].data);
                                                                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                  * (size_t)47U
                                                                                  + (size_t)38U].lock);
                                                                                uint8_t *ptr = r;
                                                                                uint8_t *r0 = ptr;
                                                                                if (!(r0 == NULL))
                                                                                {
                                                                                  r0[(size_t)(size38.sc
                                                                                  - 2U)]
                                                                                  = 42U;
                                                                                  r0[(size_t)(size38.sc
                                                                                  - 1U)]
                                                                                  = 23U;
                                                                                }
                                                                                return r0;
                                                                              }
                                                                              else
                                                                              {
                                                                                Constants_sc_full_
                                                                                size39 =
                                                                                  sizes[arena_id *
                                                                                    (size_t)47U
                                                                                  + (size_t)39U];
                                                                                bool
                                                                                b39 =
                                                                                  size39.slab_size %
                                                                                    size39.sc
                                                                                  == 0U;
                                                                                if
                                                                                (
                                                                                  b39 &&
                                                                                    bytes <=
                                                                                      size39.sc - 2U
                                                                                  &&
                                                                                    alignment <=
                                                                                      size39.sc
                                                                                )
                                                                                {
                                                                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                    * (size_t)47U
                                                                                    + (size_t)39U].lock);
                                                                                  uint8_t
                                                                                  *r =
                                                                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                      * (size_t)47U
                                                                                      + (size_t)39U].data);
                                                                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                    * (size_t)47U
                                                                                    + (size_t)39U].lock);
                                                                                  uint8_t *ptr = r;
                                                                                  uint8_t *r0 = ptr;
                                                                                  if (!(r0 == NULL))
                                                                                  {
                                                                                    r0[(size_t)(size39.sc
                                                                                    - 2U)]
                                                                                    = 42U;
                                                                                    r0[(size_t)(size39.sc
                                                                                    - 1U)]
                                                                                    = 23U;
                                                                                  }
                                                                                  return r0;
                                                                                }
                                                                                else
                                                                                {
                                                                                  Constants_sc_full_
                                                                                  size40 =
                                                                                    sizes[arena_id *
                                                                                      (size_t)47U
                                                                                    + (size_t)40U];
                                                                                  bool
                                                                                  b40 =
                                                                                    size40.slab_size
                                                                                    % size40.sc
                                                                                    == 0U;
                                                                                  if
                                                                                  (
                                                                                    b40 &&
                                                                                      bytes <=
                                                                                        size40.sc -
                                                                                          2U
                                                                                    &&
                                                                                      alignment <=
                                                                                        size40.sc
                                                                                  )
                                                                                  {
                                                                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                      * (size_t)47U
                                                                                      + (size_t)40U].lock);
                                                                                    uint8_t
                                                                                    *r =
                                                                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                        *
                                                                                          (size_t)47U
                                                                                        +
                                                                                          (size_t)40U].data);
                                                                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                      * (size_t)47U
                                                                                      + (size_t)40U].lock);
                                                                                    uint8_t
                                                                                    *ptr = r;
                                                                                    uint8_t
                                                                                    *r0 = ptr;
                                                                                    if
                                                                                    (!(r0 == NULL))
                                                                                    {
                                                                                      r0[(size_t)(size40.sc
                                                                                      - 2U)]
                                                                                      = 42U;
                                                                                      r0[(size_t)(size40.sc
                                                                                      - 1U)]
                                                                                      = 23U;
                                                                                    }
                                                                                    return r0;
                                                                                  }
                                                                                  else
                                                                                  {
                                                                                    Constants_sc_full_
                                                                                    size41 =
                                                                                      sizes[arena_id
                                                                                      * (size_t)47U
                                                                                      + (size_t)41U];
                                                                                    bool
                                                                                    b41 =
                                                                                      size41.slab_size
                                                                                      % size41.sc
                                                                                      == 0U;
                                                                                    if
                                                                                    (
                                                                                      b41 &&
                                                                                        bytes <=
                                                                                          size41.sc
                                                                                          - 2U
                                                                                      &&
                                                                                        alignment <=
                                                                                          size41.sc
                                                                                    )
                                                                                    {
                                                                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                        *
                                                                                          (size_t)47U
                                                                                        +
                                                                                          (size_t)41U].lock);
                                                                                      uint8_t
                                                                                      *r =
                                                                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                          *
                                                                                            (size_t)47U
                                                                                          +
                                                                                            (size_t)41U].data);
                                                                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                        *
                                                                                          (size_t)47U
                                                                                        +
                                                                                          (size_t)41U].lock);
                                                                                      uint8_t
                                                                                      *ptr = r;
                                                                                      uint8_t
                                                                                      *r0 = ptr;
                                                                                      if
                                                                                      (
                                                                                        !(r0 == NULL)
                                                                                      )
                                                                                      {
                                                                                        r0[(size_t)(size41.sc
                                                                                        - 2U)]
                                                                                        = 42U;
                                                                                        r0[(size_t)(size41.sc
                                                                                        - 1U)]
                                                                                        = 23U;
                                                                                      }
                                                                                      return r0;
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                      Constants_sc_full_
                                                                                      size42 =
                                                                                        sizes[arena_id
                                                                                        *
                                                                                          (size_t)47U
                                                                                        +
                                                                                          (size_t)42U];
                                                                                      bool
                                                                                      b42 =
                                                                                        size42.slab_size
                                                                                        % size42.sc
                                                                                        == 0U;
                                                                                      if
                                                                                      (
                                                                                        b42 &&
                                                                                          bytes <=
                                                                                            size42.sc
                                                                                            - 2U
                                                                                        &&
                                                                                          alignment
                                                                                          <=
                                                                                            size42.sc
                                                                                      )
                                                                                      {
                                                                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                          *
                                                                                            (size_t)47U
                                                                                          +
                                                                                            (size_t)42U].lock);
                                                                                        uint8_t
                                                                                        *r =
                                                                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                            *
                                                                                              (size_t)47U
                                                                                            +
                                                                                              (size_t)42U].data);
                                                                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                          *
                                                                                            (size_t)47U
                                                                                          +
                                                                                            (size_t)42U].lock);
                                                                                        uint8_t
                                                                                        *ptr = r;
                                                                                        uint8_t
                                                                                        *r0 = ptr;
                                                                                        if
                                                                                        (
                                                                                          !(r0 ==
                                                                                            NULL)
                                                                                        )
                                                                                        {
                                                                                          r0[(size_t)(size42.sc
                                                                                          - 2U)]
                                                                                          = 42U;
                                                                                          r0[(size_t)(size42.sc
                                                                                          - 1U)]
                                                                                          = 23U;
                                                                                        }
                                                                                        return r0;
                                                                                      }
                                                                                      else
                                                                                      {
                                                                                        Constants_sc_full_
                                                                                        size43 =
                                                                                          sizes[arena_id
                                                                                          *
                                                                                            (size_t)47U
                                                                                          +
                                                                                            (size_t)43U];
                                                                                        bool
                                                                                        b43 =
                                                                                          size43.slab_size
                                                                                          %
                                                                                            size43.sc
                                                                                          == 0U;
                                                                                        if
                                                                                        (
                                                                                          b43 &&
                                                                                            bytes <=
                                                                                              size43.sc
                                                                                              - 2U
                                                                                          &&
                                                                                            alignment
                                                                                            <=
                                                                                              size43.sc
                                                                                        )
                                                                                        {
                                                                                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                            *
                                                                                              (size_t)47U
                                                                                            +
                                                                                              (size_t)43U].lock);
                                                                                          uint8_t
                                                                                          *r =
                                                                                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                              *
                                                                                                (size_t)47U
                                                                                              +
                                                                                                (size_t)43U].data);
                                                                                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                            *
                                                                                              (size_t)47U
                                                                                            +
                                                                                              (size_t)43U].lock);
                                                                                          uint8_t
                                                                                          *ptr = r;
                                                                                          uint8_t
                                                                                          *r0 = ptr;
                                                                                          if
                                                                                          (
                                                                                            !(r0 ==
                                                                                              NULL)
                                                                                          )
                                                                                          {
                                                                                            r0[(size_t)(size43.sc
                                                                                            - 2U)]
                                                                                            = 42U;
                                                                                            r0[(size_t)(size43.sc
                                                                                            - 1U)]
                                                                                            = 23U;
                                                                                          }
                                                                                          return r0;
                                                                                        }
                                                                                        else
                                                                                        {
                                                                                          Constants_sc_full_
                                                                                          size44 =
                                                                                            sizes[arena_id
                                                                                            *
                                                                                              (size_t)47U
                                                                                            +
                                                                                              (size_t)44U];
                                                                                          bool
                                                                                          b44 =
                                                                                            size44.slab_size
                                                                                            %
                                                                                              size44.sc
                                                                                            == 0U;
                                                                                          if
                                                                                          (
                                                                                            b44 &&
                                                                                              bytes
                                                                                              <=
                                                                                                size44.sc
                                                                                                - 2U
                                                                                            &&
                                                                                              alignment
                                                                                              <=
                                                                                                size44.sc
                                                                                          )
                                                                                          {
                                                                                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                              *
                                                                                                (size_t)47U
                                                                                              +
                                                                                                (size_t)44U].lock);
                                                                                            uint8_t
                                                                                            *r =
                                                                                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                                *
                                                                                                  (size_t)47U
                                                                                                +
                                                                                                  (size_t)44U].data);
                                                                                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                              *
                                                                                                (size_t)47U
                                                                                              +
                                                                                                (size_t)44U].lock);
                                                                                            uint8_t
                                                                                            *ptr = r;
                                                                                            uint8_t
                                                                                            *r0 =
                                                                                              ptr;
                                                                                            if
                                                                                            (
                                                                                              !(r0
                                                                                              ==
                                                                                                NULL)
                                                                                            )
                                                                                            {
                                                                                              r0[(size_t)(size44.sc
                                                                                              - 2U)]
                                                                                              = 42U;
                                                                                              r0[(size_t)(size44.sc
                                                                                              - 1U)]
                                                                                              = 23U;
                                                                                            }
                                                                                            return
                                                                                              r0;
                                                                                          }
                                                                                          else
                                                                                          {
                                                                                            Constants_sc_full_
                                                                                            size45 =
                                                                                              sizes[arena_id
                                                                                              *
                                                                                                (size_t)47U
                                                                                              +
                                                                                                (size_t)45U];
                                                                                            bool
                                                                                            b45 =
                                                                                              size45.slab_size
                                                                                              %
                                                                                                size45.sc
                                                                                              == 0U;
                                                                                            if
                                                                                            (
                                                                                              b45 &&
                                                                                                bytes
                                                                                                <=
                                                                                                  size45.sc
                                                                                                  -
                                                                                                    2U
                                                                                              &&
                                                                                                alignment
                                                                                                <=
                                                                                                  size45.sc
                                                                                            )
                                                                                            {
                                                                                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                                *
                                                                                                  (size_t)47U
                                                                                                +
                                                                                                  (size_t)45U].lock);
                                                                                              uint8_t
                                                                                              *r =
                                                                                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                                  *
                                                                                                    (size_t)47U
                                                                                                  +
                                                                                                    (size_t)45U].data);
                                                                                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                                *
                                                                                                  (size_t)47U
                                                                                                +
                                                                                                  (size_t)45U].lock);
                                                                                              uint8_t
                                                                                              *ptr =
                                                                                                r;
                                                                                              uint8_t
                                                                                              *r0 =
                                                                                                ptr;
                                                                                              if
                                                                                              (
                                                                                                !(r0
                                                                                                ==
                                                                                                  NULL)
                                                                                              )
                                                                                              {
                                                                                                r0[(size_t)(size45.sc
                                                                                                - 2U)]
                                                                                                =
                                                                                                  42U;
                                                                                                r0[(size_t)(size45.sc
                                                                                                - 1U)]
                                                                                                =
                                                                                                  23U;
                                                                                              }
                                                                                              return
                                                                                                r0;
                                                                                            }
                                                                                            else
                                                                                            {
                                                                                              Constants_sc_full_
                                                                                              size46 =
                                                                                                sizes[arena_id
                                                                                                *
                                                                                                  (size_t)47U
                                                                                                +
                                                                                                  (size_t)46U];
                                                                                              bool
                                                                                              b46 =
                                                                                                size46.slab_size
                                                                                                %
                                                                                                  size46.sc
                                                                                                ==
                                                                                                  0U;
                                                                                              if
                                                                                              (
                                                                                                b46
                                                                                                &&
                                                                                                  bytes
                                                                                                  <=
                                                                                                    size46.sc
                                                                                                    -
                                                                                                      2U
                                                                                                &&
                                                                                                  alignment
                                                                                                  <=
                                                                                                    size46.sc
                                                                                              )
                                                                                              {
                                                                                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                                                  *
                                                                                                    (size_t)47U
                                                                                                  +
                                                                                                    (size_t)46U].lock);
                                                                                                uint8_t
                                                                                                *r =
                                                                                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                                                    *
                                                                                                      (size_t)47U
                                                                                                    +
                                                                                                      (size_t)46U].data);
                                                                                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                                                  *
                                                                                                    (size_t)47U
                                                                                                  +
                                                                                                    (size_t)46U].lock);
                                                                                                uint8_t
                                                                                                *ptr =
                                                                                                  r;
                                                                                                uint8_t
                                                                                                *r0 =
                                                                                                  ptr;
                                                                                                if
                                                                                                (
                                                                                                  !(r0
                                                                                                  ==
                                                                                                    NULL)
                                                                                                )
                                                                                                {
                                                                                                  r0[(size_t)(size46.sc
                                                                                                  -
                                                                                                    2U)]
                                                                                                  =
                                                                                                    42U;
                                                                                                  r0[(size_t)(size46.sc
                                                                                                  -
                                                                                                    1U)]
                                                                                                  =
                                                                                                    23U;
                                                                                                }
                                                                                                return
                                                                                                  r0;
                                                                                              }
                                                                                              else
                                                                                                return
                                                                                                  NULL;
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

static size_t slab_getsize(uint8_t *ptr)
{
  uint8_t *pt0 = ptr;
  uint8_t *pt1 = Main_Meta_sc_all.slab_region;
  ptrdiff_t diff = pt0 - pt1;
  size_t diff_sz = (size_t)diff;
  size_t index = diff_sz / (size_t)68719476736U;
  Constants_sc_full_ size = sizes[index];
  size_t rem_slot = diff_sz % (size_t)size.slab_size;
  if (rem_slot % (size_t)size.sc == (size_t)0U)
    return (size_t)(size.sc - 2U);
  else
    return (size_t)0U;
}

static bool slab_free(uint8_t *ptr)
{
  uint8_t *pt0 = ptr;
  uint8_t *pt1 = Main_Meta_sc_all.slab_region;
  ptrdiff_t diff = pt0 - pt1;
  size_t diff_sz = (size_t)diff;
  size_t index = diff_sz / (size_t)68719476736U;
  Constants_sc_full_ size = sizes[index];
  size_t rem_slab = diff_sz % (size_t)68719476736U;
  size_t rem_slot = diff_sz % (size_t)size.slab_size;
  if (rem_slot % (size_t)size.sc == (size_t)0U)
  {
    uint8_t magic1 = ptr[(size_t)(size.sc - 2U)];
    uint8_t magic2 = ptr[(size_t)(size.sc - 1U)];
    if (magic1 == 42U && magic2 == 23U)
    {
      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[index].lock);
      bool
      r = SizeClass_deallocate_size_class(Main_Meta_sc_all.size_classes[index].data, ptr, rem_slab);
      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[index].lock);
      bool b = r;
      return b;
    }
    else
      return false;
  }
  else
    return false;
}

size_t StarMalloc_threshold;

uint8_t *StarMalloc_malloc(size_t arena_id, size_t size)
{
  if (size <= StarMalloc_threshold)
  {
    uint8_t *ptr = slab_malloc(arena_id, (uint32_t)size);
    if (ptr == NULL || false)
      return ptr;
    else
    {
      bool b = check_zeroing_u8(ptr, size);
      if (b)
        return ptr;
      else
      {
        FatalError_die_from_malloc_zeroing_check_failure(ptr);
        return NULL;
      }
    }
  }
  else
  {
    size_t size_;
    if (size <= (size_t)Constants_max_slab_size)
      size_ = (size_t)Constants_max_slab_size + (size_t)1U;
    else
      size_ = size;
    uint8_t *r = large_malloc(size_);
    return r;
  }
}

uint8_t *StarMalloc_aligned_alloc(size_t arena_id, size_t alignment, size_t size)
{
  uint32_t alignment_as_u32 = (uint32_t)alignment;
  bool
  check1 =
    alignment > (size_t)0U && (size_t)Constants_max_slab_size % alignment == (size_t)0U &&
      size <= StarMalloc_threshold;
  bool check2 = alignment > (size_t)0U && (size_t)4096U % alignment == (size_t)0U;
  if (check1)
  {
    uint8_t *ptr = slab_aligned_alloc(arena_id, alignment_as_u32, (uint32_t)size);
    if (ptr == NULL || false)
      return ptr;
    else
    {
      bool b = check_zeroing_u8(ptr, size);
      if (b)
        return ptr;
      else
      {
        FatalError_die_from_malloc_zeroing_check_failure(ptr);
        return NULL;
      }
    }
  }
  else if (check2)
  {
    size_t size_;
    if (size <= (size_t)Constants_max_slab_size)
      size_ = (size_t)Constants_max_slab_size + (size_t)1U;
    else
      size_ = size;
    uint8_t *ptr = large_malloc(size_);
    return ptr;
  }
  else
    return NULL;
}

bool StarMalloc_free(uint8_t *ptr)
{
  if (ptr == NULL)
    return true;
  else
  {
    bool
    b =
      within_bounds_ptr(Main_Meta_sc_all.slab_region,
        ptr,
        Main_Meta_sc_all.slab_region + full_slab_region_size);
    bool b0 = b;
    if (b0)
      return slab_free(ptr);
    else
      return large_free(ptr);
  }
}

size_t StarMalloc_getsize(uint8_t *ptr)
{
  bool
  b =
    within_bounds_ptr(Main_Meta_sc_all.slab_region,
      ptr,
      Main_Meta_sc_all.slab_region + full_slab_region_size);
  bool b0 = b;
  if (b0)
  {
    size_t r = slab_getsize(ptr);
    return r;
  }
  else
  {
    size_t r = large_getsize(ptr);
    return r;
  }
}

uint8_t *StarMalloc_realloc(size_t arena_id, uint8_t *ptr, size_t new_size)
{
  if (ptr == NULL)
  {
    uint8_t *new_ptr = StarMalloc_malloc(arena_id, new_size);
    return new_ptr;
  }
  else if (new_size == (size_t)0U)
  {
    bool b = StarMalloc_free(ptr);
    if (b)
      return NULL;
    else
    {
      FatalError_die_from_realloc_free_failure(ptr);
      return NULL;
    }
  }
  else
  {
    size_t old_size = StarMalloc_getsize(ptr);
    bool old_allocation_is_small = old_size <= (size_t)Constants_max_slab_size;
    bool new_allocation_is_small = new_size <= StarMalloc_threshold;
    bool same_case = old_allocation_is_small == new_allocation_is_small;
    bool small_case_optim_condition;
    if (old_allocation_is_small && same_case)
    {
      uint32_t r0 = SizeClassSelection_inv_impl((uint32_t)old_size);
      size_t old_sc = (size_t)r0;
      uint32_t r = SizeClassSelection_inv_impl((uint32_t)(new_size + (size_t)2U));
      size_t new_sc = (size_t)r;
      small_case_optim_condition = old_sc == new_sc;
    }
    else
      small_case_optim_condition = false;
    bool
    large_case_optim_condition = !old_allocation_is_small && same_case && new_size <= old_size;
    if (old_size == (size_t)0U)
    {
      FatalError_die_from_realloc_invalid_previous_alloc(ptr);
      return NULL;
    }
    else if (small_case_optim_condition || large_case_optim_condition)
      return ptr;
    else
    {
      uint8_t *new_ptr = StarMalloc_malloc(arena_id, new_size);
      if (new_ptr == NULL)
        return NULL;
      else
      {
        size_t min_of_sizes;
        if (new_size <= old_size)
          min_of_sizes = new_size;
        else
          min_of_sizes = old_size;
        memcpy_u8(new_ptr, ptr, min_of_sizes);
        bool b = StarMalloc_free(ptr);
        if (b)
          return new_ptr;
        else
        {
          FatalError_die_from_realloc_free_failure(ptr);
          return NULL;
        }
      }
    }
  }
}

uint8_t *StarMalloc_calloc(size_t arena_id, size_t size1, size_t size2)
{
  size_t size = builtin_mul_overflow(size1, size2);
  uint8_t *ptr = StarMalloc_malloc(arena_id, size);
  if (ptr == NULL)
    return ptr;
  else
    return ptr;
}

