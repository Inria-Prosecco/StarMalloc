// SPDX-License-Identifier: Apache-2.0


#include "internal/StarMalloc.h"

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

static size_t slab_region_size = (size_t)7421703487488U;

static void
init_size_class(
  size_t k,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  ArrayList_cell *md_region,
  size_class *size_classes,
  const uint32_t *sizes
)
{
  uint32_t size = sizes[k];
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

static uint32_t avl_data_size = 64U;

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
      .size = avl_data_size, .slabs_idxs = r_idxs, .md_count = md_count, .slab_region = slab_region,
      .md_bm_region = md_bm_region, .md_region = md_region
    };
  SizeClass_size_class_struct_ scs0 = scs;
  Steel_SpinLock_new_lock(&ret->lock);
  ret->slab_region = slab_region;
  ret->scs = scs0;
}

Impl_Trees_Types_mmap_md_slabs Impl_Trees_Types_metadata_slabs;

extern uint8_t *Impl_Trees_Types_ref_node__to__array_u8(Impl_Trees_Types_node *x);

extern Impl_Trees_Types_node *Impl_Trees_Types_array_u8__to__ref_node(uint8_t *arr);

extern int64_t Impl_Trees_Types_cmp(Impl_Trees_Types_data uu___, Impl_Trees_Types_data x0);

bool Impl_BST_M_member(Impl_Trees_Types_node *ptr, Impl_Trees_Types_data v)
{
  if (ptr == NULL)
    return false;
  else
  {
    Impl_Trees_Types_node node = *ptr;
    Impl_Trees_Types_data data = node.data;
    int64_t delta = Impl_Trees_Types_cmp(v, data);
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

static Impl_Trees_Types_node *rotate_left_right(Impl_Trees_Types_node *ptr)
{
  Impl_Trees_Types_node x_node = *ptr;
  Impl_Trees_Types_data x = x_node.data;
  Impl_Trees_Types_node z_node = *x_node.left;
  Impl_Trees_Types_data z = z_node.data;
  Impl_Trees_Types_node y_node = *z_node.right;
  Impl_Trees_Types_data y = y_node.data;
  uint64_t s10;
  if (z_node.left == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.left;
    s10 = node.size;
  }
  uint64_t s20;
  if (y_node.left == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.left;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (z_node.left == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.left;
    h10 = node.height;
  }
  uint64_t h20;
  if (y_node.left == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.left;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Types_node
  n = { .data = z, .left = z_node.left, .right = y_node.left, .size = s, .height = h };
  *x_node.left = n;
  Impl_Trees_Types_node *new_z = x_node.left;
  uint64_t s11;
  if (y_node.right == NULL)
    s11 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.right;
    s11 = node.size;
  }
  uint64_t s21;
  if (x_node.right == NULL)
    s21 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.right;
    s21 = node.size;
  }
  uint64_t s0 = s11 + s21 + 1ULL;
  uint64_t h11;
  if (y_node.right == NULL)
    h11 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.right;
    h11 = node.height;
  }
  uint64_t h21;
  if (x_node.right == NULL)
    h21 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.right;
    h21 = node.height;
  }
  uint64_t ite1;
  if (h11 > h21)
    ite1 = h11;
  else
    ite1 = h21;
  uint64_t h0 = ite1 + 1ULL;
  Impl_Trees_Types_node
  n0 = { .data = x, .left = y_node.right, .right = x_node.right, .size = s0, .height = h0 };
  *ptr = n0;
  Impl_Trees_Types_node *new_x = ptr;
  uint64_t s1;
  if (new_z == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_z;
    s1 = node.size;
  }
  uint64_t s2;
  if (new_x == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_x;
    s2 = node.size;
  }
  uint64_t s3 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (new_z == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_z;
    h1 = node.height;
  }
  uint64_t h2;
  if (new_x == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_x;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h3 = ite + 1ULL;
  Impl_Trees_Types_node
  n1 = { .data = y, .left = new_z, .right = new_x, .size = s3, .height = h3 };
  *z_node.right = n1;
  Impl_Trees_Types_node *new_y = z_node.right;
  return new_y;
}

static Impl_Trees_Types_node *rotate_right_left(Impl_Trees_Types_node *ptr)
{
  Impl_Trees_Types_node x_node = *ptr;
  Impl_Trees_Types_data x = x_node.data;
  Impl_Trees_Types_node z_node = *x_node.right;
  Impl_Trees_Types_data z = z_node.data;
  Impl_Trees_Types_node y_node = *z_node.left;
  Impl_Trees_Types_data y = y_node.data;
  uint64_t s10;
  if (x_node.left == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.left;
    s10 = node.size;
  }
  uint64_t s20;
  if (y_node.left == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.left;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (x_node.left == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.left;
    h10 = node.height;
  }
  uint64_t h20;
  if (y_node.left == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.left;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Types_node
  n = { .data = x, .left = x_node.left, .right = y_node.left, .size = s, .height = h };
  *ptr = n;
  Impl_Trees_Types_node *new_x = ptr;
  uint64_t s11;
  if (y_node.right == NULL)
    s11 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.right;
    s11 = node.size;
  }
  uint64_t s21;
  if (z_node.right == NULL)
    s21 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.right;
    s21 = node.size;
  }
  uint64_t s0 = s11 + s21 + 1ULL;
  uint64_t h11;
  if (y_node.right == NULL)
    h11 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *y_node.right;
    h11 = node.height;
  }
  uint64_t h21;
  if (z_node.right == NULL)
    h21 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.right;
    h21 = node.height;
  }
  uint64_t ite1;
  if (h11 > h21)
    ite1 = h11;
  else
    ite1 = h21;
  uint64_t h0 = ite1 + 1ULL;
  Impl_Trees_Types_node
  n0 = { .data = z, .left = y_node.right, .right = z_node.right, .size = s0, .height = h0 };
  *x_node.right = n0;
  Impl_Trees_Types_node *new_z = x_node.right;
  uint64_t s1;
  if (new_x == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_x;
    s1 = node.size;
  }
  uint64_t s2;
  if (new_z == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_z;
    s2 = node.size;
  }
  uint64_t s3 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (new_x == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_x;
    h1 = node.height;
  }
  uint64_t h2;
  if (new_z == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_z;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h3 = ite + 1ULL;
  Impl_Trees_Types_node
  n1 = { .data = y, .left = new_x, .right = new_z, .size = s3, .height = h3 };
  *z_node.left = n1;
  Impl_Trees_Types_node *new_y = z_node.left;
  return new_y;
}

static Impl_Trees_Types_node *rotate_left(Impl_Trees_Types_node *ptr)
{
  Impl_Trees_Types_node x_node = *ptr;
  Impl_Trees_Types_data x = x_node.data;
  Impl_Trees_Types_node z_node = *x_node.right;
  Impl_Trees_Types_data z = z_node.data;
  uint64_t s10;
  if (x_node.left == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.left;
    s10 = node.size;
  }
  uint64_t s20;
  if (z_node.left == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.left;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (x_node.left == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.left;
    h10 = node.height;
  }
  uint64_t h20;
  if (z_node.left == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.left;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Types_node
  n = { .data = x, .left = x_node.left, .right = z_node.left, .size = s, .height = h };
  *ptr = n;
  Impl_Trees_Types_node *new_subnode = ptr;
  uint64_t s1;
  if (new_subnode == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_subnode;
    s1 = node.size;
  }
  uint64_t s2;
  if (z_node.right == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.right;
    s2 = node.size;
  }
  uint64_t s0 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (new_subnode == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_subnode;
    h1 = node.height;
  }
  uint64_t h2;
  if (z_node.right == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.right;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h0 = ite + 1ULL;
  Impl_Trees_Types_node
  n0 = { .data = z, .left = new_subnode, .right = z_node.right, .size = s0, .height = h0 };
  *x_node.right = n0;
  Impl_Trees_Types_node *new_node = x_node.right;
  return new_node;
}

static Impl_Trees_Types_node *rotate_right(Impl_Trees_Types_node *ptr)
{
  Impl_Trees_Types_node x_node = *ptr;
  Impl_Trees_Types_data x = x_node.data;
  Impl_Trees_Types_node z_node = *x_node.left;
  Impl_Trees_Types_data z = z_node.data;
  uint64_t s10;
  if (z_node.right == NULL)
    s10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.right;
    s10 = node.size;
  }
  uint64_t s20;
  if (x_node.right == NULL)
    s20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.right;
    s20 = node.size;
  }
  uint64_t s = s10 + s20 + 1ULL;
  uint64_t h10;
  if (z_node.right == NULL)
    h10 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.right;
    h10 = node.height;
  }
  uint64_t h20;
  if (x_node.right == NULL)
    h20 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *x_node.right;
    h20 = node.height;
  }
  uint64_t ite0;
  if (h10 > h20)
    ite0 = h10;
  else
    ite0 = h20;
  uint64_t h = ite0 + 1ULL;
  Impl_Trees_Types_node
  n = { .data = x, .left = z_node.right, .right = x_node.right, .size = s, .height = h };
  *ptr = n;
  Impl_Trees_Types_node *new_subnode = ptr;
  uint64_t s1;
  if (z_node.left == NULL)
    s1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.left;
    s1 = node.size;
  }
  uint64_t s2;
  if (new_subnode == NULL)
    s2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_subnode;
    s2 = node.size;
  }
  uint64_t s0 = s1 + s2 + 1ULL;
  uint64_t h1;
  if (z_node.left == NULL)
    h1 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *z_node.left;
    h1 = node.height;
  }
  uint64_t h2;
  if (new_subnode == NULL)
    h2 = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *new_subnode;
    h2 = node.height;
  }
  uint64_t ite;
  if (h1 > h2)
    ite = h1;
  else
    ite = h2;
  uint64_t h0 = ite + 1ULL;
  Impl_Trees_Types_node
  n0 = { .data = z, .left = z_node.left, .right = new_subnode, .size = s0, .height = h0 };
  *x_node.left = n0;
  Impl_Trees_Types_node *new_node = x_node.left;
  return new_node;
}

static bool is_balanced_local(Impl_Trees_Types_node *ptr)
{
  if (ptr == NULL)
    return true;
  else
  {
    Impl_Trees_Types_node node = *ptr;
    uint64_t lh;
    if (node.left == NULL)
      lh = 0ULL;
    else
    {
      Impl_Trees_Types_node node1 = *node.left;
      lh = node1.height;
    }
    uint64_t rh;
    if (node.right == NULL)
      rh = 0ULL;
    else
    {
      Impl_Trees_Types_node node1 = *node.right;
      rh = node1.height;
    }
    bool b1 = rh + 1ULL >= lh;
    bool b2 = lh + 1ULL >= rh;
    return b1 && b2;
  }
}

static Impl_Trees_Types_node *rebalance_avl(Impl_Trees_Types_node *ptr)
{
  if (is_balanced_local(ptr))
    return ptr;
  else
  {
    Impl_Trees_Types_node node = *ptr;
    uint64_t lh;
    if (node.left == NULL)
      lh = 0ULL;
    else
    {
      Impl_Trees_Types_node node1 = *node.left;
      lh = node1.height;
    }
    uint64_t rh;
    if (node.right == NULL)
      rh = 0ULL;
    else
    {
      Impl_Trees_Types_node node1 = *node.right;
      rh = node1.height;
    }
    if (lh > rh + 1ULL)
    {
      Impl_Trees_Types_node l_node = *node.left;
      uint64_t llh;
      if (l_node.left == NULL)
        llh = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *l_node.left;
        llh = node1.height;
      }
      uint64_t lrh;
      if (l_node.right == NULL)
        lrh = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *l_node.right;
        lrh = node1.height;
      }
      if (lrh > llh)
        return rotate_left_right(ptr);
      else
        return rotate_right(ptr);
    }
    else if (rh > lh + 1ULL)
    {
      Impl_Trees_Types_node r_node = *node.right;
      uint64_t rlh;
      if (r_node.left == NULL)
        rlh = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *r_node.left;
        rlh = node1.height;
      }
      uint64_t rrh;
      if (r_node.right == NULL)
        rrh = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *r_node.right;
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

Impl_Trees_Types_node
*Impl_AVL_M_insert_avl(
  Impl_Trees_Types_node *(*f1)(Impl_Trees_Types_node x0),
  void (*f2)(Impl_Trees_Types_node *x0),
  bool r,
  Impl_Trees_Types_node *ptr,
  Impl_Trees_Types_data new_data
)
{
  if (ptr == NULL)
  {
    Impl_Trees_Types_node *l = NULL;
    Impl_Trees_Types_node *r1 = NULL;
    uint64_t sr = 1ULL;
    uint64_t hr = 1ULL;
    Impl_Trees_Types_node
    n = { .data = new_data, .left = l, .right = r1, .size = sr, .height = hr };
    Impl_Trees_Types_node *ptr1 = f1(n);
    return ptr1;
  }
  else
  {
    Impl_Trees_Types_node node = *ptr;
    int64_t delta = Impl_Trees_Types_cmp(node.data, new_data);
    if (delta == (int64_t)0)
      if (r)
      {
        Impl_Trees_Types_node
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
      Impl_Trees_Types_node *new_left = Impl_AVL_M_insert_avl(f1, f2, r, node.left, new_data);
      uint64_t s1;
      if (new_left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (node.right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (new_left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (node.right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Types_node
      n = { .data = node.data, .left = new_left, .right = node.right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Types_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
    else
    {
      Impl_Trees_Types_node *new_right = Impl_AVL_M_insert_avl(f1, f2, r, node.right, new_data);
      uint64_t s1;
      if (node.left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (new_right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (node.left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (new_right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Types_node
      n = { .data = node.data, .left = node.left, .right = new_right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Types_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
  }
}

Impl_AVL_M_result
Impl_AVL_M_remove_leftmost_avl(
  Impl_Trees_Types_node *(*f1)(Impl_Trees_Types_node x0),
  void (*f2)(Impl_Trees_Types_node *x0),
  Impl_Trees_Types_node *ptr
)
{
  Impl_Trees_Types_node node = *ptr;
  if (node.left == NULL)
  {
    Impl_Trees_Types_data data = node.data;
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
      Impl_Trees_Types_node node1 = *r0.ptr;
      s1 = node1.size;
    }
    uint64_t s2;
    if (node.right == NULL)
      s2 = 0ULL;
    else
    {
      Impl_Trees_Types_node node1 = *node.right;
      s2 = node1.size;
    }
    uint64_t s = s1 + s2 + 1ULL;
    uint64_t h1;
    if (r0.ptr == NULL)
      h1 = 0ULL;
    else
    {
      Impl_Trees_Types_node node1 = *r0.ptr;
      h1 = node1.height;
    }
    uint64_t h2;
    if (node.right == NULL)
      h2 = 0ULL;
    else
    {
      Impl_Trees_Types_node node1 = *node.right;
      h2 = node1.height;
    }
    uint64_t ite;
    if (h1 > h2)
      ite = h1;
    else
      ite = h2;
    uint64_t h = ite + 1ULL;
    Impl_Trees_Types_node
    n = { .data = node.data, .left = r0.ptr, .right = node.right, .size = s, .height = h };
    *ptr = n;
    Impl_Trees_Types_node *new_ptr = ptr;
    Impl_Trees_Types_node *new_ptr1 = rebalance_avl(new_ptr);
    return ((Impl_AVL_M_result){ .ptr = new_ptr1, .data = r0.data });
  }
}

Impl_Trees_Types_node
*Impl_AVL_M_delete_avl(
  Impl_Trees_Types_node *(*f1)(Impl_Trees_Types_node x0),
  void (*f2)(Impl_Trees_Types_node *x0),
  Impl_Trees_Types_node *ptr,
  Impl_Trees_Types_data data_to_rm
)
{
  if (ptr == NULL)
    return ptr;
  else
  {
    Impl_Trees_Types_node node = *ptr;
    int64_t delta = Impl_Trees_Types_cmp(data_to_rm, node.data);
    if (delta == (int64_t)0)
    {
      Impl_Trees_Types_node node1 = *ptr;
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
          Impl_Trees_Types_node node2 = *node1.left;
          s1 = node2.size;
        }
        uint64_t s2;
        if (r0.ptr == NULL)
          s2 = 0ULL;
        else
        {
          Impl_Trees_Types_node node2 = *r0.ptr;
          s2 = node2.size;
        }
        uint64_t s = s1 + s2 + 1ULL;
        uint64_t h1;
        if (node1.left == NULL)
          h1 = 0ULL;
        else
        {
          Impl_Trees_Types_node node2 = *node1.left;
          h1 = node2.height;
        }
        uint64_t h2;
        if (r0.ptr == NULL)
          h2 = 0ULL;
        else
        {
          Impl_Trees_Types_node node2 = *r0.ptr;
          h2 = node2.height;
        }
        uint64_t ite;
        if (h1 > h2)
          ite = h1;
        else
          ite = h2;
        uint64_t h = ite + 1ULL;
        Impl_Trees_Types_node
        n = { .data = r0.data, .left = node1.left, .right = r0.ptr, .size = s, .height = h };
        *ptr = n;
        Impl_Trees_Types_node *new_ptr = ptr;
        Impl_Trees_Types_node *new_ptr1 = rebalance_avl(new_ptr);
        return new_ptr1;
      }
    }
    else if (delta < (int64_t)0)
    {
      Impl_Trees_Types_node *new_left = Impl_AVL_M_delete_avl(f1, f2, node.left, data_to_rm);
      uint64_t s1;
      if (new_left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (node.right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (new_left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (node.right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Types_node
      n = { .data = node.data, .left = new_left, .right = node.right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Types_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
    else
    {
      Impl_Trees_Types_node *new_right = Impl_AVL_M_delete_avl(f1, f2, node.right, data_to_rm);
      uint64_t s1;
      if (node.left == NULL)
        s1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.left;
        s1 = node1.size;
      }
      uint64_t s2;
      if (new_right == NULL)
        s2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_right;
        s2 = node1.size;
      }
      uint64_t s = s1 + s2 + 1ULL;
      uint64_t h1;
      if (node.left == NULL)
        h1 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *node.left;
        h1 = node1.height;
      }
      uint64_t h2;
      if (new_right == NULL)
        h2 = 0ULL;
      else
      {
        Impl_Trees_Types_node node1 = *new_right;
        h2 = node1.height;
      }
      uint64_t ite;
      if (h1 > h2)
        ite = h1;
      else
        ite = h2;
      uint64_t h = ite + 1ULL;
      Impl_Trees_Types_node
      n = { .data = node.data, .left = node.left, .right = new_right, .size = s, .height = h };
      *ptr = n;
      Impl_Trees_Types_node *new_ptr = ptr;
      return rebalance_avl(new_ptr);
    }
  }
}

static size_t snd__Prims_dtuple2__uint8_t_____size_t(Impl_Trees_Types_data x)
{
  return x.snd;
}

FStar_Pervasives_Native_option__size_t
Map_M_find(Impl_Trees_Types_node *ptr, Impl_Trees_Types_data v)
{
  if (ptr == NULL)
    return ((FStar_Pervasives_Native_option__size_t){ .tag = FStar_Pervasives_Native_None });
  else
  {
    Impl_Trees_Types_node node = *ptr;
    int64_t delta = Impl_Trees_Types_cmp(v, node.data);
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

extern Impl_Trees_Types_node **mmap_ptr_metadata(void);

void init_mmap_md(mmap_md *ret)
{
  Impl_Trees_Types_node **ptr = mmap_ptr_metadata();
  Impl_Trees_Types_node *tree = NULL;
  *ptr = tree;
  Steel_SpinLock_new_lock(&ret->lock);
  ret->data = ptr;
}

mmap_md metadata;

static Impl_Trees_Types_node *trees_malloc2(Impl_Trees_Types_node x)
{
  Steel_SpinLock_acquire(&Impl_Trees_Types_metadata_slabs.lock);
  uint8_t *ptr = SizeClass_allocate_size_class(Impl_Trees_Types_metadata_slabs.scs);
  Impl_Trees_Types_node *r;
  if (ptr == NULL)
    r = NULL;
  else
  {
    Impl_Trees_Types_node *r_ = Impl_Trees_Types_array_u8__to__ref_node(ptr);
    *r_ = x;
    r = r_;
  }
  Steel_SpinLock_release(&Impl_Trees_Types_metadata_slabs.lock);
  Impl_Trees_Types_node *r0 = r;
  return r0;
}

static void trees_free2(Impl_Trees_Types_node *r)
{
  Steel_SpinLock_acquire(&Impl_Trees_Types_metadata_slabs.lock);
  uint8_t *ptr = Impl_Trees_Types_ref_node__to__array_u8(r);
  uint8_t *pt0 = ptr;
  uint8_t *pt1 = Impl_Trees_Types_metadata_slabs.slab_region;
  ptrdiff_t diff = pt0 - pt1;
  size_t diff_sz = (size_t)diff;
  bool b = SizeClass_deallocate_size_class(Impl_Trees_Types_metadata_slabs.scs, ptr, diff_sz);
  if (b)
  {

  }
  Steel_SpinLock_release(&Impl_Trees_Types_metadata_slabs.lock);
}

static uint8_t *large_malloc(size_t size)
{
  Steel_SpinLock_acquire(&metadata.lock);
  Impl_Trees_Types_node *md_v0 = *metadata.data;
  uint64_t md_size;
  if (md_v0 == NULL)
    md_size = 0ULL;
  else
  {
    Impl_Trees_Types_node node = *md_v0;
    md_size = node.size;
  }
  uint8_t *r;
  if (md_size < 18446744073709551615ULL)
  {
    Impl_Trees_Types_node *md_v = *metadata.data;
    uint8_t *ptr0 = mmap_u8(size);
    uint8_t *ptr;
    if (ptr0 == NULL)
      ptr = ptr0;
    else
    {
      size_t size_ = PtrdiffWrapper_mmap_actual_size(size);
      bool b = Impl_BST_M_member(md_v, ((Impl_Trees_Types_data){ .fst = ptr0, .snd = size_ }));
      if (b)
        ptr = NULL;
      else
      {
        Impl_Trees_Types_node
        *md_v_ =
          Impl_AVL_M_insert_avl(trees_malloc2,
            trees_free2,
            false,
            md_v,
            ((Impl_Trees_Types_data){ .fst = ptr0, .snd = size_ }));
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
  Impl_Trees_Types_node *md_v = *metadata.data;
  Impl_Trees_Types_data k_elem = { .fst = ptr, .snd = (size_t)0U };
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
    Impl_Trees_Types_node
    *md_v_ =
      Impl_AVL_M_delete_avl(trees_malloc2,
        trees_free2,
        md_v,
        ((Impl_Trees_Types_data){ .fst = ptr, .snd = size1 }));
    *metadata.data = md_v_;
    r = true;
  }
  else
    r = false;
  Steel_SpinLock_release(&metadata.lock);
  bool b = r;
  return b;
}

static size_t large_getsize_aux(Impl_Trees_Types_node **metadata1, uint8_t *ptr)
{
  Impl_Trees_Types_node *md_v = *metadata1;
  FStar_Pervasives_Native_option__size_t
  size = Map_M_find(md_v, ((Impl_Trees_Types_data){ .fst = ptr, .snd = (size_t)0U }));
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
uint32_t
sizes[108U] =
  {
    16U, 32U, 64U, 80U, 96U, 112U, 128U, 160U, 192U, 224U, 256U, 320U, 384U, 448U, 512U, 640U, 768U,
    896U, 1024U, 1280U, 1536U, 1792U, 2048U, 2560U, 3072U, 3584U, 4096U, 16U, 32U, 64U, 80U, 96U,
    112U, 128U, 160U, 192U, 224U, 256U, 320U, 384U, 448U, 512U, 640U, 768U, 896U, 1024U, 1280U,
    1536U, 1792U, 2048U, 2560U, 3072U, 3584U, 4096U, 16U, 32U, 64U, 80U, 96U, 112U, 128U, 160U,
    192U, 224U, 256U, 320U, 384U, 448U, 512U, 640U, 768U, 896U, 1024U, 1280U, 1536U, 1792U, 2048U,
    2560U, 3072U, 3584U, 4096U, 16U, 32U, 64U, 80U, 96U, 112U, 128U, 160U, 192U, 224U, 256U, 320U,
    384U, 448U, 512U, 640U, 768U, 896U, 1024U, 1280U, 1536U, 1792U, 2048U, 2560U, 3072U, 3584U,
    4096U
  };

Main_Meta_size_classes_all Main_Meta_init(void)
{
  uint8_t *slab_region = mmap_u8_init((size_t)16777216U * (size_t)4096U * (size_t)108U);
  uint64_t *md_bm_region = mmap_u64_init((size_t)7247757312U);
  ArrayList_cell *md_region = mmap_cell_status_init((size_t)1811939328U);
  size_class *size_classes = mmap_sc_init((size_t)108U);
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
  uint32_t size = sizes[arena_id * (size_t)27U + i];
  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)27U + i].lock);
  uint8_t
  *r = allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)27U + i].data);
  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)27U + i].lock);
  uint8_t *ptr = r;
  uint8_t *ptr0 = ptr;
  if (!(ptr0 == NULL))
  {
    ptr0[(size_t)(size - 2U)] = 42U;
    ptr0[(size_t)(size - 1U)] = 23U;
  }
  return ptr0;
}

static uint8_t *slab_aligned_alloc(size_t arena_id, uint32_t alignment, uint32_t bytes)
{
  uint32_t size = sizes[arena_id * (size_t)27U + (size_t)0U];
  bool b = 4096U % size == 0U;
  if (b && bytes <= size - 2U && alignment <= size)
  {
    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)27U + (size_t)0U].lock);
    uint8_t
    *r =
      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)27U + (size_t)0U].data);
    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)27U + (size_t)0U].lock);
    uint8_t *ptr = r;
    uint8_t *ptr0 = ptr;
    if (!(ptr0 == NULL))
    {
      ptr0[(size_t)(size - 2U)] = 42U;
      ptr0[(size_t)(size - 1U)] = 23U;
    }
    return ptr0;
  }
  else
  {
    uint32_t size1 = sizes[arena_id * (size_t)27U + (size_t)1U];
    bool b1 = 4096U % size1 == 0U;
    if (b1 && bytes <= size1 - 2U && alignment <= size1)
    {
      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
        * (size_t)27U
        + (size_t)1U].lock);
      uint8_t
      *r =
        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)27U + (size_t)1U].data);
      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
        * (size_t)27U
        + (size_t)1U].lock);
      uint8_t *ptr = r;
      uint8_t *ptr0 = ptr;
      if (!(ptr0 == NULL))
      {
        ptr0[(size_t)(size1 - 2U)] = 42U;
        ptr0[(size_t)(size1 - 1U)] = 23U;
      }
      return ptr0;
    }
    else
    {
      uint32_t size2 = sizes[arena_id * (size_t)27U + (size_t)2U];
      bool b2 = 4096U % size2 == 0U;
      if (b2 && bytes <= size2 - 2U && alignment <= size2)
      {
        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
          * (size_t)27U
          + (size_t)2U].lock);
        uint8_t
        *r =
          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
            * (size_t)27U
            + (size_t)2U].data);
        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
          * (size_t)27U
          + (size_t)2U].lock);
        uint8_t *ptr = r;
        uint8_t *ptr0 = ptr;
        if (!(ptr0 == NULL))
        {
          ptr0[(size_t)(size2 - 2U)] = 42U;
          ptr0[(size_t)(size2 - 1U)] = 23U;
        }
        return ptr0;
      }
      else
      {
        uint32_t size3 = sizes[arena_id * (size_t)27U + (size_t)3U];
        bool b3 = 4096U % size3 == 0U;
        if (b3 && bytes <= size3 - 2U && alignment <= size3)
        {
          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
            * (size_t)27U
            + (size_t)3U].lock);
          uint8_t
          *r =
            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
              * (size_t)27U
              + (size_t)3U].data);
          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
            * (size_t)27U
            + (size_t)3U].lock);
          uint8_t *ptr = r;
          uint8_t *ptr0 = ptr;
          if (!(ptr0 == NULL))
          {
            ptr0[(size_t)(size3 - 2U)] = 42U;
            ptr0[(size_t)(size3 - 1U)] = 23U;
          }
          return ptr0;
        }
        else
        {
          uint32_t size4 = sizes[arena_id * (size_t)27U + (size_t)4U];
          bool b4 = 4096U % size4 == 0U;
          if (b4 && bytes <= size4 - 2U && alignment <= size4)
          {
            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
              * (size_t)27U
              + (size_t)4U].lock);
            uint8_t
            *r =
              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                * (size_t)27U
                + (size_t)4U].data);
            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
              * (size_t)27U
              + (size_t)4U].lock);
            uint8_t *ptr = r;
            uint8_t *ptr0 = ptr;
            if (!(ptr0 == NULL))
            {
              ptr0[(size_t)(size4 - 2U)] = 42U;
              ptr0[(size_t)(size4 - 1U)] = 23U;
            }
            return ptr0;
          }
          else
          {
            uint32_t size5 = sizes[arena_id * (size_t)27U + (size_t)5U];
            bool b5 = 4096U % size5 == 0U;
            if (b5 && bytes <= size5 - 2U && alignment <= size5)
            {
              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                * (size_t)27U
                + (size_t)5U].lock);
              uint8_t
              *r =
                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                  * (size_t)27U
                  + (size_t)5U].data);
              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                * (size_t)27U
                + (size_t)5U].lock);
              uint8_t *ptr = r;
              uint8_t *ptr0 = ptr;
              if (!(ptr0 == NULL))
              {
                ptr0[(size_t)(size5 - 2U)] = 42U;
                ptr0[(size_t)(size5 - 1U)] = 23U;
              }
              return ptr0;
            }
            else
            {
              uint32_t size6 = sizes[arena_id * (size_t)27U + (size_t)6U];
              bool b6 = 4096U % size6 == 0U;
              if (b6 && bytes <= size6 - 2U && alignment <= size6)
              {
                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                  * (size_t)27U
                  + (size_t)6U].lock);
                uint8_t
                *r =
                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                    * (size_t)27U
                    + (size_t)6U].data);
                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                  * (size_t)27U
                  + (size_t)6U].lock);
                uint8_t *ptr = r;
                uint8_t *ptr0 = ptr;
                if (!(ptr0 == NULL))
                {
                  ptr0[(size_t)(size6 - 2U)] = 42U;
                  ptr0[(size_t)(size6 - 1U)] = 23U;
                }
                return ptr0;
              }
              else
              {
                uint32_t size7 = sizes[arena_id * (size_t)27U + (size_t)7U];
                bool b7 = 4096U % size7 == 0U;
                if (b7 && bytes <= size7 - 2U && alignment <= size7)
                {
                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                    * (size_t)27U
                    + (size_t)7U].lock);
                  uint8_t
                  *r =
                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                      * (size_t)27U
                      + (size_t)7U].data);
                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                    * (size_t)27U
                    + (size_t)7U].lock);
                  uint8_t *ptr = r;
                  uint8_t *ptr0 = ptr;
                  if (!(ptr0 == NULL))
                  {
                    ptr0[(size_t)(size7 - 2U)] = 42U;
                    ptr0[(size_t)(size7 - 1U)] = 23U;
                  }
                  return ptr0;
                }
                else
                {
                  uint32_t size8 = sizes[arena_id * (size_t)27U + (size_t)8U];
                  bool b8 = 4096U % size8 == 0U;
                  if (b8 && bytes <= size8 - 2U && alignment <= size8)
                  {
                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                      * (size_t)27U
                      + (size_t)8U].lock);
                    uint8_t
                    *r =
                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                        * (size_t)27U
                        + (size_t)8U].data);
                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                      * (size_t)27U
                      + (size_t)8U].lock);
                    uint8_t *ptr = r;
                    uint8_t *ptr0 = ptr;
                    if (!(ptr0 == NULL))
                    {
                      ptr0[(size_t)(size8 - 2U)] = 42U;
                      ptr0[(size_t)(size8 - 1U)] = 23U;
                    }
                    return ptr0;
                  }
                  else
                  {
                    uint32_t size9 = sizes[arena_id * (size_t)27U + (size_t)9U];
                    bool b9 = 4096U % size9 == 0U;
                    if (b9 && bytes <= size9 - 2U && alignment <= size9)
                    {
                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                        * (size_t)27U
                        + (size_t)9U].lock);
                      uint8_t
                      *r =
                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                          * (size_t)27U
                          + (size_t)9U].data);
                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                        * (size_t)27U
                        + (size_t)9U].lock);
                      uint8_t *ptr = r;
                      uint8_t *ptr0 = ptr;
                      if (!(ptr0 == NULL))
                      {
                        ptr0[(size_t)(size9 - 2U)] = 42U;
                        ptr0[(size_t)(size9 - 1U)] = 23U;
                      }
                      return ptr0;
                    }
                    else
                    {
                      uint32_t size10 = sizes[arena_id * (size_t)27U + (size_t)10U];
                      bool b10 = 4096U % size10 == 0U;
                      if (b10 && bytes <= size10 - 2U && alignment <= size10)
                      {
                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                          * (size_t)27U
                          + (size_t)10U].lock);
                        uint8_t
                        *r =
                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                            * (size_t)27U
                            + (size_t)10U].data);
                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                          * (size_t)27U
                          + (size_t)10U].lock);
                        uint8_t *ptr = r;
                        uint8_t *ptr0 = ptr;
                        if (!(ptr0 == NULL))
                        {
                          ptr0[(size_t)(size10 - 2U)] = 42U;
                          ptr0[(size_t)(size10 - 1U)] = 23U;
                        }
                        return ptr0;
                      }
                      else
                      {
                        uint32_t size11 = sizes[arena_id * (size_t)27U + (size_t)11U];
                        bool b11 = 4096U % size11 == 0U;
                        if (b11 && bytes <= size11 - 2U && alignment <= size11)
                        {
                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                            * (size_t)27U
                            + (size_t)11U].lock);
                          uint8_t
                          *r =
                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                              * (size_t)27U
                              + (size_t)11U].data);
                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                            * (size_t)27U
                            + (size_t)11U].lock);
                          uint8_t *ptr = r;
                          uint8_t *ptr0 = ptr;
                          if (!(ptr0 == NULL))
                          {
                            ptr0[(size_t)(size11 - 2U)] = 42U;
                            ptr0[(size_t)(size11 - 1U)] = 23U;
                          }
                          return ptr0;
                        }
                        else
                        {
                          uint32_t size12 = sizes[arena_id * (size_t)27U + (size_t)12U];
                          bool b12 = 4096U % size12 == 0U;
                          if (b12 && bytes <= size12 - 2U && alignment <= size12)
                          {
                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                              * (size_t)27U
                              + (size_t)12U].lock);
                            uint8_t
                            *r =
                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                * (size_t)27U
                                + (size_t)12U].data);
                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                              * (size_t)27U
                              + (size_t)12U].lock);
                            uint8_t *ptr = r;
                            uint8_t *ptr0 = ptr;
                            if (!(ptr0 == NULL))
                            {
                              ptr0[(size_t)(size12 - 2U)] = 42U;
                              ptr0[(size_t)(size12 - 1U)] = 23U;
                            }
                            return ptr0;
                          }
                          else
                          {
                            uint32_t size13 = sizes[arena_id * (size_t)27U + (size_t)13U];
                            bool b13 = 4096U % size13 == 0U;
                            if (b13 && bytes <= size13 - 2U && alignment <= size13)
                            {
                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                * (size_t)27U
                                + (size_t)13U].lock);
                              uint8_t
                              *r =
                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                  * (size_t)27U
                                  + (size_t)13U].data);
                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                * (size_t)27U
                                + (size_t)13U].lock);
                              uint8_t *ptr = r;
                              uint8_t *ptr0 = ptr;
                              if (!(ptr0 == NULL))
                              {
                                ptr0[(size_t)(size13 - 2U)] = 42U;
                                ptr0[(size_t)(size13 - 1U)] = 23U;
                              }
                              return ptr0;
                            }
                            else
                            {
                              uint32_t size14 = sizes[arena_id * (size_t)27U + (size_t)14U];
                              bool b14 = 4096U % size14 == 0U;
                              if (b14 && bytes <= size14 - 2U && alignment <= size14)
                              {
                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                  * (size_t)27U
                                  + (size_t)14U].lock);
                                uint8_t
                                *r =
                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                    * (size_t)27U
                                    + (size_t)14U].data);
                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                  * (size_t)27U
                                  + (size_t)14U].lock);
                                uint8_t *ptr = r;
                                uint8_t *ptr0 = ptr;
                                if (!(ptr0 == NULL))
                                {
                                  ptr0[(size_t)(size14 - 2U)] = 42U;
                                  ptr0[(size_t)(size14 - 1U)] = 23U;
                                }
                                return ptr0;
                              }
                              else
                              {
                                uint32_t size15 = sizes[arena_id * (size_t)27U + (size_t)15U];
                                bool b15 = 4096U % size15 == 0U;
                                if (b15 && bytes <= size15 - 2U && alignment <= size15)
                                {
                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                    * (size_t)27U
                                    + (size_t)15U].lock);
                                  uint8_t
                                  *r =
                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                      * (size_t)27U
                                      + (size_t)15U].data);
                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                    * (size_t)27U
                                    + (size_t)15U].lock);
                                  uint8_t *ptr = r;
                                  uint8_t *ptr0 = ptr;
                                  if (!(ptr0 == NULL))
                                  {
                                    ptr0[(size_t)(size15 - 2U)] = 42U;
                                    ptr0[(size_t)(size15 - 1U)] = 23U;
                                  }
                                  return ptr0;
                                }
                                else
                                {
                                  uint32_t size16 = sizes[arena_id * (size_t)27U + (size_t)16U];
                                  bool b16 = 4096U % size16 == 0U;
                                  if (b16 && bytes <= size16 - 2U && alignment <= size16)
                                  {
                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                      * (size_t)27U
                                      + (size_t)16U].lock);
                                    uint8_t
                                    *r =
                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)27U
                                        + (size_t)16U].data);
                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                      * (size_t)27U
                                      + (size_t)16U].lock);
                                    uint8_t *ptr = r;
                                    uint8_t *ptr0 = ptr;
                                    if (!(ptr0 == NULL))
                                    {
                                      ptr0[(size_t)(size16 - 2U)] = 42U;
                                      ptr0[(size_t)(size16 - 1U)] = 23U;
                                    }
                                    return ptr0;
                                  }
                                  else
                                  {
                                    uint32_t size17 = sizes[arena_id * (size_t)27U + (size_t)17U];
                                    bool b17 = 4096U % size17 == 0U;
                                    if (b17 && bytes <= size17 - 2U && alignment <= size17)
                                    {
                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)27U
                                        + (size_t)17U].lock);
                                      uint8_t
                                      *r =
                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)27U
                                          + (size_t)17U].data);
                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)27U
                                        + (size_t)17U].lock);
                                      uint8_t *ptr = r;
                                      uint8_t *ptr0 = ptr;
                                      if (!(ptr0 == NULL))
                                      {
                                        ptr0[(size_t)(size17 - 2U)] = 42U;
                                        ptr0[(size_t)(size17 - 1U)] = 23U;
                                      }
                                      return ptr0;
                                    }
                                    else
                                    {
                                      uint32_t size18 = sizes[arena_id * (size_t)27U + (size_t)18U];
                                      bool b18 = 4096U % size18 == 0U;
                                      if (b18 && bytes <= size18 - 2U && alignment <= size18)
                                      {
                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)27U
                                          + (size_t)18U].lock);
                                        uint8_t
                                        *r =
                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)27U
                                            + (size_t)18U].data);
                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)27U
                                          + (size_t)18U].lock);
                                        uint8_t *ptr = r;
                                        uint8_t *ptr0 = ptr;
                                        if (!(ptr0 == NULL))
                                        {
                                          ptr0[(size_t)(size18 - 2U)] = 42U;
                                          ptr0[(size_t)(size18 - 1U)] = 23U;
                                        }
                                        return ptr0;
                                      }
                                      else
                                      {
                                        uint32_t
                                        size19 = sizes[arena_id * (size_t)27U + (size_t)19U];
                                        bool b19 = 4096U % size19 == 0U;
                                        if (b19 && bytes <= size19 - 2U && alignment <= size19)
                                        {
                                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)27U
                                            + (size_t)19U].lock);
                                          uint8_t
                                          *r =
                                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)27U
                                              + (size_t)19U].data);
                                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)27U
                                            + (size_t)19U].lock);
                                          uint8_t *ptr = r;
                                          uint8_t *ptr0 = ptr;
                                          if (!(ptr0 == NULL))
                                          {
                                            ptr0[(size_t)(size19 - 2U)] = 42U;
                                            ptr0[(size_t)(size19 - 1U)] = 23U;
                                          }
                                          return ptr0;
                                        }
                                        else
                                        {
                                          uint32_t
                                          size20 = sizes[arena_id * (size_t)27U + (size_t)20U];
                                          bool b20 = 4096U % size20 == 0U;
                                          if (b20 && bytes <= size20 - 2U && alignment <= size20)
                                          {
                                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)27U
                                              + (size_t)20U].lock);
                                            uint8_t
                                            *r =
                                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)27U
                                                + (size_t)20U].data);
                                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)27U
                                              + (size_t)20U].lock);
                                            uint8_t *ptr = r;
                                            uint8_t *ptr0 = ptr;
                                            if (!(ptr0 == NULL))
                                            {
                                              ptr0[(size_t)(size20 - 2U)] = 42U;
                                              ptr0[(size_t)(size20 - 1U)] = 23U;
                                            }
                                            return ptr0;
                                          }
                                          else
                                          {
                                            uint32_t
                                            size21 = sizes[arena_id * (size_t)27U + (size_t)21U];
                                            bool b21 = 4096U % size21 == 0U;
                                            if (b21 && bytes <= size21 - 2U && alignment <= size21)
                                            {
                                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)27U
                                                + (size_t)21U].lock);
                                              uint8_t
                                              *r =
                                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)27U
                                                  + (size_t)21U].data);
                                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)27U
                                                + (size_t)21U].lock);
                                              uint8_t *ptr = r;
                                              uint8_t *ptr0 = ptr;
                                              if (!(ptr0 == NULL))
                                              {
                                                ptr0[(size_t)(size21 - 2U)] = 42U;
                                                ptr0[(size_t)(size21 - 1U)] = 23U;
                                              }
                                              return ptr0;
                                            }
                                            else
                                            {
                                              uint32_t
                                              size22 = sizes[arena_id * (size_t)27U + (size_t)22U];
                                              bool b22 = 4096U % size22 == 0U;
                                              if
                                              (b22 && bytes <= size22 - 2U && alignment <= size22)
                                              {
                                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)27U
                                                  + (size_t)22U].lock);
                                                uint8_t
                                                *r =
                                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)27U
                                                    + (size_t)22U].data);
                                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)27U
                                                  + (size_t)22U].lock);
                                                uint8_t *ptr = r;
                                                uint8_t *ptr0 = ptr;
                                                if (!(ptr0 == NULL))
                                                {
                                                  ptr0[(size_t)(size22 - 2U)] = 42U;
                                                  ptr0[(size_t)(size22 - 1U)] = 23U;
                                                }
                                                return ptr0;
                                              }
                                              else
                                              {
                                                uint32_t
                                                size23 = sizes[arena_id * (size_t)27U + (size_t)23U];
                                                bool b23 = 4096U % size23 == 0U;
                                                if
                                                (b23 && bytes <= size23 - 2U && alignment <= size23)
                                                {
                                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)27U
                                                    + (size_t)23U].lock);
                                                  uint8_t
                                                  *r =
                                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)27U
                                                      + (size_t)23U].data);
                                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)27U
                                                    + (size_t)23U].lock);
                                                  uint8_t *ptr = r;
                                                  uint8_t *ptr0 = ptr;
                                                  if (!(ptr0 == NULL))
                                                  {
                                                    ptr0[(size_t)(size23 - 2U)] = 42U;
                                                    ptr0[(size_t)(size23 - 1U)] = 23U;
                                                  }
                                                  return ptr0;
                                                }
                                                else
                                                {
                                                  uint32_t
                                                  size24 =
                                                    sizes[arena_id
                                                    * (size_t)27U
                                                    + (size_t)24U];
                                                  bool b24 = 4096U % size24 == 0U;
                                                  if
                                                  (
                                                    b24
                                                    && bytes <= size24 - 2U
                                                    && alignment <= size24
                                                  )
                                                  {
                                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)27U
                                                      + (size_t)24U].lock);
                                                    uint8_t
                                                    *r =
                                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)27U
                                                        + (size_t)24U].data);
                                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)27U
                                                      + (size_t)24U].lock);
                                                    uint8_t *ptr = r;
                                                    uint8_t *ptr0 = ptr;
                                                    if (!(ptr0 == NULL))
                                                    {
                                                      ptr0[(size_t)(size24 - 2U)] = 42U;
                                                      ptr0[(size_t)(size24 - 1U)] = 23U;
                                                    }
                                                    return ptr0;
                                                  }
                                                  else
                                                  {
                                                    uint32_t
                                                    size25 =
                                                      sizes[arena_id
                                                      * (size_t)27U
                                                      + (size_t)25U];
                                                    bool b25 = 4096U % size25 == 0U;
                                                    if
                                                    (
                                                      b25
                                                      && bytes <= size25 - 2U
                                                      && alignment <= size25
                                                    )
                                                    {
                                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)27U
                                                        + (size_t)25U].lock);
                                                      uint8_t
                                                      *r =
                                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)27U
                                                          + (size_t)25U].data);
                                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)27U
                                                        + (size_t)25U].lock);
                                                      uint8_t *ptr = r;
                                                      uint8_t *ptr0 = ptr;
                                                      if (!(ptr0 == NULL))
                                                      {
                                                        ptr0[(size_t)(size25 - 2U)] = 42U;
                                                        ptr0[(size_t)(size25 - 1U)] = 23U;
                                                      }
                                                      return ptr0;
                                                    }
                                                    else
                                                    {
                                                      uint32_t
                                                      size26 =
                                                        sizes[arena_id
                                                        * (size_t)27U
                                                        + (size_t)26U];
                                                      bool b26 = 4096U % size26 == 0U;
                                                      if
                                                      (
                                                        b26
                                                        && bytes <= size26 - 2U
                                                        && alignment <= size26
                                                      )
                                                      {
                                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)27U
                                                          + (size_t)26U].lock);
                                                        uint8_t
                                                        *r =
                                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                            * (size_t)27U
                                                            + (size_t)26U].data);
                                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)27U
                                                          + (size_t)26U].lock);
                                                        uint8_t *ptr = r;
                                                        uint8_t *ptr0 = ptr;
                                                        if (!(ptr0 == NULL))
                                                        {
                                                          ptr0[(size_t)(size26 - 2U)] = 42U;
                                                          ptr0[(size_t)(size26 - 1U)] = 23U;
                                                        }
                                                        return ptr0;
                                                      }
                                                      else
                                                        return NULL;
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
  uint32_t size = sizes[index];
  size_t rem_slot = diff_sz % (size_t)4096U;
  if (rem_slot % (size_t)size == (size_t)0U)
    return (size_t)(size - 2U);
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
  uint32_t size = sizes[index];
  size_t rem_slab = diff_sz % (size_t)68719476736U;
  size_t rem_slot = diff_sz % (size_t)4096U;
  if (rem_slot % (size_t)size == (size_t)0U)
  {
    uint8_t magic1 = ptr[(size_t)(size - 2U)];
    uint8_t magic2 = ptr[(size_t)(size - 1U)];
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

uint8_t *StarMalloc_malloc(size_t arena_id, size_t size)
{
  size_t threshold = (size_t)4096U - (size_t)2U;
  if (size <= threshold)
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
        StarMalloc_malloc_zeroing_die(ptr);
        return NULL;
      }
    }
  }
  else
  {
    size_t size_;
    if (size <= (size_t)4096U)
      size_ = (size_t)4096U + (size_t)1U;
    else
      size_ = size;
    uint8_t *r = large_malloc(size_);
    return r;
  }
}

uint8_t *StarMalloc_aligned_alloc(size_t arena_id, size_t alignment, size_t size)
{
  size_t page_as_sz = (size_t)4096U;
  bool check = alignment > (size_t)0U && (size_t)4096U % alignment == (size_t)0U;
  if (check)
  {
    uint32_t alignment_as_u32 = (uint32_t)alignment;
    size_t threshold = page_as_sz - (size_t)2U;
    if (size <= threshold)
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
          StarMalloc_malloc_zeroing_die(ptr);
          return NULL;
        }
      }
    }
    else
    {
      size_t size_;
      if (size <= (size_t)4096U)
        size_ = (size_t)4096U + (size_t)1U;
      else
        size_ = size;
      uint8_t *ptr = large_malloc(size_);
      return ptr;
    }
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
        Main_Meta_sc_all.slab_region + slab_region_size);
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
      Main_Meta_sc_all.slab_region + slab_region_size);
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
      return NULL;
  }
  else
  {
    size_t old_size = StarMalloc_getsize(ptr);
    bool old_allocation_is_small = old_size <= (size_t)4096U;
    if (old_size == (size_t)0U)
      return NULL;
    else if (new_size <= old_size && !old_allocation_is_small)
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
          return NULL;
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

