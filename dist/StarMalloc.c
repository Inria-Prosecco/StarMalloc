// SPDX-License-Identifier: Apache-2.0


#include "internal/StarMalloc.h"

#include "internal/Slabs2.h"

static uint32_t avl_data_size = 64U;

extern int64_t Impl_Trees_Cast_M_cmp(Impl_Trees_Cast_M_data uu___, Impl_Trees_Cast_M_data x0);

extern uint8_t *Impl_Trees_Cast_M_ref_node__to__array_u8(Impl_Trees_Cast_M_node *x);

extern Impl_Trees_Cast_M_node *Impl_Trees_Cast_M_array_u8__to__ref_node(uint8_t *arr);

size_t Main_metadata_max_ex;

size_t Main_sc_slab_region_size;

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

size_t Main_slab_region_size;

static void
init_size_class(
  size_t offset,
  size_t k,
  uint8_t *slab_region,
  uint64_t *md_bm_region,
  ArrayList_cell *md_region,
  size_class *size_classes,
  const Constants_sc_union *sizes
)
{
  size_t idx = offset + k;
  Constants_sc_union size = sizes[idx];
  if (size.tag == Constants_Sc)
  {
    uint32_t size1 = size.case_Sc;
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
        .size = { .tag = Constants_Sc, { .case_Sc = size1 } }, .is_extended = false,
        .slabs_idxs = r_idxs, .md_count = md_count, .slab_region = slab_region_,
        .md_bm_region = md_bm_region_, .md_bm_region_b = NULL, .md_region = md_region_
      };
    SizeClass_size_class_struct_ data = scs;
    Steel_SpinLock_new_lock(&size_classes[k].lock);
    size_classes[k].data = data;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static void
init_size_class2(
  size_t offset,
  size_t k,
  uint8_t *slab_region,
  bool *md_bm_region,
  ArrayList_cell *md_region,
  size_class *size_classes,
  const Constants_sc_union *sizes
)
{
  size_t idx = offset + k;
  Constants_sc_union size = sizes[idx];
  if (size.tag == Constants_Sc_ex)
  {
    uint32_t size1 = size.case_Sc_ex;
    static_assert(UINT32_MAX <= SIZE_MAX);
    uint8_t
    *slab_region_ = slab_region + SlabsCommon2_metadata_max_ex * SlabsCommon2_slab_size * k;
    bool *md_bm_region_ = md_bm_region + SlabsCommon2_metadata_max_ex * k;
    ArrayList_cell *md_region_ = md_region + SlabsCommon2_metadata_max_ex * k;
    size_t *r_idxs = mmap_array_us_init((size_t)7U);
    init_idxs(r_idxs);
    size_t *md_count = mmap_ptr_us_init();
    *md_count = (size_t)0U;
    SizeClass_size_class_struct_
    scs =
      {
        .size = { .tag = Constants_Sc_ex, { .case_Sc_ex = size1 } }, .is_extended = true,
        .slabs_idxs = r_idxs, .md_count = md_count, .slab_region = slab_region_,
        .md_bm_region = NULL, .md_bm_region_b = md_bm_region_, .md_region = md_region_
      };
    SizeClass_size_class_struct_ data = scs;
    Steel_SpinLock_new_lock(&size_classes[k].lock);
    size_classes[k].data = data;
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

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
      .size = { .tag = Constants_Sc, { .case_Sc = avl_data_size } }, .is_extended = false,
      .slabs_idxs = r_idxs, .md_count = md_count, .slab_region = slab_region,
      .md_bm_region = md_bm_region, .md_bm_region_b = NULL, .md_region = md_region
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
  uint8_t *ptr = SizeClass_allocate_size_class_sc(Impl_Trees_Types_metadata_slabs.scs);
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
  bool b = SizeClass_deallocate_size_class_sc(Impl_Trees_Types_metadata_slabs.scs, ptr, diff_sz);
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
Constants_sc_union
sizes[124U] =
  {
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 16U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 32U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 64U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 80U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 96U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 112U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 128U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 160U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 192U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 224U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 256U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 320U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 384U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 448U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 512U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 640U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 768U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 896U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1024U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1280U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1536U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1792U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2048U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2560U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3072U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3584U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 4096U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 5120U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 6144U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 7168U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 8192U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 16U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 32U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 64U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 80U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 96U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 112U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 128U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 160U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 192U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 224U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 256U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 320U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 384U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 448U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 512U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 640U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 768U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 896U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1024U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1280U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1536U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1792U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2048U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2560U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3072U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3584U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 4096U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 5120U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 6144U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 7168U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 8192U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 16U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 32U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 64U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 80U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 96U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 112U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 128U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 160U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 192U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 224U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 256U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 320U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 384U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 448U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 512U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 640U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 768U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 896U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1024U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1280U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1536U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1792U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2048U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2560U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3072U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3584U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 4096U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 5120U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 6144U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 7168U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 8192U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 16U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 32U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 64U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 80U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 96U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 112U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 128U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 160U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 192U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 224U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 256U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 320U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 384U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 448U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 512U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 640U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 768U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 896U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1024U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1280U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1536U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 1792U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2048U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 2560U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3072U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 3584U } }),
    ((Constants_sc_union){ .tag = Constants_Sc, { .case_Sc = 4096U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 5120U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 6144U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 7168U } }),
    ((Constants_sc_union){ .tag = Constants_Sc_ex, { .case_Sc_ex = 8192U } })
  };

typedef struct tuple4_s
{
  size_t x;
  size_t y;
  size_t z;
  size_t w;
}
tuple4;

static tuple4 gen_arena_sizes(void)
{
  size_t arena_slab_region_size = Main_sc_slab_region_size * (size_t)31U;
  size_t arena_md_bm_region_size = (size_t)1811939328U;
  size_t arena_md_bm_region_b_size = Main_metadata_max_ex * (size_t)4U;
  size_t arena_md_region_size = (size_t)452984832U + Main_metadata_max_ex * (size_t)4U;
  return
    (
      (tuple4){
        .x = arena_slab_region_size,
        .y = arena_md_bm_region_size,
        .z = arena_md_bm_region_b_size,
        .w = arena_md_region_size
      }
    );
}

Main_Meta_size_classes_all Main_Meta_init(void)
{
  tuple4 arena_sizes = gen_arena_sizes();
  uint8_t *slab_region = mmap_u8_init(arena_sizes.x * (size_t)4U);
  uint64_t *md_bm_region = mmap_u64_init(arena_sizes.y * (size_t)4U);
  bool *md_bm_region_b = mmap_bool_init(arena_sizes.z * (size_t)4U);
  ArrayList_cell *md_region = mmap_cell_status_init(arena_sizes.w * (size_t)4U);
  size_class *size_classes = mmap_sc_init((size_t)124U);
  size_t offset_ = (size_t)0U;
  init_size_class(offset_,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)4U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)5U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)6U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)7U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)8U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)9U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)10U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)11U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)12U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)13U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)14U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)15U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)16U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)17U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)18U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)19U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)20U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)21U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)22U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)23U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)24U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)25U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class(offset_,
    (size_t)26U,
    slab_region + arena_sizes.x * (size_t)0U,
    md_bm_region + arena_sizes.y * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U,
    size_classes,
    sizes);
  init_size_class2(offset_ + (size_t)27U,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)0U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U + (size_t)452984832U,
    size_classes + (size_t)27U,
    sizes);
  init_size_class2(offset_ + (size_t)27U,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)0U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U + (size_t)452984832U,
    size_classes + (size_t)27U,
    sizes);
  init_size_class2(offset_ + (size_t)27U,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)0U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U + (size_t)452984832U,
    size_classes + (size_t)27U,
    sizes);
  init_size_class2(offset_ + (size_t)27U,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)0U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)0U,
    md_region + arena_sizes.w * (size_t)0U + (size_t)452984832U,
    size_classes + (size_t)27U,
    sizes);
  size_t offset_0 = (size_t)31U;
  init_size_class(offset_0,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)4U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)5U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)6U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)7U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)8U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)9U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)10U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)11U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)12U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)13U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)14U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)15U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)16U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)17U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)18U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)19U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)20U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)21U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)22U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)23U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)24U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)25U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class(offset_0,
    (size_t)26U,
    slab_region + arena_sizes.x * (size_t)1U,
    md_bm_region + arena_sizes.y * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U,
    size_classes + (size_t)31U,
    sizes);
  init_size_class2(offset_0 + (size_t)27U,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)1U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U + (size_t)452984832U,
    size_classes + (size_t)31U + (size_t)27U,
    sizes);
  init_size_class2(offset_0 + (size_t)27U,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)1U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U + (size_t)452984832U,
    size_classes + (size_t)31U + (size_t)27U,
    sizes);
  init_size_class2(offset_0 + (size_t)27U,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)1U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U + (size_t)452984832U,
    size_classes + (size_t)31U + (size_t)27U,
    sizes);
  init_size_class2(offset_0 + (size_t)27U,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)1U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)1U,
    md_region + arena_sizes.w * (size_t)1U + (size_t)452984832U,
    size_classes + (size_t)31U + (size_t)27U,
    sizes);
  size_t offset_1 = (size_t)62U;
  init_size_class(offset_1,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)4U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)5U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)6U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)7U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)8U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)9U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)10U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)11U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)12U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)13U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)14U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)15U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)16U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)17U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)18U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)19U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)20U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)21U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)22U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)23U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)24U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)25U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class(offset_1,
    (size_t)26U,
    slab_region + arena_sizes.x * (size_t)2U,
    md_bm_region + arena_sizes.y * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U,
    size_classes + (size_t)62U,
    sizes);
  init_size_class2(offset_1 + (size_t)27U,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)2U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U + (size_t)452984832U,
    size_classes + (size_t)62U + (size_t)27U,
    sizes);
  init_size_class2(offset_1 + (size_t)27U,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)2U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U + (size_t)452984832U,
    size_classes + (size_t)62U + (size_t)27U,
    sizes);
  init_size_class2(offset_1 + (size_t)27U,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)2U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U + (size_t)452984832U,
    size_classes + (size_t)62U + (size_t)27U,
    sizes);
  init_size_class2(offset_1 + (size_t)27U,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)2U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)2U,
    md_region + arena_sizes.w * (size_t)2U + (size_t)452984832U,
    size_classes + (size_t)62U + (size_t)27U,
    sizes);
  size_t offset_2 = (size_t)93U;
  init_size_class(offset_2,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)4U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)5U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)6U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)7U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)8U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)9U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)10U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)11U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)12U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)13U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)14U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)15U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)16U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)17U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)18U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)19U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)20U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)21U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)22U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)23U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)24U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)25U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class(offset_2,
    (size_t)26U,
    slab_region + arena_sizes.x * (size_t)3U,
    md_bm_region + arena_sizes.y * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U,
    size_classes + (size_t)93U,
    sizes);
  init_size_class2(offset_2 + (size_t)27U,
    (size_t)0U,
    slab_region + arena_sizes.x * (size_t)3U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U + (size_t)452984832U,
    size_classes + (size_t)93U + (size_t)27U,
    sizes);
  init_size_class2(offset_2 + (size_t)27U,
    (size_t)1U,
    slab_region + arena_sizes.x * (size_t)3U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U + (size_t)452984832U,
    size_classes + (size_t)93U + (size_t)27U,
    sizes);
  init_size_class2(offset_2 + (size_t)27U,
    (size_t)2U,
    slab_region + arena_sizes.x * (size_t)3U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U + (size_t)452984832U,
    size_classes + (size_t)93U + (size_t)27U,
    sizes);
  init_size_class2(offset_2 + (size_t)27U,
    (size_t)3U,
    slab_region + arena_sizes.x * (size_t)3U + (size_t)16777216U * (size_t)4096U * (size_t)27U,
    md_bm_region_b + arena_sizes.z * (size_t)3U,
    md_region + arena_sizes.w * (size_t)3U + (size_t)452984832U,
    size_classes + (size_t)93U + (size_t)27U,
    sizes);
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
  Constants_sc_union size = sizes[arena_id * (size_t)31U + i];
  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)31U + i].lock);
  uint8_t
  *r = allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)31U + i].data);
  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)31U + i].lock);
  uint8_t *ptr = r;
  uint8_t *ptr0 = ptr;
  uint32_t size1;
  if (size.tag == Constants_Sc)
    size1 = size.case_Sc;
  else if (size.tag == Constants_Sc_ex)
    size1 = size.case_Sc_ex;
  else
    size1 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  if (!(ptr0 == NULL))
  {
    ptr0[(size_t)(size1 - 2U)] = 42U;
    ptr0[(size_t)(size1 - 1U)] = 23U;
  }
  return ptr0;
}

static uint8_t *slab_aligned_alloc(size_t arena_id, uint32_t alignment, uint32_t bytes)
{
  Constants_sc_union size = sizes[arena_id * (size_t)31U + (size_t)0U];
  uint32_t size_;
  if (size.tag == Constants_Sc)
    size_ = size.case_Sc;
  else if (size.tag == Constants_Sc_ex)
    size_ = size.case_Sc_ex;
  else
    size_ = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  bool b = 4096U % size_ == 0U;
  if (b && bytes <= size_ - 2U && alignment <= size_)
  {
    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id * (size_t)31U + (size_t)0U].lock);
    uint8_t
    *r =
      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)31U + (size_t)0U].data);
    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id * (size_t)31U + (size_t)0U].lock);
    uint8_t *ptr = r;
    uint8_t *ptr0 = ptr;
    uint32_t size1;
    if (size.tag == Constants_Sc)
      size1 = size.case_Sc;
    else if (size.tag == Constants_Sc_ex)
      size1 = size.case_Sc_ex;
    else
      size1 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
    if (!(ptr0 == NULL))
    {
      ptr0[(size_t)(size1 - 2U)] = 42U;
      ptr0[(size_t)(size1 - 1U)] = 23U;
    }
    return ptr0;
  }
  else
  {
    Constants_sc_union size1 = sizes[arena_id * (size_t)31U + (size_t)1U];
    uint32_t size_1;
    if (size1.tag == Constants_Sc)
      size_1 = size1.case_Sc;
    else if (size1.tag == Constants_Sc_ex)
      size_1 = size1.case_Sc_ex;
    else
      size_1 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
    bool b1 = 4096U % size_1 == 0U;
    if (b1 && bytes <= size_1 - 2U && alignment <= size_1)
    {
      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
        * (size_t)31U
        + (size_t)1U].lock);
      uint8_t
      *r =
        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id * (size_t)31U + (size_t)1U].data);
      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
        * (size_t)31U
        + (size_t)1U].lock);
      uint8_t *ptr = r;
      uint8_t *ptr0 = ptr;
      uint32_t size2;
      if (size1.tag == Constants_Sc)
        size2 = size1.case_Sc;
      else if (size1.tag == Constants_Sc_ex)
        size2 = size1.case_Sc_ex;
      else
        size2 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
      if (!(ptr0 == NULL))
      {
        ptr0[(size_t)(size2 - 2U)] = 42U;
        ptr0[(size_t)(size2 - 1U)] = 23U;
      }
      return ptr0;
    }
    else
    {
      Constants_sc_union size2 = sizes[arena_id * (size_t)31U + (size_t)2U];
      uint32_t size_2;
      if (size2.tag == Constants_Sc)
        size_2 = size2.case_Sc;
      else if (size2.tag == Constants_Sc_ex)
        size_2 = size2.case_Sc_ex;
      else
        size_2 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
      bool b2 = 4096U % size_2 == 0U;
      if (b2 && bytes <= size_2 - 2U && alignment <= size_2)
      {
        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
          * (size_t)31U
          + (size_t)2U].lock);
        uint8_t
        *r =
          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
            * (size_t)31U
            + (size_t)2U].data);
        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
          * (size_t)31U
          + (size_t)2U].lock);
        uint8_t *ptr = r;
        uint8_t *ptr0 = ptr;
        uint32_t size3;
        if (size2.tag == Constants_Sc)
          size3 = size2.case_Sc;
        else if (size2.tag == Constants_Sc_ex)
          size3 = size2.case_Sc_ex;
        else
          size3 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
        if (!(ptr0 == NULL))
        {
          ptr0[(size_t)(size3 - 2U)] = 42U;
          ptr0[(size_t)(size3 - 1U)] = 23U;
        }
        return ptr0;
      }
      else
      {
        Constants_sc_union size3 = sizes[arena_id * (size_t)31U + (size_t)3U];
        uint32_t size_3;
        if (size3.tag == Constants_Sc)
          size_3 = size3.case_Sc;
        else if (size3.tag == Constants_Sc_ex)
          size_3 = size3.case_Sc_ex;
        else
          size_3 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
        bool b3 = 4096U % size_3 == 0U;
        if (b3 && bytes <= size_3 - 2U && alignment <= size_3)
        {
          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
            * (size_t)31U
            + (size_t)3U].lock);
          uint8_t
          *r =
            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
              * (size_t)31U
              + (size_t)3U].data);
          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
            * (size_t)31U
            + (size_t)3U].lock);
          uint8_t *ptr = r;
          uint8_t *ptr0 = ptr;
          uint32_t size4;
          if (size3.tag == Constants_Sc)
            size4 = size3.case_Sc;
          else if (size3.tag == Constants_Sc_ex)
            size4 = size3.case_Sc_ex;
          else
            size4 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
          if (!(ptr0 == NULL))
          {
            ptr0[(size_t)(size4 - 2U)] = 42U;
            ptr0[(size_t)(size4 - 1U)] = 23U;
          }
          return ptr0;
        }
        else
        {
          Constants_sc_union size4 = sizes[arena_id * (size_t)31U + (size_t)4U];
          uint32_t size_4;
          if (size4.tag == Constants_Sc)
            size_4 = size4.case_Sc;
          else if (size4.tag == Constants_Sc_ex)
            size_4 = size4.case_Sc_ex;
          else
            size_4 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
          bool b4 = 4096U % size_4 == 0U;
          if (b4 && bytes <= size_4 - 2U && alignment <= size_4)
          {
            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
              * (size_t)31U
              + (size_t)4U].lock);
            uint8_t
            *r =
              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                * (size_t)31U
                + (size_t)4U].data);
            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
              * (size_t)31U
              + (size_t)4U].lock);
            uint8_t *ptr = r;
            uint8_t *ptr0 = ptr;
            uint32_t size5;
            if (size4.tag == Constants_Sc)
              size5 = size4.case_Sc;
            else if (size4.tag == Constants_Sc_ex)
              size5 = size4.case_Sc_ex;
            else
              size5 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
            if (!(ptr0 == NULL))
            {
              ptr0[(size_t)(size5 - 2U)] = 42U;
              ptr0[(size_t)(size5 - 1U)] = 23U;
            }
            return ptr0;
          }
          else
          {
            Constants_sc_union size5 = sizes[arena_id * (size_t)31U + (size_t)5U];
            uint32_t size_5;
            if (size5.tag == Constants_Sc)
              size_5 = size5.case_Sc;
            else if (size5.tag == Constants_Sc_ex)
              size_5 = size5.case_Sc_ex;
            else
              size_5 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
            bool b5 = 4096U % size_5 == 0U;
            if (b5 && bytes <= size_5 - 2U && alignment <= size_5)
            {
              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                * (size_t)31U
                + (size_t)5U].lock);
              uint8_t
              *r =
                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                  * (size_t)31U
                  + (size_t)5U].data);
              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                * (size_t)31U
                + (size_t)5U].lock);
              uint8_t *ptr = r;
              uint8_t *ptr0 = ptr;
              uint32_t size6;
              if (size5.tag == Constants_Sc)
                size6 = size5.case_Sc;
              else if (size5.tag == Constants_Sc_ex)
                size6 = size5.case_Sc_ex;
              else
                size6 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
              if (!(ptr0 == NULL))
              {
                ptr0[(size_t)(size6 - 2U)] = 42U;
                ptr0[(size_t)(size6 - 1U)] = 23U;
              }
              return ptr0;
            }
            else
            {
              Constants_sc_union size6 = sizes[arena_id * (size_t)31U + (size_t)6U];
              uint32_t size_6;
              if (size6.tag == Constants_Sc)
                size_6 = size6.case_Sc;
              else if (size6.tag == Constants_Sc_ex)
                size_6 = size6.case_Sc_ex;
              else
                size_6 = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
              bool b6 = 4096U % size_6 == 0U;
              if (b6 && bytes <= size_6 - 2U && alignment <= size_6)
              {
                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                  * (size_t)31U
                  + (size_t)6U].lock);
                uint8_t
                *r =
                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                    * (size_t)31U
                    + (size_t)6U].data);
                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                  * (size_t)31U
                  + (size_t)6U].lock);
                uint8_t *ptr = r;
                uint8_t *ptr0 = ptr;
                uint32_t size7;
                if (size6.tag == Constants_Sc)
                  size7 = size6.case_Sc;
                else if (size6.tag == Constants_Sc_ex)
                  size7 = size6.case_Sc_ex;
                else
                  size7 =
                    KRML_EABORT(uint32_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                if (!(ptr0 == NULL))
                {
                  ptr0[(size_t)(size7 - 2U)] = 42U;
                  ptr0[(size_t)(size7 - 1U)] = 23U;
                }
                return ptr0;
              }
              else
              {
                Constants_sc_union size7 = sizes[arena_id * (size_t)31U + (size_t)7U];
                uint32_t size_7;
                if (size7.tag == Constants_Sc)
                  size_7 = size7.case_Sc;
                else if (size7.tag == Constants_Sc_ex)
                  size_7 = size7.case_Sc_ex;
                else
                  size_7 =
                    KRML_EABORT(uint32_t,
                      "unreachable (pattern matches are exhaustive in F*)");
                bool b7 = 4096U % size_7 == 0U;
                if (b7 && bytes <= size_7 - 2U && alignment <= size_7)
                {
                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                    * (size_t)31U
                    + (size_t)7U].lock);
                  uint8_t
                  *r =
                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                      * (size_t)31U
                      + (size_t)7U].data);
                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                    * (size_t)31U
                    + (size_t)7U].lock);
                  uint8_t *ptr = r;
                  uint8_t *ptr0 = ptr;
                  uint32_t size8;
                  if (size7.tag == Constants_Sc)
                    size8 = size7.case_Sc;
                  else if (size7.tag == Constants_Sc_ex)
                    size8 = size7.case_Sc_ex;
                  else
                    size8 =
                      KRML_EABORT(uint32_t,
                        "unreachable (pattern matches are exhaustive in F*)");
                  if (!(ptr0 == NULL))
                  {
                    ptr0[(size_t)(size8 - 2U)] = 42U;
                    ptr0[(size_t)(size8 - 1U)] = 23U;
                  }
                  return ptr0;
                }
                else
                {
                  Constants_sc_union size8 = sizes[arena_id * (size_t)31U + (size_t)8U];
                  uint32_t size_8;
                  if (size8.tag == Constants_Sc)
                    size_8 = size8.case_Sc;
                  else if (size8.tag == Constants_Sc_ex)
                    size_8 = size8.case_Sc_ex;
                  else
                    size_8 =
                      KRML_EABORT(uint32_t,
                        "unreachable (pattern matches are exhaustive in F*)");
                  bool b8 = 4096U % size_8 == 0U;
                  if (b8 && bytes <= size_8 - 2U && alignment <= size_8)
                  {
                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                      * (size_t)31U
                      + (size_t)8U].lock);
                    uint8_t
                    *r =
                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                        * (size_t)31U
                        + (size_t)8U].data);
                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                      * (size_t)31U
                      + (size_t)8U].lock);
                    uint8_t *ptr = r;
                    uint8_t *ptr0 = ptr;
                    uint32_t size9;
                    if (size8.tag == Constants_Sc)
                      size9 = size8.case_Sc;
                    else if (size8.tag == Constants_Sc_ex)
                      size9 = size8.case_Sc_ex;
                    else
                      size9 =
                        KRML_EABORT(uint32_t,
                          "unreachable (pattern matches are exhaustive in F*)");
                    if (!(ptr0 == NULL))
                    {
                      ptr0[(size_t)(size9 - 2U)] = 42U;
                      ptr0[(size_t)(size9 - 1U)] = 23U;
                    }
                    return ptr0;
                  }
                  else
                  {
                    Constants_sc_union size9 = sizes[arena_id * (size_t)31U + (size_t)9U];
                    uint32_t size_9;
                    if (size9.tag == Constants_Sc)
                      size_9 = size9.case_Sc;
                    else if (size9.tag == Constants_Sc_ex)
                      size_9 = size9.case_Sc_ex;
                    else
                      size_9 =
                        KRML_EABORT(uint32_t,
                          "unreachable (pattern matches are exhaustive in F*)");
                    bool b9 = 4096U % size_9 == 0U;
                    if (b9 && bytes <= size_9 - 2U && alignment <= size_9)
                    {
                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                        * (size_t)31U
                        + (size_t)9U].lock);
                      uint8_t
                      *r =
                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                          * (size_t)31U
                          + (size_t)9U].data);
                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                        * (size_t)31U
                        + (size_t)9U].lock);
                      uint8_t *ptr = r;
                      uint8_t *ptr0 = ptr;
                      uint32_t size10;
                      if (size9.tag == Constants_Sc)
                        size10 = size9.case_Sc;
                      else if (size9.tag == Constants_Sc_ex)
                        size10 = size9.case_Sc_ex;
                      else
                        size10 =
                          KRML_EABORT(uint32_t,
                            "unreachable (pattern matches are exhaustive in F*)");
                      if (!(ptr0 == NULL))
                      {
                        ptr0[(size_t)(size10 - 2U)] = 42U;
                        ptr0[(size_t)(size10 - 1U)] = 23U;
                      }
                      return ptr0;
                    }
                    else
                    {
                      Constants_sc_union size10 = sizes[arena_id * (size_t)31U + (size_t)10U];
                      uint32_t size_10;
                      if (size10.tag == Constants_Sc)
                        size_10 = size10.case_Sc;
                      else if (size10.tag == Constants_Sc_ex)
                        size_10 = size10.case_Sc_ex;
                      else
                        size_10 =
                          KRML_EABORT(uint32_t,
                            "unreachable (pattern matches are exhaustive in F*)");
                      bool b10 = 4096U % size_10 == 0U;
                      if (b10 && bytes <= size_10 - 2U && alignment <= size_10)
                      {
                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                          * (size_t)31U
                          + (size_t)10U].lock);
                        uint8_t
                        *r =
                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                            * (size_t)31U
                            + (size_t)10U].data);
                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                          * (size_t)31U
                          + (size_t)10U].lock);
                        uint8_t *ptr = r;
                        uint8_t *ptr0 = ptr;
                        uint32_t size11;
                        if (size10.tag == Constants_Sc)
                          size11 = size10.case_Sc;
                        else if (size10.tag == Constants_Sc_ex)
                          size11 = size10.case_Sc_ex;
                        else
                          size11 =
                            KRML_EABORT(uint32_t,
                              "unreachable (pattern matches are exhaustive in F*)");
                        if (!(ptr0 == NULL))
                        {
                          ptr0[(size_t)(size11 - 2U)] = 42U;
                          ptr0[(size_t)(size11 - 1U)] = 23U;
                        }
                        return ptr0;
                      }
                      else
                      {
                        Constants_sc_union size11 = sizes[arena_id * (size_t)31U + (size_t)11U];
                        uint32_t size_11;
                        if (size11.tag == Constants_Sc)
                          size_11 = size11.case_Sc;
                        else if (size11.tag == Constants_Sc_ex)
                          size_11 = size11.case_Sc_ex;
                        else
                          size_11 =
                            KRML_EABORT(uint32_t,
                              "unreachable (pattern matches are exhaustive in F*)");
                        bool b11 = 4096U % size_11 == 0U;
                        if (b11 && bytes <= size_11 - 2U && alignment <= size_11)
                        {
                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                            * (size_t)31U
                            + (size_t)11U].lock);
                          uint8_t
                          *r =
                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                              * (size_t)31U
                              + (size_t)11U].data);
                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                            * (size_t)31U
                            + (size_t)11U].lock);
                          uint8_t *ptr = r;
                          uint8_t *ptr0 = ptr;
                          uint32_t size12;
                          if (size11.tag == Constants_Sc)
                            size12 = size11.case_Sc;
                          else if (size11.tag == Constants_Sc_ex)
                            size12 = size11.case_Sc_ex;
                          else
                            size12 =
                              KRML_EABORT(uint32_t,
                                "unreachable (pattern matches are exhaustive in F*)");
                          if (!(ptr0 == NULL))
                          {
                            ptr0[(size_t)(size12 - 2U)] = 42U;
                            ptr0[(size_t)(size12 - 1U)] = 23U;
                          }
                          return ptr0;
                        }
                        else
                        {
                          Constants_sc_union size12 = sizes[arena_id * (size_t)31U + (size_t)12U];
                          uint32_t size_12;
                          if (size12.tag == Constants_Sc)
                            size_12 = size12.case_Sc;
                          else if (size12.tag == Constants_Sc_ex)
                            size_12 = size12.case_Sc_ex;
                          else
                            size_12 =
                              KRML_EABORT(uint32_t,
                                "unreachable (pattern matches are exhaustive in F*)");
                          bool b12 = 4096U % size_12 == 0U;
                          if (b12 && bytes <= size_12 - 2U && alignment <= size_12)
                          {
                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                              * (size_t)31U
                              + (size_t)12U].lock);
                            uint8_t
                            *r =
                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                * (size_t)31U
                                + (size_t)12U].data);
                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                              * (size_t)31U
                              + (size_t)12U].lock);
                            uint8_t *ptr = r;
                            uint8_t *ptr0 = ptr;
                            uint32_t size13;
                            if (size12.tag == Constants_Sc)
                              size13 = size12.case_Sc;
                            else if (size12.tag == Constants_Sc_ex)
                              size13 = size12.case_Sc_ex;
                            else
                              size13 =
                                KRML_EABORT(uint32_t,
                                  "unreachable (pattern matches are exhaustive in F*)");
                            if (!(ptr0 == NULL))
                            {
                              ptr0[(size_t)(size13 - 2U)] = 42U;
                              ptr0[(size_t)(size13 - 1U)] = 23U;
                            }
                            return ptr0;
                          }
                          else
                          {
                            Constants_sc_union size13 = sizes[arena_id * (size_t)31U + (size_t)13U];
                            uint32_t size_13;
                            if (size13.tag == Constants_Sc)
                              size_13 = size13.case_Sc;
                            else if (size13.tag == Constants_Sc_ex)
                              size_13 = size13.case_Sc_ex;
                            else
                              size_13 =
                                KRML_EABORT(uint32_t,
                                  "unreachable (pattern matches are exhaustive in F*)");
                            bool b13 = 4096U % size_13 == 0U;
                            if (b13 && bytes <= size_13 - 2U && alignment <= size_13)
                            {
                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                * (size_t)31U
                                + (size_t)13U].lock);
                              uint8_t
                              *r =
                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                  * (size_t)31U
                                  + (size_t)13U].data);
                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                * (size_t)31U
                                + (size_t)13U].lock);
                              uint8_t *ptr = r;
                              uint8_t *ptr0 = ptr;
                              uint32_t size14;
                              if (size13.tag == Constants_Sc)
                                size14 = size13.case_Sc;
                              else if (size13.tag == Constants_Sc_ex)
                                size14 = size13.case_Sc_ex;
                              else
                                size14 =
                                  KRML_EABORT(uint32_t,
                                    "unreachable (pattern matches are exhaustive in F*)");
                              if (!(ptr0 == NULL))
                              {
                                ptr0[(size_t)(size14 - 2U)] = 42U;
                                ptr0[(size_t)(size14 - 1U)] = 23U;
                              }
                              return ptr0;
                            }
                            else
                            {
                              Constants_sc_union
                              size14 = sizes[arena_id * (size_t)31U + (size_t)14U];
                              uint32_t size_14;
                              if (size14.tag == Constants_Sc)
                                size_14 = size14.case_Sc;
                              else if (size14.tag == Constants_Sc_ex)
                                size_14 = size14.case_Sc_ex;
                              else
                                size_14 =
                                  KRML_EABORT(uint32_t,
                                    "unreachable (pattern matches are exhaustive in F*)");
                              bool b14 = 4096U % size_14 == 0U;
                              if (b14 && bytes <= size_14 - 2U && alignment <= size_14)
                              {
                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                  * (size_t)31U
                                  + (size_t)14U].lock);
                                uint8_t
                                *r =
                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                    * (size_t)31U
                                    + (size_t)14U].data);
                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                  * (size_t)31U
                                  + (size_t)14U].lock);
                                uint8_t *ptr = r;
                                uint8_t *ptr0 = ptr;
                                uint32_t size15;
                                if (size14.tag == Constants_Sc)
                                  size15 = size14.case_Sc;
                                else if (size14.tag == Constants_Sc_ex)
                                  size15 = size14.case_Sc_ex;
                                else
                                  size15 =
                                    KRML_EABORT(uint32_t,
                                      "unreachable (pattern matches are exhaustive in F*)");
                                if (!(ptr0 == NULL))
                                {
                                  ptr0[(size_t)(size15 - 2U)] = 42U;
                                  ptr0[(size_t)(size15 - 1U)] = 23U;
                                }
                                return ptr0;
                              }
                              else
                              {
                                Constants_sc_union
                                size15 = sizes[arena_id * (size_t)31U + (size_t)15U];
                                uint32_t size_15;
                                if (size15.tag == Constants_Sc)
                                  size_15 = size15.case_Sc;
                                else if (size15.tag == Constants_Sc_ex)
                                  size_15 = size15.case_Sc_ex;
                                else
                                  size_15 =
                                    KRML_EABORT(uint32_t,
                                      "unreachable (pattern matches are exhaustive in F*)");
                                bool b15 = 4096U % size_15 == 0U;
                                if (b15 && bytes <= size_15 - 2U && alignment <= size_15)
                                {
                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                    * (size_t)31U
                                    + (size_t)15U].lock);
                                  uint8_t
                                  *r =
                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                      * (size_t)31U
                                      + (size_t)15U].data);
                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                    * (size_t)31U
                                    + (size_t)15U].lock);
                                  uint8_t *ptr = r;
                                  uint8_t *ptr0 = ptr;
                                  uint32_t size16;
                                  if (size15.tag == Constants_Sc)
                                    size16 = size15.case_Sc;
                                  else if (size15.tag == Constants_Sc_ex)
                                    size16 = size15.case_Sc_ex;
                                  else
                                    size16 =
                                      KRML_EABORT(uint32_t,
                                        "unreachable (pattern matches are exhaustive in F*)");
                                  if (!(ptr0 == NULL))
                                  {
                                    ptr0[(size_t)(size16 - 2U)] = 42U;
                                    ptr0[(size_t)(size16 - 1U)] = 23U;
                                  }
                                  return ptr0;
                                }
                                else
                                {
                                  Constants_sc_union
                                  size16 = sizes[arena_id * (size_t)31U + (size_t)16U];
                                  uint32_t size_16;
                                  if (size16.tag == Constants_Sc)
                                    size_16 = size16.case_Sc;
                                  else if (size16.tag == Constants_Sc_ex)
                                    size_16 = size16.case_Sc_ex;
                                  else
                                    size_16 =
                                      KRML_EABORT(uint32_t,
                                        "unreachable (pattern matches are exhaustive in F*)");
                                  bool b16 = 4096U % size_16 == 0U;
                                  if (b16 && bytes <= size_16 - 2U && alignment <= size_16)
                                  {
                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                      * (size_t)31U
                                      + (size_t)16U].lock);
                                    uint8_t
                                    *r =
                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)31U
                                        + (size_t)16U].data);
                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                      * (size_t)31U
                                      + (size_t)16U].lock);
                                    uint8_t *ptr = r;
                                    uint8_t *ptr0 = ptr;
                                    uint32_t size17;
                                    if (size16.tag == Constants_Sc)
                                      size17 = size16.case_Sc;
                                    else if (size16.tag == Constants_Sc_ex)
                                      size17 = size16.case_Sc_ex;
                                    else
                                      size17 =
                                        KRML_EABORT(uint32_t,
                                          "unreachable (pattern matches are exhaustive in F*)");
                                    if (!(ptr0 == NULL))
                                    {
                                      ptr0[(size_t)(size17 - 2U)] = 42U;
                                      ptr0[(size_t)(size17 - 1U)] = 23U;
                                    }
                                    return ptr0;
                                  }
                                  else
                                  {
                                    Constants_sc_union
                                    size17 = sizes[arena_id * (size_t)31U + (size_t)17U];
                                    uint32_t size_17;
                                    if (size17.tag == Constants_Sc)
                                      size_17 = size17.case_Sc;
                                    else if (size17.tag == Constants_Sc_ex)
                                      size_17 = size17.case_Sc_ex;
                                    else
                                      size_17 =
                                        KRML_EABORT(uint32_t,
                                          "unreachable (pattern matches are exhaustive in F*)");
                                    bool b17 = 4096U % size_17 == 0U;
                                    if (b17 && bytes <= size_17 - 2U && alignment <= size_17)
                                    {
                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)31U
                                        + (size_t)17U].lock);
                                      uint8_t
                                      *r =
                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)31U
                                          + (size_t)17U].data);
                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                        * (size_t)31U
                                        + (size_t)17U].lock);
                                      uint8_t *ptr = r;
                                      uint8_t *ptr0 = ptr;
                                      uint32_t size18;
                                      if (size17.tag == Constants_Sc)
                                        size18 = size17.case_Sc;
                                      else if (size17.tag == Constants_Sc_ex)
                                        size18 = size17.case_Sc_ex;
                                      else
                                        size18 =
                                          KRML_EABORT(uint32_t,
                                            "unreachable (pattern matches are exhaustive in F*)");
                                      if (!(ptr0 == NULL))
                                      {
                                        ptr0[(size_t)(size18 - 2U)] = 42U;
                                        ptr0[(size_t)(size18 - 1U)] = 23U;
                                      }
                                      return ptr0;
                                    }
                                    else
                                    {
                                      Constants_sc_union
                                      size18 = sizes[arena_id * (size_t)31U + (size_t)18U];
                                      uint32_t size_18;
                                      if (size18.tag == Constants_Sc)
                                        size_18 = size18.case_Sc;
                                      else if (size18.tag == Constants_Sc_ex)
                                        size_18 = size18.case_Sc_ex;
                                      else
                                        size_18 =
                                          KRML_EABORT(uint32_t,
                                            "unreachable (pattern matches are exhaustive in F*)");
                                      bool b18 = 4096U % size_18 == 0U;
                                      if (b18 && bytes <= size_18 - 2U && alignment <= size_18)
                                      {
                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)31U
                                          + (size_t)18U].lock);
                                        uint8_t
                                        *r =
                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)31U
                                            + (size_t)18U].data);
                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                          * (size_t)31U
                                          + (size_t)18U].lock);
                                        uint8_t *ptr = r;
                                        uint8_t *ptr0 = ptr;
                                        uint32_t size19;
                                        if (size18.tag == Constants_Sc)
                                          size19 = size18.case_Sc;
                                        else if (size18.tag == Constants_Sc_ex)
                                          size19 = size18.case_Sc_ex;
                                        else
                                          size19 =
                                            KRML_EABORT(uint32_t,
                                              "unreachable (pattern matches are exhaustive in F*)");
                                        if (!(ptr0 == NULL))
                                        {
                                          ptr0[(size_t)(size19 - 2U)] = 42U;
                                          ptr0[(size_t)(size19 - 1U)] = 23U;
                                        }
                                        return ptr0;
                                      }
                                      else
                                      {
                                        Constants_sc_union
                                        size19 = sizes[arena_id * (size_t)31U + (size_t)19U];
                                        uint32_t size_19;
                                        if (size19.tag == Constants_Sc)
                                          size_19 = size19.case_Sc;
                                        else if (size19.tag == Constants_Sc_ex)
                                          size_19 = size19.case_Sc_ex;
                                        else
                                          size_19 =
                                            KRML_EABORT(uint32_t,
                                              "unreachable (pattern matches are exhaustive in F*)");
                                        bool b19 = 4096U % size_19 == 0U;
                                        if (b19 && bytes <= size_19 - 2U && alignment <= size_19)
                                        {
                                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)31U
                                            + (size_t)19U].lock);
                                          uint8_t
                                          *r =
                                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)31U
                                              + (size_t)19U].data);
                                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                            * (size_t)31U
                                            + (size_t)19U].lock);
                                          uint8_t *ptr = r;
                                          uint8_t *ptr0 = ptr;
                                          uint32_t size20;
                                          if (size19.tag == Constants_Sc)
                                            size20 = size19.case_Sc;
                                          else if (size19.tag == Constants_Sc_ex)
                                            size20 = size19.case_Sc_ex;
                                          else
                                            size20 =
                                              KRML_EABORT(uint32_t,
                                                "unreachable (pattern matches are exhaustive in F*)");
                                          if (!(ptr0 == NULL))
                                          {
                                            ptr0[(size_t)(size20 - 2U)] = 42U;
                                            ptr0[(size_t)(size20 - 1U)] = 23U;
                                          }
                                          return ptr0;
                                        }
                                        else
                                        {
                                          Constants_sc_union
                                          size20 = sizes[arena_id * (size_t)31U + (size_t)20U];
                                          uint32_t size_20;
                                          if (size20.tag == Constants_Sc)
                                            size_20 = size20.case_Sc;
                                          else if (size20.tag == Constants_Sc_ex)
                                            size_20 = size20.case_Sc_ex;
                                          else
                                            size_20 =
                                              KRML_EABORT(uint32_t,
                                                "unreachable (pattern matches are exhaustive in F*)");
                                          bool b20 = 4096U % size_20 == 0U;
                                          if (b20 && bytes <= size_20 - 2U && alignment <= size_20)
                                          {
                                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)31U
                                              + (size_t)20U].lock);
                                            uint8_t
                                            *r =
                                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)31U
                                                + (size_t)20U].data);
                                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                              * (size_t)31U
                                              + (size_t)20U].lock);
                                            uint8_t *ptr = r;
                                            uint8_t *ptr0 = ptr;
                                            uint32_t size21;
                                            if (size20.tag == Constants_Sc)
                                              size21 = size20.case_Sc;
                                            else if (size20.tag == Constants_Sc_ex)
                                              size21 = size20.case_Sc_ex;
                                            else
                                              size21 =
                                                KRML_EABORT(uint32_t,
                                                  "unreachable (pattern matches are exhaustive in F*)");
                                            if (!(ptr0 == NULL))
                                            {
                                              ptr0[(size_t)(size21 - 2U)] = 42U;
                                              ptr0[(size_t)(size21 - 1U)] = 23U;
                                            }
                                            return ptr0;
                                          }
                                          else
                                          {
                                            Constants_sc_union
                                            size21 = sizes[arena_id * (size_t)31U + (size_t)21U];
                                            uint32_t size_21;
                                            if (size21.tag == Constants_Sc)
                                              size_21 = size21.case_Sc;
                                            else if (size21.tag == Constants_Sc_ex)
                                              size_21 = size21.case_Sc_ex;
                                            else
                                              size_21 =
                                                KRML_EABORT(uint32_t,
                                                  "unreachable (pattern matches are exhaustive in F*)");
                                            bool b21 = 4096U % size_21 == 0U;
                                            if
                                            (b21 && bytes <= size_21 - 2U && alignment <= size_21)
                                            {
                                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)31U
                                                + (size_t)21U].lock);
                                              uint8_t
                                              *r =
                                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)31U
                                                  + (size_t)21U].data);
                                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                * (size_t)31U
                                                + (size_t)21U].lock);
                                              uint8_t *ptr = r;
                                              uint8_t *ptr0 = ptr;
                                              uint32_t size22;
                                              if (size21.tag == Constants_Sc)
                                                size22 = size21.case_Sc;
                                              else if (size21.tag == Constants_Sc_ex)
                                                size22 = size21.case_Sc_ex;
                                              else
                                                size22 =
                                                  KRML_EABORT(uint32_t,
                                                    "unreachable (pattern matches are exhaustive in F*)");
                                              if (!(ptr0 == NULL))
                                              {
                                                ptr0[(size_t)(size22 - 2U)] = 42U;
                                                ptr0[(size_t)(size22 - 1U)] = 23U;
                                              }
                                              return ptr0;
                                            }
                                            else
                                            {
                                              Constants_sc_union
                                              size22 = sizes[arena_id * (size_t)31U + (size_t)22U];
                                              uint32_t size_22;
                                              if (size22.tag == Constants_Sc)
                                                size_22 = size22.case_Sc;
                                              else if (size22.tag == Constants_Sc_ex)
                                                size_22 = size22.case_Sc_ex;
                                              else
                                                size_22 =
                                                  KRML_EABORT(uint32_t,
                                                    "unreachable (pattern matches are exhaustive in F*)");
                                              bool b22 = 4096U % size_22 == 0U;
                                              if
                                              (b22 && bytes <= size_22 - 2U && alignment <= size_22)
                                              {
                                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)31U
                                                  + (size_t)22U].lock);
                                                uint8_t
                                                *r =
                                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)31U
                                                    + (size_t)22U].data);
                                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                  * (size_t)31U
                                                  + (size_t)22U].lock);
                                                uint8_t *ptr = r;
                                                uint8_t *ptr0 = ptr;
                                                uint32_t size23;
                                                if (size22.tag == Constants_Sc)
                                                  size23 = size22.case_Sc;
                                                else if (size22.tag == Constants_Sc_ex)
                                                  size23 = size22.case_Sc_ex;
                                                else
                                                  size23 =
                                                    KRML_EABORT(uint32_t,
                                                      "unreachable (pattern matches are exhaustive in F*)");
                                                if (!(ptr0 == NULL))
                                                {
                                                  ptr0[(size_t)(size23 - 2U)] = 42U;
                                                  ptr0[(size_t)(size23 - 1U)] = 23U;
                                                }
                                                return ptr0;
                                              }
                                              else
                                              {
                                                Constants_sc_union
                                                size23 = sizes[arena_id * (size_t)31U + (size_t)23U];
                                                uint32_t size_23;
                                                if (size23.tag == Constants_Sc)
                                                  size_23 = size23.case_Sc;
                                                else if (size23.tag == Constants_Sc_ex)
                                                  size_23 = size23.case_Sc_ex;
                                                else
                                                  size_23 =
                                                    KRML_EABORT(uint32_t,
                                                      "unreachable (pattern matches are exhaustive in F*)");
                                                bool b23 = 4096U % size_23 == 0U;
                                                if
                                                (
                                                  b23
                                                  && bytes <= size_23 - 2U
                                                  && alignment <= size_23
                                                )
                                                {
                                                  Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)31U
                                                    + (size_t)23U].lock);
                                                  uint8_t
                                                  *r =
                                                    allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)31U
                                                      + (size_t)23U].data);
                                                  Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                    * (size_t)31U
                                                    + (size_t)23U].lock);
                                                  uint8_t *ptr = r;
                                                  uint8_t *ptr0 = ptr;
                                                  uint32_t size24;
                                                  if (size23.tag == Constants_Sc)
                                                    size24 = size23.case_Sc;
                                                  else if (size23.tag == Constants_Sc_ex)
                                                    size24 = size23.case_Sc_ex;
                                                  else
                                                    size24 =
                                                      KRML_EABORT(uint32_t,
                                                        "unreachable (pattern matches are exhaustive in F*)");
                                                  if (!(ptr0 == NULL))
                                                  {
                                                    ptr0[(size_t)(size24 - 2U)] = 42U;
                                                    ptr0[(size_t)(size24 - 1U)] = 23U;
                                                  }
                                                  return ptr0;
                                                }
                                                else
                                                {
                                                  Constants_sc_union
                                                  size24 =
                                                    sizes[arena_id
                                                    * (size_t)31U
                                                    + (size_t)24U];
                                                  uint32_t size_24;
                                                  if (size24.tag == Constants_Sc)
                                                    size_24 = size24.case_Sc;
                                                  else if (size24.tag == Constants_Sc_ex)
                                                    size_24 = size24.case_Sc_ex;
                                                  else
                                                    size_24 =
                                                      KRML_EABORT(uint32_t,
                                                        "unreachable (pattern matches are exhaustive in F*)");
                                                  bool b24 = 4096U % size_24 == 0U;
                                                  if
                                                  (
                                                    b24
                                                    && bytes <= size_24 - 2U
                                                    && alignment <= size_24
                                                  )
                                                  {
                                                    Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)31U
                                                      + (size_t)24U].lock);
                                                    uint8_t
                                                    *r =
                                                      allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)31U
                                                        + (size_t)24U].data);
                                                    Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                      * (size_t)31U
                                                      + (size_t)24U].lock);
                                                    uint8_t *ptr = r;
                                                    uint8_t *ptr0 = ptr;
                                                    uint32_t size25;
                                                    if (size24.tag == Constants_Sc)
                                                      size25 = size24.case_Sc;
                                                    else if (size24.tag == Constants_Sc_ex)
                                                      size25 = size24.case_Sc_ex;
                                                    else
                                                      size25 =
                                                        KRML_EABORT(uint32_t,
                                                          "unreachable (pattern matches are exhaustive in F*)");
                                                    if (!(ptr0 == NULL))
                                                    {
                                                      ptr0[(size_t)(size25 - 2U)] = 42U;
                                                      ptr0[(size_t)(size25 - 1U)] = 23U;
                                                    }
                                                    return ptr0;
                                                  }
                                                  else
                                                  {
                                                    Constants_sc_union
                                                    size25 =
                                                      sizes[arena_id
                                                      * (size_t)31U
                                                      + (size_t)25U];
                                                    uint32_t size_25;
                                                    if (size25.tag == Constants_Sc)
                                                      size_25 = size25.case_Sc;
                                                    else if (size25.tag == Constants_Sc_ex)
                                                      size_25 = size25.case_Sc_ex;
                                                    else
                                                      size_25 =
                                                        KRML_EABORT(uint32_t,
                                                          "unreachable (pattern matches are exhaustive in F*)");
                                                    bool b25 = 4096U % size_25 == 0U;
                                                    if
                                                    (
                                                      b25
                                                      && bytes <= size_25 - 2U
                                                      && alignment <= size_25
                                                    )
                                                    {
                                                      Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)31U
                                                        + (size_t)25U].lock);
                                                      uint8_t
                                                      *r =
                                                        allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)31U
                                                          + (size_t)25U].data);
                                                      Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                        * (size_t)31U
                                                        + (size_t)25U].lock);
                                                      uint8_t *ptr = r;
                                                      uint8_t *ptr0 = ptr;
                                                      uint32_t size26;
                                                      if (size25.tag == Constants_Sc)
                                                        size26 = size25.case_Sc;
                                                      else if (size25.tag == Constants_Sc_ex)
                                                        size26 = size25.case_Sc_ex;
                                                      else
                                                        size26 =
                                                          KRML_EABORT(uint32_t,
                                                            "unreachable (pattern matches are exhaustive in F*)");
                                                      if (!(ptr0 == NULL))
                                                      {
                                                        ptr0[(size_t)(size26 - 2U)] = 42U;
                                                        ptr0[(size_t)(size26 - 1U)] = 23U;
                                                      }
                                                      return ptr0;
                                                    }
                                                    else
                                                    {
                                                      Constants_sc_union
                                                      size26 =
                                                        sizes[arena_id
                                                        * (size_t)31U
                                                        + (size_t)26U];
                                                      uint32_t size_26;
                                                      if (size26.tag == Constants_Sc)
                                                        size_26 = size26.case_Sc;
                                                      else if (size26.tag == Constants_Sc_ex)
                                                        size_26 = size26.case_Sc_ex;
                                                      else
                                                        size_26 =
                                                          KRML_EABORT(uint32_t,
                                                            "unreachable (pattern matches are exhaustive in F*)");
                                                      bool b26 = 4096U % size_26 == 0U;
                                                      if
                                                      (
                                                        b26
                                                        && bytes <= size_26 - 2U
                                                        && alignment <= size_26
                                                      )
                                                      {
                                                        Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)31U
                                                          + (size_t)26U].lock);
                                                        uint8_t
                                                        *r =
                                                          allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                            * (size_t)31U
                                                            + (size_t)26U].data);
                                                        Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                          * (size_t)31U
                                                          + (size_t)26U].lock);
                                                        uint8_t *ptr = r;
                                                        uint8_t *ptr0 = ptr;
                                                        uint32_t size27;
                                                        if (size26.tag == Constants_Sc)
                                                          size27 = size26.case_Sc;
                                                        else if (size26.tag == Constants_Sc_ex)
                                                          size27 = size26.case_Sc_ex;
                                                        else
                                                          size27 =
                                                            KRML_EABORT(uint32_t,
                                                              "unreachable (pattern matches are exhaustive in F*)");
                                                        if (!(ptr0 == NULL))
                                                        {
                                                          ptr0[(size_t)(size27 - 2U)] = 42U;
                                                          ptr0[(size_t)(size27 - 1U)] = 23U;
                                                        }
                                                        return ptr0;
                                                      }
                                                      else
                                                      {
                                                        Constants_sc_union
                                                        size27 =
                                                          sizes[arena_id
                                                          * (size_t)31U
                                                          + (size_t)27U];
                                                        uint32_t size_27;
                                                        if (size27.tag == Constants_Sc)
                                                          size_27 = size27.case_Sc;
                                                        else if (size27.tag == Constants_Sc_ex)
                                                          size_27 = size27.case_Sc_ex;
                                                        else
                                                          size_27 =
                                                            KRML_EABORT(uint32_t,
                                                              "unreachable (pattern matches are exhaustive in F*)");
                                                        bool b27 = 4096U % size_27 == 0U;
                                                        if
                                                        (
                                                          b27
                                                          && bytes <= size_27 - 2U
                                                          && alignment <= size_27
                                                        )
                                                        {
                                                          Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                            * (size_t)31U
                                                            + (size_t)27U].lock);
                                                          uint8_t
                                                          *r =
                                                            allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                              * (size_t)31U
                                                              + (size_t)27U].data);
                                                          Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                            * (size_t)31U
                                                            + (size_t)27U].lock);
                                                          uint8_t *ptr = r;
                                                          uint8_t *ptr0 = ptr;
                                                          uint32_t size28;
                                                          if (size27.tag == Constants_Sc)
                                                            size28 = size27.case_Sc;
                                                          else if (size27.tag == Constants_Sc_ex)
                                                            size28 = size27.case_Sc_ex;
                                                          else
                                                            size28 =
                                                              KRML_EABORT(uint32_t,
                                                                "unreachable (pattern matches are exhaustive in F*)");
                                                          if (!(ptr0 == NULL))
                                                          {
                                                            ptr0[(size_t)(size28 - 2U)] = 42U;
                                                            ptr0[(size_t)(size28 - 1U)] = 23U;
                                                          }
                                                          return ptr0;
                                                        }
                                                        else
                                                        {
                                                          Constants_sc_union
                                                          size28 =
                                                            sizes[arena_id
                                                            * (size_t)31U
                                                            + (size_t)28U];
                                                          uint32_t size_28;
                                                          if (size28.tag == Constants_Sc)
                                                            size_28 = size28.case_Sc;
                                                          else if (size28.tag == Constants_Sc_ex)
                                                            size_28 = size28.case_Sc_ex;
                                                          else
                                                            size_28 =
                                                              KRML_EABORT(uint32_t,
                                                                "unreachable (pattern matches are exhaustive in F*)");
                                                          bool b28 = 4096U % size_28 == 0U;
                                                          if
                                                          (
                                                            b28
                                                            && bytes <= size_28 - 2U
                                                            && alignment <= size_28
                                                          )
                                                          {
                                                            Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                              * (size_t)31U
                                                              + (size_t)28U].lock);
                                                            uint8_t
                                                            *r =
                                                              allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                * (size_t)31U
                                                                + (size_t)28U].data);
                                                            Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                              * (size_t)31U
                                                              + (size_t)28U].lock);
                                                            uint8_t *ptr = r;
                                                            uint8_t *ptr0 = ptr;
                                                            uint32_t size29;
                                                            if (size28.tag == Constants_Sc)
                                                              size29 = size28.case_Sc;
                                                            else if (size28.tag == Constants_Sc_ex)
                                                              size29 = size28.case_Sc_ex;
                                                            else
                                                              size29 =
                                                                KRML_EABORT(uint32_t,
                                                                  "unreachable (pattern matches are exhaustive in F*)");
                                                            if (!(ptr0 == NULL))
                                                            {
                                                              ptr0[(size_t)(size29 - 2U)] = 42U;
                                                              ptr0[(size_t)(size29 - 1U)] = 23U;
                                                            }
                                                            return ptr0;
                                                          }
                                                          else
                                                          {
                                                            Constants_sc_union
                                                            size29 =
                                                              sizes[arena_id
                                                              * (size_t)31U
                                                              + (size_t)29U];
                                                            uint32_t size_29;
                                                            if (size29.tag == Constants_Sc)
                                                              size_29 = size29.case_Sc;
                                                            else if (size29.tag == Constants_Sc_ex)
                                                              size_29 = size29.case_Sc_ex;
                                                            else
                                                              size_29 =
                                                                KRML_EABORT(uint32_t,
                                                                  "unreachable (pattern matches are exhaustive in F*)");
                                                            bool b29 = 4096U % size_29 == 0U;
                                                            if
                                                            (
                                                              b29
                                                              && bytes <= size_29 - 2U
                                                              && alignment <= size_29
                                                            )
                                                            {
                                                              Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                * (size_t)31U
                                                                + (size_t)29U].lock);
                                                              uint8_t
                                                              *r =
                                                                allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                  * (size_t)31U
                                                                  + (size_t)29U].data);
                                                              Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                * (size_t)31U
                                                                + (size_t)29U].lock);
                                                              uint8_t *ptr = r;
                                                              uint8_t *ptr0 = ptr;
                                                              uint32_t size30;
                                                              if (size29.tag == Constants_Sc)
                                                                size30 = size29.case_Sc;
                                                              else if
                                                              (size29.tag == Constants_Sc_ex)
                                                                size30 = size29.case_Sc_ex;
                                                              else
                                                                size30 =
                                                                  KRML_EABORT(uint32_t,
                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                              if (!(ptr0 == NULL))
                                                              {
                                                                ptr0[(size_t)(size30 - 2U)] = 42U;
                                                                ptr0[(size_t)(size30 - 1U)] = 23U;
                                                              }
                                                              return ptr0;
                                                            }
                                                            else
                                                            {
                                                              Constants_sc_union
                                                              size30 =
                                                                sizes[arena_id
                                                                * (size_t)31U
                                                                + (size_t)30U];
                                                              uint32_t size_30;
                                                              if (size30.tag == Constants_Sc)
                                                                size_30 = size30.case_Sc;
                                                              else if
                                                              (size30.tag == Constants_Sc_ex)
                                                                size_30 = size30.case_Sc_ex;
                                                              else
                                                                size_30 =
                                                                  KRML_EABORT(uint32_t,
                                                                    "unreachable (pattern matches are exhaustive in F*)");
                                                              bool b30 = 4096U % size_30 == 0U;
                                                              if
                                                              (
                                                                b30
                                                                && bytes <= size_30 - 2U
                                                                && alignment <= size_30
                                                              )
                                                              {
                                                                Steel_SpinLock_acquire(&Main_Meta_sc_all.size_classes[arena_id
                                                                  * (size_t)31U
                                                                  + (size_t)30U].lock);
                                                                uint8_t
                                                                *r =
                                                                  allocate_size_class(Main_Meta_sc_all.size_classes[arena_id
                                                                    * (size_t)31U
                                                                    + (size_t)30U].data);
                                                                Steel_SpinLock_release(&Main_Meta_sc_all.size_classes[arena_id
                                                                  * (size_t)31U
                                                                  + (size_t)30U].lock);
                                                                uint8_t *ptr = r;
                                                                uint8_t *ptr0 = ptr;
                                                                uint32_t size31;
                                                                if (size30.tag == Constants_Sc)
                                                                  size31 = size30.case_Sc;
                                                                else if
                                                                (size30.tag == Constants_Sc_ex)
                                                                  size31 = size30.case_Sc_ex;
                                                                else
                                                                  size31 =
                                                                    KRML_EABORT(uint32_t,
                                                                      "unreachable (pattern matches are exhaustive in F*)");
                                                                if (!(ptr0 == NULL))
                                                                {
                                                                  ptr0[(size_t)(size31 - 2U)] = 42U;
                                                                  ptr0[(size_t)(size31 - 1U)] = 23U;
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
  size_t index = diff_sz / Main_sc_slab_region_size;
  Constants_sc_union scrut = sizes[index];
  uint32_t size;
  if (scrut.tag == Constants_Sc)
    size = scrut.case_Sc;
  else if (scrut.tag == Constants_Sc_ex)
    size = scrut.case_Sc_ex;
  else
    size = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
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
  size_t index = diff_sz / Main_sc_slab_region_size;
  Constants_sc_union scrut = sizes[index];
  uint32_t size;
  if (scrut.tag == Constants_Sc)
    size = scrut.case_Sc;
  else if (scrut.tag == Constants_Sc_ex)
    size = scrut.case_Sc_ex;
  else
    size = KRML_EABORT(uint32_t, "unreachable (pattern matches are exhaustive in F*)");
  size_t rem_slab = diff_sz % Main_sc_slab_region_size;
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

size_t StarMalloc_threshold = (size_t)4096U - (size_t)2U;

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
  bool check = alignment > (size_t)0U && (size_t)4096U % alignment == (size_t)0U;
  if (check)
  {
    uint32_t alignment_as_u32 = (uint32_t)alignment;
    if (size <= StarMalloc_threshold)
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
        Main_Meta_sc_all.slab_region + Main_slab_region_size);
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
      Main_Meta_sc_all.slab_region + Main_slab_region_size);
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
    bool old_allocation_is_small = old_size <= (size_t)4096U;
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

