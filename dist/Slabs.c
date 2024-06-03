/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /nix/store/c6gw8n5jwizcqim5r1y3x4dq44xg9w51-karamel-1b809c2917853d1117034c78d978ac19642aa84a-home/krml -skip-compilation -skip-makefiles -fparentheses -tmpdir dist -library Steel.ArrayArith -static-header Steel.ArrayArith -no-prefix Steel.ArrayArith -bundle Steel.SpinLock= -bundle FStar.\*,Steel.\* -bundle StarMalloc=Map.\*,Impl.\*,Spec.\*,Main,Main.Meta,LargeAlloc[rename=StarMalloc] -bundle SlabsCommon,SlabsFree,SlabsAlloc[rename=Slabs] -bundle SlotsFree,SlotsAlloc[rename=Slots] -bundle ArrayList,ArrayListGen[rename=ArrayList] -no-prefix Main -no-prefix LargeAlloc -no-prefix Mman -no-prefix MemoryTrap -warn-error +9 -add-include Steel_SpinLock:"steel_types.h" -add-include Steel_SpinLock:"steel_base.h" obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Mul.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_Preorder.krml obj/FStar_Sealed.krml obj/FStar_Range.krml obj/FStar_Calc.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_Classical_Sugar.krml obj/FStar_List_Tot_Base.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_Int.krml obj/FStar_Int16.krml obj/Seq2.krml obj/Bitmap1.krml obj/Bitmap2.krml obj/FStar_UInt64.krml obj/Bitmap3.krml obj/Bitmap4.krml obj/FStar_Int64.krml obj/FStar_Int32.krml obj/FStar_Int8.krml obj/FStar_UInt16.krml obj/FStar_UInt8.krml obj/FStar_Int_Cast.krml obj/FStar_Ghost.krml obj/FStar_SizeT.krml obj/SeqUtils.krml obj/FStar_VConfig.krml obj/FStar_Float.krml obj/FStar_Char.krml obj/FStar_Pprint.krml obj/FStar_Issue.krml obj/FStar_TypeChecker_Core.krml obj/FStar_Errors_Msg.krml obj/FStar_Tactics_Common.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Monotonic_Pure.krml obj/FStar_Tactics_Effect.krml obj/FStar_Tactics_Unseal.krml obj/FStar_Sealed_Inhabited.krml obj/FStar_Syntax_Syntax.krml obj/FStar_Reflection_V2_Data.krml obj/FStar_Order.krml obj/FStar_Reflection_V2_Builtins.krml obj/FStar_Reflection_Const.krml obj/FStar_Tactics_V2_Builtins.krml obj/FStar_Tactics_SMT.krml obj/FStar_Tactics_Util.krml obj/FStar_Reflection_V2_Derived.krml obj/FStar_Reflection_V2_Compare.krml obj/FStar_Reflection_V2_Derived_Lemmas.krml obj/FStar_Reflection_V2.krml obj/FStar_Tactics_Visit.krml obj/FStar_Tactics_NamedView.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_Reflection_V1_Data.krml obj/FStar_Reflection_V1_Builtins.krml obj/FStar_Tactics_V1_Builtins.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Tactics_V2_SyntaxCoercions.krml obj/FStar_Tactics_V2_SyntaxHelpers.krml obj/FStar_Reflection_V2_Formula.krml obj/FStar_Tactics_V2_Derived.krml obj/FStar_Tactics_Print.krml obj/FStar_IndefiniteDescription.krml obj/FStar_Reflection_V1_Derived.krml obj/FStar_Reflection_V1_Formula.krml obj/FStar_Reflection_V1_Compare.krml obj/FStar_Reflection_V1_Derived_Lemmas.krml obj/FStar_Reflection_V1.krml obj/FStar_Tactics_V1_SyntaxHelpers.krml obj/FStar_Tactics_V1_Derived.krml obj/FStar_Tactics_V1_Logic.krml obj/FStar_Tactics_V1.krml obj/FStar_Tactics.krml obj/FStar_PtrdiffT.krml obj/FStar_Real.krml obj/Steel_FractionalPermission.krml obj/FStar_Witnessed_Core.krml obj/FStar_MSTTotal.krml obj/FStar_NMSTTotal.krml obj/FStar_PCM.krml obj/Steel_Preorder.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_PredicateExtensionality.krml obj/FStar_WellFounded.krml obj/FStar_Universe.krml obj/Steel_Heap.krml obj/Steel_Memory.krml obj/FStar_MST.krml obj/FStar_NMST.krml obj/Steel_Semantics_Hoare_MST.krml obj/Steel_Semantics_Instantiate.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_ErasedLogic.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_List.krml obj/FStar_String.krml obj/FStar_Reflection_V2_TermEq.krml obj/FStar_Tactics_Typeclasses.krml obj/FStar_Tactics_MApply.krml obj/FStar_Tactics_V2_Logic.krml obj/FStar_Tactics_V2.krml obj/FStar_Tactics_CanonCommSwaps.krml obj/FStar_Algebra_CommMonoid_Equiv.krml obj/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml obj/Steel_Effect_Common.krml obj/Steel_Effect.krml obj/Steel_Effect_Atomic.krml obj/Steel_ST_Effect.krml obj/Steel_ST_Effect_AtomicAndGhost.krml obj/Steel_ST_Effect_Atomic.krml obj/Steel_ST_Effect_Ghost.krml obj/Steel_ST_Coercions.krml obj/Steel_PCMReference.krml obj/Steel_PCMFrac.krml obj/Steel_HigherReference.krml obj/Steel_Reference.krml obj/Steel_Loops.krml obj/Steel_ST_Util.krml obj/Steel_ST_Loops.krml obj/Steel_ST_Reference.krml obj/FStar_Map.krml obj/Steel_PCMMap.krml obj/Steel_ST_PCMReference.krml obj/Steel_ST_HigherArray.krml obj/Steel_ST_Array.krml obj/Steel_Array.krml obj/Prelude.krml obj/Config.krml obj/Utils2.krml obj/MiscArith.krml obj/PtrdiffWrapper.krml obj/NullOrVarray.krml obj/Steel_ArrayArith.krml obj/Bitmap5.krml obj/SteelVRefineDep.krml obj/SteelOptUtils.krml obj/SteelStarSeqUtils.krml obj/SlotsAlloc.krml obj/Helpers.krml obj/MemoryTrap.krml obj/Quarantine.krml obj/FStar_FiniteSet_Base.krml obj/FStar_FiniteSet_Ambient.krml obj/Steel_ArrayRef.krml obj/SetUtils.krml obj/ArrayListGen.krml obj/ArrayList.krml obj/Guards.krml obj/SteelVRefine2.krml obj/SlabsCommon.krml obj/SlotsFree.krml obj/SlabsFree.krml obj/SlabsAlloc.krml obj/SizeClass.krml obj/Steel_SpinLock.krml obj/Mman.krml obj/Spec_Trees.krml obj/Spec_BST.krml obj/Impl_Common.krml obj/Steel_TLArray.krml obj/Main.krml obj/Impl_Core.krml obj/Impl_Trees_Types.krml obj/Impl_Trees_M.krml obj/ROArray.krml obj/WithLock.krml obj/Spec_AVL.krml obj/Spec.krml obj/Impl_BST_M.krml obj/Impl_Trees_Rotate3_M.krml obj/Impl_Trees_Rotate2_M.krml obj/Impl_Trees_Rotate_M.krml obj/Impl_AVL_M.krml obj/Impl_Mono.krml obj/Map_M.krml obj/LargeAlloc.krml obj/Main_Meta.krml obj/StarMalloc.krml
  F* version: <unknown>
  KaRaMeL version: <unknown>
 */

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

