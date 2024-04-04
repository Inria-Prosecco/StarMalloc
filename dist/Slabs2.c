/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /nix/store/1b0xvj8l1s7jbr6wk9qr18h0lgpbfqdi-karamel-08bfa78ae1df5639446e6c5897b07c9823fbf3b0-home/krml -skip-compilation -fparentheses -tmpdir dist -library Steel.ArrayArith -static-header Steel.ArrayArith -no-prefix Steel.ArrayArith -bundle Steel.SpinLock= -bundle FStar.\*,Steel.\* -bundle StarMalloc=Map.\*,Impl.\*,Spec.\*,Main,Main.Meta,LargeAlloc[rename=StarMalloc] -bundle SlabsCommon,SlabsFree,SlabsAlloc[rename=Slabs] -bundle SlabsCommon2,SlabsFree2,SlabsAlloc2[rename=Slabs2] -bundle SlotsFree,SlotsAlloc[rename=Slots] -bundle ArrayList,ArrayListGen[rename=ArrayList] -no-prefix Main -no-prefix LargeAlloc -no-prefix Mman -no-prefix MemoryTrap -warn-error +9 -add-include Steel_SpinLock:"steel_types.h" -add-include Steel_SpinLock:"steel_base.h" obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Mul.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_Preorder.krml obj/FStar_Sealed.krml obj/FStar_Range.krml obj/FStar_Calc.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_Classical_Sugar.krml obj/FStar_List_Tot_Base.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_Int.krml obj/FStar_Int16.krml obj/Seq2.krml obj/Bitmap1.krml obj/Bitmap2.krml obj/FStar_UInt64.krml obj/Bitmap3.krml obj/Bitmap4.krml obj/FStar_Int64.krml obj/FStar_Int32.krml obj/FStar_Int8.krml obj/FStar_UInt16.krml obj/FStar_UInt8.krml obj/FStar_Int_Cast.krml obj/FStar_Ghost.krml obj/FStar_SizeT.krml obj/SeqUtils.krml obj/FStar_VConfig.krml obj/FStar_Float.krml obj/FStar_Char.krml obj/FStar_Pprint.krml obj/FStar_Issue.krml obj/FStar_TypeChecker_Core.krml obj/FStar_Tactics_Common.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Monotonic_Pure.krml obj/FStar_Tactics_Effect.krml obj/FStar_Tactics_Unseal.krml obj/FStar_Sealed_Inhabited.krml obj/FStar_Syntax_Syntax.krml obj/FStar_Reflection_V2_Data.krml obj/FStar_Order.krml obj/FStar_Reflection_V2_Builtins.krml obj/FStar_Reflection_Const.krml obj/FStar_Tactics_V2_Builtins.krml obj/FStar_Tactics_SMT.krml obj/FStar_Tactics_Util.krml obj/FStar_Reflection_V2_Derived.krml obj/FStar_Reflection_V2_Compare.krml obj/FStar_Reflection_V2_Derived_Lemmas.krml obj/FStar_Reflection_V2.krml obj/FStar_Tactics_Visit.krml obj/FStar_Tactics_NamedView.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_Reflection_V1_Data.krml obj/FStar_Reflection_V1_Builtins.krml obj/FStar_Tactics_V1_Builtins.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Tactics_V2_SyntaxCoercions.krml obj/FStar_Tactics_V2_SyntaxHelpers.krml obj/FStar_Reflection_V2_Formula.krml obj/FStar_Tactics_V2_Derived.krml obj/FStar_Tactics_Print.krml obj/FStar_IndefiniteDescription.krml obj/FStar_Reflection_V1_Derived.krml obj/FStar_Reflection_V1_Formula.krml obj/FStar_Reflection_V1_Compare.krml obj/FStar_Reflection_V1_Derived_Lemmas.krml obj/FStar_Reflection_V1.krml obj/FStar_Tactics_V1_SyntaxHelpers.krml obj/FStar_Tactics_V1_Derived.krml obj/FStar_Tactics_V1_Logic.krml obj/FStar_Tactics_V1.krml obj/FStar_Tactics.krml obj/FStar_PtrdiffT.krml obj/FStar_Real.krml obj/Steel_FractionalPermission.krml obj/FStar_Witnessed_Core.krml obj/FStar_MSTTotal.krml obj/FStar_NMSTTotal.krml obj/FStar_PCM.krml obj/Steel_Preorder.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_PredicateExtensionality.krml obj/FStar_WellFounded.krml obj/FStar_Universe.krml obj/Steel_Heap.krml obj/Steel_Memory.krml obj/FStar_MST.krml obj/FStar_NMST.krml obj/Steel_Semantics_Hoare_MST.krml obj/Steel_Semantics_Instantiate.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_ErasedLogic.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_List.krml obj/FStar_String.krml obj/FStar_Reflection_V2_TermEq.krml obj/FStar_Tactics_Typeclasses.krml obj/FStar_Tactics_MApply.krml obj/FStar_Tactics_V2_Logic.krml obj/FStar_Tactics_V2.krml obj/FStar_Tactics_CanonCommSwaps.krml obj/FStar_Algebra_CommMonoid_Equiv.krml obj/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml obj/Steel_Effect_Common.krml obj/Steel_Effect.krml obj/Steel_Effect_Atomic.krml obj/Steel_ST_Effect.krml obj/Steel_ST_Effect_AtomicAndGhost.krml obj/Steel_ST_Effect_Atomic.krml obj/Steel_ST_Effect_Ghost.krml obj/Steel_ST_Coercions.krml obj/Steel_PCMReference.krml obj/Steel_PCMFrac.krml obj/Steel_HigherReference.krml obj/Steel_Reference.krml obj/Steel_Loops.krml obj/Steel_ST_Util.krml obj/Steel_ST_Loops.krml obj/Steel_ST_Reference.krml obj/FStar_Map.krml obj/Steel_PCMMap.krml obj/Steel_ST_PCMReference.krml obj/Steel_ST_HigherArray.krml obj/Steel_ST_Array.krml obj/Steel_Array.krml obj/Prelude.krml obj/Config.krml obj/Utils2.krml obj/NullOrVarray.krml obj/Bitmap5.krml obj/SteelVRefineDep.krml obj/SteelOptUtils.krml obj/SteelStarSeqUtils.krml obj/SlotsAlloc.krml obj/Helpers.krml obj/MemoryTrap.krml obj/Quarantine.krml obj/FStar_FiniteSet_Base.krml obj/FStar_FiniteSet_Ambient.krml obj/Steel_ArrayRef.krml obj/SetUtils.krml obj/ArrayListGen.krml obj/ArrayList.krml obj/Guards.krml obj/SteelVRefine2.krml obj/SlabsCommon.krml obj/SlotsFree.krml obj/SlabsFree.krml obj/Quarantine2.krml obj/Guards2.krml obj/SlabsCommon2.krml obj/SlabsFree2.krml obj/Steel_ArrayArith.krml obj/SlabsAlloc.krml obj/SlabsAlloc2.krml obj/MiscArith.krml obj/SizeClass.krml obj/Steel_SpinLock.krml obj/Mman.krml obj/Spec_Trees.krml obj/Spec_BST.krml obj/Impl_Common.krml obj/Steel_TLArray.krml obj/Main.krml obj/Impl_Core.krml obj/Impl_Trees_Types.krml obj/Impl_Trees_M.krml obj/Spec_AVL.krml obj/Spec.krml obj/Impl_BST_M.krml obj/Impl_Trees_Rotate3_M.krml obj/Impl_Trees_Rotate2_M.krml obj/Impl_Trees_Rotate_M.krml obj/Impl_AVL_M.krml obj/Impl_Mono.krml obj/Map_M.krml obj/LargeAlloc.krml obj/ROArray.krml obj/Main_Meta.krml obj/StarMalloc.krml obj/WithLock.krml
  F* version: <unknown>
  KaRaMeL version: <unknown>
 */

#include "internal/Slabs2.h"

#include "internal/ArrayList.h"

size_t SlabsCommon2_slab_region_size = (size_t)68719476736U;

size_t SlabsCommon2_slab_size = (size_t)4096U * (size_t)64U;

size_t SlabsCommon2_metadata_max_ex = (size_t)262144U;

typedef bool *slab_metadata;

static uint8_t *allocate_slot(uint8_t *arr, bool *md)
{
  bool b = md[0U];
  md[0U] = !b;
  return arr;
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
  KRML_MAYBE_UNUSED_VAR(size_class);
  KRML_MAYBE_UNUSED_VAR(slab_region);
  KRML_MAYBE_UNUSED_VAR(md_bm_region);
  size_t md_count_v_ = *md_count;
  size_t idx1_ = r_idxs[0U];
  size_t idx3_ = r_idxs[2U];
  size_t pos = diff_ / (size_t)4096U;
  if (pos < md_count_v_)
  {
    uint32_t status1 = ArrayList_read_in_place(md_region, pos);
    if (status1 == 2U)
    {
      bool b = true;
      if (b)
      {
        size_t v = ArrayList_remove(md_region, idx3_, pos);
        size_t idx3_ = v;
        ArrayList_insert(md_region, idx1_, pos, 0U);
        r_idxs[2U] = idx3_;
        r_idxs[0U] = pos;
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

static void allocate_slab_aux_3_3_2(uint32_t size_class)
{
  KRML_MAYBE_UNUSED_VAR(size_class);
}

static void allocate_slab_aux_3_3(uint32_t size_class)
{
  allocate_slab_aux_3_3_2(size_class);
}

static void
allocate_slab_aux_3(
  uint32_t size_class,
  ArrayList_cell *md_region,
  size_t *md_count,
  size_t *r_idxs,
  size_t md_count_v,
  size_t idx1
)
{
  ArrayList_insert(md_region, idx1, md_count_v, 0U);
  allocate_slab_aux_3_3(size_class);
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

static void allocate_slab_aux_4_aux2(uint32_t size_class)
{
  KRML_MAYBE_UNUSED_VAR(size_class);
}

static bounded_tuple_
allocate_slab_aux_4(
  uint32_t size_class,
  ArrayList_cell *md_region,
  size_t *r_idxs,
  size_t idx1,
  size_t idx5,
  size_t idx6,
  size_t idx7
)
{
  bounded_tuple_ r = allocate_slab_aux_4_aux1(md_region, idx1, idx5, idx6, idx7);
  allocate_slab_aux_4_aux2(size_class);
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
    size_t shift_size_t0 = idx1_ * SlabsCommon2_slab_size;
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
      idxs = allocate_slab_aux_4(size_class, md_region, r_idxs, idx1_, idx5_, idx6_, idx7_);
      uint8_t *ptr0 = slab_region;
      size_t shift_size_t0 = idxs.x * SlabsCommon2_slab_size;
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
      bool b1 = md_count_v_0 + (size_t)1U <= SlabsCommon2_metadata_max_ex;
      if (b1)
      {
        allocate_slab_aux_3(size_class, md_region, md_count, r_idxs, md_count_v_, idx1_);
        uint8_t *ptr0 = slab_region;
        size_t shift_size_t0 = md_count_v_ * SlabsCommon2_slab_size;
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

