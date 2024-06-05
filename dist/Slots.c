/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /nix/store/c6gw8n5jwizcqim5r1y3x4dq44xg9w51-karamel-1b809c2917853d1117034c78d978ac19642aa84a-home/krml -skip-compilation -fparentheses -tmpdir dist -library Steel.ArrayArith -static-header Steel.ArrayArith -no-prefix Steel.ArrayArith -bundle Steel.SpinLock= -bundle FStar.\*,Steel.\* -bundle StarMalloc=Map.\*,Impl.\*,Spec.\*,Main,Main.Meta,LargeAlloc[rename=StarMalloc] -bundle SlabsCommon,SlabsFree,SlabsAlloc[rename=Slabs] -bundle SlotsFree,SlotsAlloc[rename=Slots] -bundle ArrayList,ArrayListGen[rename=ArrayList] -no-prefix Main -no-prefix LargeAlloc -no-prefix Mman -no-prefix MemoryTrap -no-prefix ExternUtils -warn-error +9 -add-include Steel_SpinLock:"steel_types.h" -add-include Steel_SpinLock:"steel_base.h" obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Mul.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_Preorder.krml obj/FStar_Sealed.krml obj/FStar_Range.krml obj/FStar_Calc.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_Classical_Sugar.krml obj/FStar_List_Tot_Base.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_Int.krml obj/FStar_Int16.krml obj/Seq2.krml obj/Bitmap1.krml obj/Bitmap2.krml obj/FStar_UInt64.krml obj/Bitmap3.krml obj/Bitmap4.krml obj/FStar_Ghost.krml obj/FStar_Int64.krml obj/FStar_Int32.krml obj/FStar_Int8.krml obj/FStar_UInt16.krml obj/FStar_UInt8.krml obj/FStar_Int_Cast.krml obj/FStar_SizeT.krml obj/SeqUtils.krml obj/FStar_VConfig.krml obj/FStar_Float.krml obj/FStar_Char.krml obj/FStar_Pprint.krml obj/FStar_Issue.krml obj/FStar_TypeChecker_Core.krml obj/FStar_Errors_Msg.krml obj/FStar_Tactics_Common.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Monotonic_Pure.krml obj/FStar_Tactics_Effect.krml obj/FStar_Tactics_Unseal.krml obj/FStar_Sealed_Inhabited.krml obj/FStar_Syntax_Syntax.krml obj/FStar_Reflection_V2_Data.krml obj/FStar_Order.krml obj/FStar_Reflection_V2_Builtins.krml obj/FStar_Reflection_Const.krml obj/FStar_Tactics_V2_Builtins.krml obj/FStar_Tactics_SMT.krml obj/FStar_Tactics_Util.krml obj/FStar_Reflection_V2_Derived.krml obj/FStar_Reflection_V2_Compare.krml obj/FStar_Reflection_V2_Derived_Lemmas.krml obj/FStar_Reflection_V2.krml obj/FStar_Tactics_Visit.krml obj/FStar_Tactics_NamedView.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_Reflection_V1_Data.krml obj/FStar_Reflection_V1_Builtins.krml obj/FStar_Tactics_V1_Builtins.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Tactics_V2_SyntaxCoercions.krml obj/FStar_Tactics_V2_SyntaxHelpers.krml obj/FStar_Reflection_V2_Formula.krml obj/FStar_Tactics_V2_Derived.krml obj/FStar_Tactics_Print.krml obj/FStar_IndefiniteDescription.krml obj/FStar_Reflection_V1_Derived.krml obj/FStar_Reflection_V1_Formula.krml obj/FStar_Reflection_V1_Compare.krml obj/FStar_Reflection_V1_Derived_Lemmas.krml obj/FStar_Reflection_V1.krml obj/FStar_Tactics_V1_SyntaxHelpers.krml obj/FStar_Tactics_V1_Derived.krml obj/FStar_Tactics_V1_Logic.krml obj/FStar_Tactics_V1.krml obj/FStar_Tactics.krml obj/FStar_PtrdiffT.krml obj/FStar_Real.krml obj/Steel_FractionalPermission.krml obj/FStar_Witnessed_Core.krml obj/FStar_MSTTotal.krml obj/FStar_NMSTTotal.krml obj/FStar_PCM.krml obj/Steel_Preorder.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_PredicateExtensionality.krml obj/FStar_WellFounded.krml obj/FStar_Universe.krml obj/Steel_Heap.krml obj/Steel_Memory.krml obj/FStar_MST.krml obj/FStar_NMST.krml obj/Steel_Semantics_Hoare_MST.krml obj/Steel_Semantics_Instantiate.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_ErasedLogic.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_List.krml obj/FStar_String.krml obj/FStar_Reflection_V2_TermEq.krml obj/FStar_Tactics_Typeclasses.krml obj/FStar_Tactics_MApply.krml obj/FStar_Tactics_V2_Logic.krml obj/FStar_Tactics_V2.krml obj/FStar_Tactics_CanonCommSwaps.krml obj/FStar_Algebra_CommMonoid_Equiv.krml obj/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml obj/Steel_Effect_Common.krml obj/Steel_Effect.krml obj/Steel_Effect_Atomic.krml obj/Steel_ST_Effect.krml obj/Steel_ST_Effect_AtomicAndGhost.krml obj/Steel_ST_Effect_Atomic.krml obj/Steel_ST_Effect_Ghost.krml obj/Steel_ST_Coercions.krml obj/Steel_PCMReference.krml obj/Steel_PCMFrac.krml obj/Steel_HigherReference.krml obj/Steel_Reference.krml obj/Steel_Loops.krml obj/Steel_ST_Util.krml obj/Steel_ST_Loops.krml obj/Steel_ST_Reference.krml obj/FStar_Map.krml obj/Steel_PCMMap.krml obj/Steel_ST_PCMReference.krml obj/Steel_ST_HigherArray.krml obj/Steel_ST_Array.krml obj/Steel_Array.krml obj/Prelude.krml obj/Constants.krml obj/Utils2.krml obj/NullOrVarray.krml obj/Steel_ArrayArith.krml obj/Bitmap5.krml obj/SteelVRefineDep.krml obj/SteelOptUtils.krml obj/SteelStarSeqUtils.krml obj/ExternUtils.krml obj/MiscArith.krml obj/SizeClassSelection.krml obj/Config.krml obj/SlotsAlloc.krml obj/Helpers.krml obj/MemoryTrap.krml obj/Quarantine.krml obj/FStar_FiniteSet_Base.krml obj/FStar_FiniteSet_Ambient.krml obj/Steel_ArrayRef.krml obj/SetUtils.krml obj/ArrayListGen.krml obj/ArrayList.krml obj/Guards.krml obj/SteelVRefine2.krml obj/SlabsCommon.krml obj/SlotsFree.krml obj/SlabsFree.krml obj/SlabsAlloc.krml obj/SizeClass.krml obj/Steel_SpinLock.krml obj/Mman.krml obj/Spec_Trees.krml obj/Spec_BST.krml obj/Impl_Common.krml obj/Steel_TLArray.krml obj/Main.krml obj/Impl_Core.krml obj/Impl_Trees_Types.krml obj/Impl_Trees_M.krml obj/ROArray.krml obj/WithLock.krml obj/Spec_AVL.krml obj/Spec.krml obj/Impl_BST_M.krml obj/Impl_Trees_Rotate3_M.krml obj/Impl_Trees_Rotate2_M.krml obj/Impl_Trees_Rotate_M.krml obj/Impl_AVL_M.krml obj/Impl_Mono.krml obj/Map_M.krml obj/LargeAlloc.krml obj/Main_Meta.krml obj/StarMalloc.krml
  F* version: <unknown>
  KaRaMeL version: <unknown>
 */

#include "internal/Slots.h"

static uint8_t *slot_array(uint32_t size_class, uint8_t *arr, uint32_t pos)
{
  uint8_t *ptr = arr;
  uint32_t shift = pos * size_class;
  size_t shift_size_t = (size_t)shift;
  return ptr + shift_size_t;
}

static uint8_t *get_slot_as_returned_value(uint32_t size_class, uint8_t *arr, uint32_t pos)
{
  uint8_t *r = slot_array(size_class, arr, pos);
  return r;
}

static uint32_t get_free_slot(uint32_t size_class, uint64_t *bitmap)
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

uint8_t *SlotsAlloc_allocate_slot(uint32_t size_class, uint64_t *md, uint8_t *arr)
{
  uint32_t pos = get_free_slot(size_class, md);
  Bitmap5_bm_set(md, pos);
  uint8_t *r = get_slot_as_returned_value(size_class, arr, pos);
  uint8_t *r0 = r;
  return r0;
}

static bool deallocate_slot_aux0(uint32_t size_class, uint32_t diff)
{
  size_t diff_sz = (size_t)diff;
  return diff_sz < Utils2_rounding(size_class);
}

static uint32_t deallocate_slot_aux1(uint32_t size_class, uint32_t diff)
{
  return diff / size_class;
}

extern void SlotsFree_deallocate_zeroing(uint32_t size_class, uint8_t *ptr);

static bool deallocate_slot_(uint32_t size_class, uint64_t *md, uint8_t *ptr, size_t diff_)
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
      SlotsFree_deallocate_zeroing(size_class, ptr);
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
  uint32_t size_class,
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

