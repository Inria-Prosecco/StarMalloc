/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /nix/store/ags1nakkl1xw664acvgrildc32fm63l5-karamel-96f97c9ca09471076bcb7524978c910bc6e0090c-home/krml -skip-compilation -fparentheses -tmpdir dist -library Steel.ArrayArith -static-header Steel.ArrayArith -no-prefix Steel.ArrayArith -bundle Steel.SpinLock= -bundle FStar.\*,Steel.\* -bundle StarMalloc=Map.\*,Impl.\*,Spec.\*,Main,Main.Meta,LargeAlloc[rename=StarMalloc] -bundle SlabsCommon,SlabsFree,SlabsAlloc[rename=Slabs] -bundle SlotsFree,SlotsAlloc[rename=Slots] -bundle ArrayList,ArrayListGen[rename=ArrayList] -no-prefix Main -no-prefix LargeAlloc -no-prefix Mman -no-prefix MemoryTrap -warn-error +9 -add-include Steel_SpinLock:"steel_types.h" -add-include Steel_SpinLock:"steel_base.h" obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Mul.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_Preorder.krml obj/FStar_Sealed.krml obj/FStar_Range.krml obj/FStar_Calc.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_Classical_Sugar.krml obj/FStar_List_Tot_Base.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_Int.krml obj/FStar_Int16.krml obj/Seq2.krml obj/Bitmap1.krml obj/Bitmap2.krml obj/FStar_UInt64.krml obj/Bitmap3.krml obj/Bitmap4.krml obj/FStar_Int64.krml obj/FStar_Int32.krml obj/FStar_Int8.krml obj/FStar_UInt16.krml obj/FStar_UInt8.krml obj/FStar_Int_Cast.krml obj/FStar_Ghost.krml obj/FStar_SizeT.krml obj/SeqUtils.krml obj/FStar_VConfig.krml obj/FStar_Float.krml obj/FStar_Char.krml obj/FStar_Pprint.krml obj/FStar_Issue.krml obj/FStar_TypeChecker_Core.krml obj/FStar_Tactics_Common.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Monotonic_Pure.krml obj/FStar_Tactics_Effect.krml obj/FStar_Tactics_Unseal.krml obj/FStar_Sealed_Inhabited.krml obj/FStar_Syntax_Syntax.krml obj/FStar_Reflection_V2_Data.krml obj/FStar_Order.krml obj/FStar_Reflection_V2_Builtins.krml obj/FStar_Reflection_Const.krml obj/FStar_Tactics_V2_Builtins.krml obj/FStar_Tactics_SMT.krml obj/FStar_Tactics_Util.krml obj/FStar_Reflection_V2_Derived.krml obj/FStar_Reflection_V2_Compare.krml obj/FStar_Reflection_V2_Derived_Lemmas.krml obj/FStar_Reflection_V2.krml obj/FStar_Tactics_Visit.krml obj/FStar_Tactics_NamedView.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_Reflection_V1_Data.krml obj/FStar_Reflection_V1_Builtins.krml obj/FStar_Tactics_V1_Builtins.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Tactics_V2_SyntaxCoercions.krml obj/FStar_Tactics_V2_SyntaxHelpers.krml obj/FStar_Reflection_V2_Formula.krml obj/FStar_Tactics_V2_Derived.krml obj/FStar_Tactics_Print.krml obj/FStar_IndefiniteDescription.krml obj/FStar_Reflection_V1_Derived.krml obj/FStar_Reflection_V1_Formula.krml obj/FStar_Reflection_V1_Compare.krml obj/FStar_Reflection_V1_Derived_Lemmas.krml obj/FStar_Reflection_V1.krml obj/FStar_Tactics_V1_SyntaxHelpers.krml obj/FStar_Tactics_V1_Derived.krml obj/FStar_Tactics_V1_Logic.krml obj/FStar_Tactics_V1.krml obj/FStar_Tactics.krml obj/FStar_PtrdiffT.krml obj/FStar_Real.krml obj/Steel_FractionalPermission.krml obj/FStar_Witnessed_Core.krml obj/FStar_MSTTotal.krml obj/FStar_NMSTTotal.krml obj/FStar_PCM.krml obj/Steel_Preorder.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_PredicateExtensionality.krml obj/FStar_WellFounded.krml obj/FStar_Universe.krml obj/Steel_Heap.krml obj/Steel_Memory.krml obj/FStar_MST.krml obj/FStar_NMST.krml obj/Steel_Semantics_Hoare_MST.krml obj/Steel_Semantics_Instantiate.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_ErasedLogic.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_List.krml obj/FStar_String.krml obj/FStar_Tactics_Typeclasses.krml obj/FStar_Tactics_MApply.krml obj/FStar_Tactics_V2_Logic.krml obj/FStar_Tactics_V2.krml obj/FStar_Tactics_CanonCommSwaps.krml obj/FStar_Algebra_CommMonoid_Equiv.krml obj/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml obj/Steel_Effect_Common.krml obj/Steel_Effect.krml obj/Steel_Effect_Atomic.krml obj/Steel_ST_Effect.krml obj/Steel_ST_Effect_AtomicAndGhost.krml obj/Steel_ST_Effect_Atomic.krml obj/Steel_ST_Effect_Ghost.krml obj/Steel_ST_Coercions.krml obj/Steel_PCMReference.krml obj/Steel_PCMFrac.krml obj/Steel_HigherReference.krml obj/Steel_Reference.krml obj/Steel_Loops.krml obj/Steel_ST_Util.krml obj/Steel_ST_Loops.krml obj/Steel_ST_Reference.krml obj/FStar_Map.krml obj/Steel_PCMMap.krml obj/Steel_ST_PCMReference.krml obj/Steel_ST_HigherArray.krml obj/Steel_ST_Array.krml obj/Steel_Array.krml obj/Prelude.krml obj/Config.krml obj/Utils2.krml obj/NullOrVarray.krml obj/Steel_ArrayArith.krml obj/Bitmap5.krml obj/SteelVRefineDep.krml obj/SteelOptUtils.krml obj/SteelStarSeqUtils.krml obj/SlotsAlloc.krml obj/MemoryTrap.krml obj/Quarantine.krml obj/FStar_FiniteSet_Base.krml obj/FStar_FiniteSet_Ambient.krml obj/Steel_ArrayRef.krml obj/ArrayListGen.krml obj/Helpers.krml obj/Guards.krml obj/ArrayList.krml obj/SteelVRefine2.krml obj/SlabsCommon.krml obj/SlotsFree.krml obj/SlabsFree.krml obj/MiscArith.krml obj/SlabsAlloc.krml obj/SizeClass.krml obj/Steel_SpinLock.krml obj/Mman.krml obj/Spec_Trees.krml obj/Spec_BST.krml obj/Impl_Common.krml obj/Steel_TLArray.krml obj/Main.krml obj/Impl_Core.krml obj/Impl_Trees_Types.krml obj/Impl_Trees_M.krml obj/Spec_AVL.krml obj/Spec.krml obj/Impl_BST_M.krml obj/Impl_Trees_Rotate3_M.krml obj/Impl_Trees_Rotate2_M.krml obj/Impl_Trees_Rotate_M.krml obj/Impl_AVL_M.krml obj/Impl_Mono.krml obj/Map_M.krml obj/LargeAlloc.krml obj/ROArray.krml obj/Main_Meta.krml obj/StarMalloc.krml obj/Temp.krml
  F* version: f7c80bf6814f
  KaRaMeL version: 96f97c9ca094
 */

#ifndef __Helpers_H
#define __Helpers_H

#include "krmllib.h"

typedef void *Helpers_zero_beyond_bound;


#define __Helpers_H_DEFINED
#endif
