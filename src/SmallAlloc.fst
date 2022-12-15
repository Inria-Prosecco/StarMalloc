module SmallAlloc

open Utils2
open Slabs

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module SL = Selectors.LList
module A = Steel.Array
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module G = FStar.Ghost

//let partial_slabs : SL.t blob
//  = SL.null_t
//let empty_slabs : SL.t blob
//  = SL.null_t
//
//let partial_slabs_ptr : ref (SL.t blob)
//  = null
//let empty_slabs_ptr : ref (SL.t blob)
//  = null
//
//let status : U64.t
//  = 0UL

let small_alloc
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  : Steel (array U8.t)
  (SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr)
  (fun r ->
  A.varray r `star`
  SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
  =
  //if (U64.eq status 0UL)
  //then (
  //  ()
  //);
  let r = allocate_slab sc partial_slabs_ptr empty_slabs_ptr (G.hide True) in
  return r

module L = FStar.List.Tot
module TLA = Steel.TLArray

//WARNING: attributes but non-ghost type required
open SizeClass

//noextract inline_for_extraction
//let null_sc_struct (size_class: sc) : size_class_struct = {
//  size = size_class;
//  partial_slabs = null;
//  empty_slabs = null;
//  metadata_allocated = 0ul;
//  //region_start = null;
//}
//
//noextract inline_for_extraction
//let size_classes_spec : list sc = [16ul;32ul;64ul]
//
//noextract inline_for_extraction
//let size_classes_struct
//  : list size_class_struct
//  = normalize_term (L.map null_sc_struct size_classes_spec)
//
//let size_classes_extracted
//  = TLA.create size_classes_struct
//
////TODO: n_arena is required
////top-level const uint = length of size_classes_extracted
////implies TLA.length should be extracted?
//
////TODO: TLArrays extracted as const
////leads to init necessary in C
////with_local trick?
//
//module U32 = FStar.UInt32
//
//let select_size_class (size: U32.t)
//  : Steel (G.erased sc & U32.t)
//  emp (fun _ -> emp)
//  (requires fun _ -> U32.v size <= max_sc)
//  (ensures fun _ r _ ->
//    U32.lte size (G.reveal (fst r)) /\
//    L.nth size_classes_spec (U32.v (snd r)) == Some (G.reveal (fst r))
//  )
//  =
//  assume (TLA.length size_classes_extracted == L.length size_classes_spec);
//  //admit ();
//  //let r = TLA.get size_classes_extracted 0ul in
//  //return (G.hide 0ul, r)
//  if U32.lte size 16ul then (
//    return (G.hide 16ul, 0ul)
//  ) else if U32.lte size 32ul then (
//    return (G.hide 32ul, 1ul)
//  ) else (
//    return (G.hide 64ul, 2ul)
//  )
