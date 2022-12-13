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

