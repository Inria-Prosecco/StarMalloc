module Slabs2

module UP = FStar.PtrdiffT
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module G = FStar.Ghost
module FI = FStar.Int
module L = FStar.List.Tot

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

module AL = ArrayList

open Utils2
open Slots
open Slots2
open Slabs

//TODO: remove, now likely useless
//let deallocate_slab_aux
//  (size_class: sc)
//  (partial_slabs_ptr empty_slabs_ptr full_slabs_ptr: ref SL.t)
//  (partial_slabs empty_slabs full_slabs: SL.t)
//  (slab: array U8.t{A.length slab = U32.v page_size})
//  (md: slab_metadata)
//  (ptr: array U8.t)
//  : Steel bool
//  (
//    A.varray ptr `star`
//    slab_vprop size_class slab md `star`
//    vptr empty_slabs_ptr `star`
//    SL.llist (p_empty size_class) empty_slabs `star`
//    vptr partial_slabs_ptr `star`
//    SL.llist (p_partial size_class) partial_slabs `star`
//    vptr full_slabs_ptr `star`
//    SL.llist (p_full size_class) full_slabs
//  )
//  (fun b ->
//    (if b then emp else A.varray ptr) `star`
//    SL.ind_llist (p_empty size_class) empty_slabs_ptr `star`
//    SL.ind_llist (p_partial size_class) partial_slabs_ptr `star`
//    SL.ind_llist (p_full size_class) full_slabs_ptr
//  )
//  (requires fun h0 ->
//    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab) in
//    same_base_array slab ptr /\
//    0 <= diff /\
//    diff <= U32.v page_size - U32.v size_class /\
//    (U32.v page_size) % (U32.v size_class) = 0 /\
//    sel partial_slabs_ptr h0 == partial_slabs /\
//    sel empty_slabs_ptr h0 == empty_slabs /\
//    not (SL.is_null_t partial_slabs))
//  (ensures fun _ _ _ -> True)
//  =
//  let r = deallocate_slot size_class md slab ptr in
//  if r
//  then (
//    // cf Slack discussion: flattening bijectively the lists is required
//    sladmit ();
//    SL.pack_ind (p_partial size_class) partial_slabs_ptr partial_slabs;
//    SL.pack_ind (p_empty size_class) empty_slabs_ptr empty_slabs;
//    return r
//  ) else (
//    sladmit ();
//    SL.pack_ind (p_partial size_class) partial_slabs_ptr partial_slabs;
//    SL.pack_ind (p_empty size_class) empty_slabs_ptr empty_slabs;
//    return r
//  )

open FStar.Mul

unfold
let blob = Slabs.blob
(*
#push-options "--compat_pre_typed_indexed_effects --z3rlimit 50"
let deallocate_slab
  (size_class: sc)
  //(partial_slabs_ptr empty_slabs_ptr full_slabs_ptr: ref SL.t)
  //(partial_slabs empty_slabs full_slabs: SL.t)
  (slab_region: array U8.t{A.length slab_region == U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell blob){A.length md_region = U32.v metadata_max})
  (ptr: array U8.t)
  (md_count_v: (x:U32.t{U32.v x <= U32.v metadata_max}))
  : Steel bool
  (
    A.varray ptr `star`
    AL.varraylist (A.split_l md_region (u32_to_sz md_count_v)) 0 `star`
    A.varray (A.split_l slab_region 0sz)
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    AL.varraylist (A.split_l md_region (u32_to_sz md_count_v)) 0 `star`
    A.varray (A.split_l slab_region 0sz)
  )
  (requires fun h0 ->
    //TODO: FIXME @Aymeric
    //let s = h0 (AL.varraylist (A.split_l md_region (u32_to_sz md_count_v)) 0) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab_region) in
    same_base_array ptr slab_region /\
    0 <= diff /\
    UP.fits ((U32.v page_size) * (U32.v metadata_max)) /\
    diff < (U32.v page_size) * (U32.v metadata_max) /\
    (U32.v page_size) % (U32.v size_class) = 0 /\
    U32.v md_count_v <= U32.v metadata_max

  )
  (ensures fun _ _ _ -> True)
  =
  let diff = A.ptrdiff ptr (A.split_l slab_region 0sz) in
  let diff_sz = UP.ptrdifft_to_sizet diff in
  assume (US.fits_u32);
  assert_norm (4 < FI.max_int 16);
  let diff_u32 = US.sizet_to_uint32 diff_sz in
  assert (U32.v diff_u32 == UP.v diff);
  let pos = U32.div diff_u32 page_size in
  // check diff/page_size < md_count
  if U32.lt pos md_count_v then (
    // get corresponding slab/md pointers
    let b = AL.read_in_place (A.split_l md_region (u32_to_sz md_count_v)) 0 (u32_to_sz pos) in
    // refinement: Steel issue, does not work as logical precond
    assume (snd b == slab_array slab_region pos);
    // ArrayList predicate + unpacking/packing support 1/2
    rewrite_slprop
      emp (slab_vprop size_class (snd b) (fst b))
      (fun _ -> admit ());
    // metadata check done at slots level
    let status = deallocate_slot size_class (fst b) (snd b) ptr in
    // ArrayList predicate + unpacking/packing support 2/2
    rewrite_slprop
      (slab_vprop size_class (snd b) (fst b)) emp
      (fun _ -> admit ());
    if status then (
      // update {partial, free, full}_slabs lists accordingly
      sladmit ();
      return true
    ) else (
      change_equal_slprop
        (if status then emp else A.varray ptr)
        (A.varray ptr);
      return false
    )
  ) else (
    return false
  )
*)
