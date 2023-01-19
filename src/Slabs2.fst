module Slabs2

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module G = FStar.Ghost
module FU = FStar.UInt
module L = FStar.List.Tot

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

module SL = BlobList

//module Temp = TempLock

open Utils2
open Slots
open Slots2
open Slabs

let deallocate_slab_aux
  (size_class: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref SL.t)
  (partial_slabs empty_slabs: SL.t)
  (slab: array U8.t{A.length slab = U32.v page_size})
  (md: slab_metadata)
  (ptr: array U8.t)
  : Steel bool
  (
    A.varray ptr `star`
    slab_vprop size_class slab md `star`
    vptr empty_slabs_ptr `star`
    SL.llist (p_empty size_class) empty_slabs `star`
    vptr partial_slabs_ptr `star`
    SL.llist (p_partial size_class) partial_slabs
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    SL.ind_llist (p_empty size_class) empty_slabs_ptr `star`
    SL.ind_llist (p_partial size_class) partial_slabs_ptr
  )
  (requires fun h0 ->
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab) in
    same_base_array slab ptr /\
    0 <= diff /\
    diff <= U32.v page_size - U32.v size_class /\
    (U32.v page_size) % (U32.v size_class) = 0 /\
    sel partial_slabs_ptr h0 == partial_slabs /\
    sel empty_slabs_ptr h0 == empty_slabs /\
    not (SL.is_null_t partial_slabs))
  (ensures fun _ _ _ -> True)
  =
  let r = deallocate_slot size_class md slab ptr in
  if r
  then (
    // cf Slack discussion: flattening bijectively the lists is required
    sladmit ();
    SL.pack_ind (p_partial size_class) partial_slabs_ptr partial_slabs;
    SL.pack_ind (p_empty size_class) empty_slabs_ptr empty_slabs;
    return r
  ) else (
    sladmit ();
    SL.pack_ind (p_partial size_class) partial_slabs_ptr partial_slabs;
    SL.pack_ind (p_empty size_class) empty_slabs_ptr empty_slabs;
    return r
  )
