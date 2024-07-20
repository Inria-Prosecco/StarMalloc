module SlotsFree

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

open Constants
open Utils2

open SlotsCommon


val deallocate_slot
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md md_q: slab_metadata)
  (ptr: array U8.t)
  (diff_: US.t)
  : Steel bool
  (A.varray ptr `star` slab_vprop size_class arr md md_q)
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    slab_vprop size_class arr md md_q)
  (requires fun h0 ->
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    //TODO: improve spec
    //let blob0 : t_of (slab_vprop size_class arr md))
    //  = h0 (slab_vprop size_class arr md) in
    //let v0 : Seq.lseq U64.t 4 = dfst blob0 in
    //not (is_empty size_class v0))
    same_base_array arr ptr /\
    0 <= diff /\
    diff < U32.v page_size /\
    diff % U32.v size_class == 0 /\
    US.v diff_ = diff /\
    A.length ptr == U32.v size_class
  )
  (ensures fun h0 b h1 ->
    //TODO: improve spec
    //let blob0 : t_of (slab_vprop size_class arr md md_q)
    //  = h0 (slab_vprop size_class arr md md_q) in
    //let v0 : _ & Seq.lseq U64.t 4 = dfst (fst blob0) in
    //let blob1 : t_of (slab_vprop size_class arr md md_q)
    //  = h1 (slab_vprop size_class arr md md_q) in
    //let v1 : _ & Seq.lseq U64.t 4 = dfst (fst blob1) in
    //(b ==> not (is_full size_class (fst v1))) /\
    True
    //(not b ==> v1 == v0)
  )
