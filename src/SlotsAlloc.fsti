module SlotsAlloc

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

open Constants
open Utils2

open SlotsCommon

val allocate_slot
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md md_q: slab_metadata)
  : Steel (array U8.t)
  (slab_vprop size_class arr md md_q)
  (fun r -> A.varray r `star` slab_vprop size_class arr md md_q)
  (requires fun h0 ->
    let blob0 : t_of (slab_vprop size_class arr md md_q)
      = h0 (slab_vprop size_class arr md md_q) in
    let vs0 : _ & Seq.lseq U64.t 4 = dfst (fst blob0) in
    let v_or0 : Seq.lseq U64.t 4 = seq_u64_or (fst vs0) (snd vs0) in
    has_free_slot size_class v_or0)
  (ensures fun h0 r h1 ->
    let blob0 : t_of (slab_vprop size_class arr md md_q)
      = h0 (slab_vprop size_class arr md md_q) in
    let blob1 : t_of (slab_vprop size_class arr md md_q)
      = h1 (slab_vprop size_class arr md md_q) in
    let vs0 : _ & Seq.lseq U64.t 4 = dfst (fst blob0) in
    let vs1 : _ & Seq.lseq U64.t 4 = dfst (fst blob1) in
    let v_or0 : Seq.lseq U64.t 4 = seq_u64_or (fst vs0) (snd vs0) in
    let v_or1 : Seq.lseq U64.t 4 = seq_u64_or (fst vs1) (snd vs1) in
    not (is_empty size_class v_or1) /\
    A.length r == U32.v size_class /\
    same_base_array r arr /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) >= 0 /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) < U32.v page_size /\
    (A.offset (A.ptr_of r) - A.offset (A.ptr_of arr)) % (U32.v size_class) == 0
  )
    //U32.v (G.reveal (snd r)) < U64.n * 4 /\
    //v1 == Bitmap4.set v0 (G.reveal (snd r)))
    //TODO: is it worth having such a precise spec?
    //requires having pos as ghost in returned value
    //considering the case of multiple consecutive allocations
    //probably for testing slab filling
