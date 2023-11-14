module SlabsFree

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT
module UP = FStar.PtrdiffT

module AL = ArrayList

open Steel.Reference
open Steel.Effect
module A = Steel.Array

open FStar.Mul
open SteelVRefineDep

open Config
open Utils2

include SlabsCommon

module RB = RingBuffer

val deallocate_slab
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (r_ringbuffer: array US.t{A.length r_ringbuffer = US.v RB.max_size})
  (r_in r_out r_size: ref US.t)
  (diff_: US.t)
  : Steel bool
  (
    A.varray ptr `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 r_ringbuffer r_in r_out r_size)
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 r_ringbuffer r_in r_out r_size)
  )
  (requires fun _ ->
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab_region) in
    same_base_array ptr slab_region /\
    US.v diff_ = diff' /\
    0 <= diff' /\
    (diff' % U32.v page_size) % U32.v size_class == 0 /\
    //diff' < US.v metadata_max * U32.v page_size /\
    //diff' % U32.v size_class = 0 /\
    A.length ptr == U32.v size_class
  )
  (ensures fun _ _ _ -> True)
