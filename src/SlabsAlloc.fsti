module SlabsAlloc

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

module AL = ArrayList

open Steel.Reference
open Steel.Effect
module A = Steel.Array

open FStar.Mul
open SteelVRefineDep
open Utils2

include SlabsCommon

val allocate_slab
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3 r4: ref US.t)
  : Steel (array U8.t)
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun _ -> True)
  (ensures fun _ r _ ->
    not (A.is_null r) ==> A.length r == U32.v size_class
  )
