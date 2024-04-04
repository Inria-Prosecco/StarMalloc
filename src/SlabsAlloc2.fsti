module SlabsAlloc2

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

open Config
open Utils2

include SlabsCommon2

val allocate_slab
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  : Steel (array U8.t)
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun _ -> True)
  (ensures fun _ r _ ->
    not (A.is_null r) ==> (
      A.length r == U32.v size_class /\
      same_base_array r slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region) >= 0 /\
      True
      //((A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region)) % U32.v page_size) % (U32.v size_class) == 0
    )
  )
