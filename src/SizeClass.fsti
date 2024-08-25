module SizeClass

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module A = Steel.Array
module R = Steel.Reference
module AL = ArrayList

open Steel.Effect.Atomic
open Steel.Effect

open Constants
open Config
open Utils2

noeq
type size_class_struct' = {
  size: sc_union;
  is_extended: bool;
  slabs_idxs: A.array US.t;
  md_count: R.ref US.t;
  slab_region: array U8.t;
  md_bm_region: array U64.t;
  md_bm_region_b: array bool;
  md_region: array AL.cell;
}

inline_for_extraction noextract
let slab_region_size = SlabsCommon2.slab_region_size

inline_for_extraction noextract
let metadata_max_ex = SlabsCommon2.metadata_max_ex

inline_for_extraction noextract
let slab_size = SlabsCommon2.slab_size

open FStar.Mul
type size_class_struct = s:size_class_struct'{
  array_u8_alignment s.slab_region page_size /\
  A.length s.slab_region == US.v slab_region_size /\
  A.length s.slabs_idxs == 7 /\
  // prove equivalence
  (s.is_extended ==> (
    Sc_ex? s.size /\
    s.md_bm_region == A.null #U64.t /\
    A.length s.md_bm_region_b == US.v metadata_max_ex/\
    A.length s.md_region == US.v metadata_max_ex
  )) /\
  (not s.is_extended ==> (
    Sc? s.size /\
    s.md_bm_region_b == A.null #bool /\
    A.length s.md_bm_region == US.v metadata_max * 4 /\
    A.length s.md_region == US.v metadata_max
  ))
}

open SteelVRefineDep

unfold
type size_class_struct_sc = s:size_class_struct{not s.is_extended}

unfold
type size_class_struct_sc_ex = s:size_class_struct{s.is_extended}

//TODO: should be abstract
let size_class_vprop_sc
  (scs: size_class_struct_sc)
  : vprop
  =
  vrefinedep
    (R.vptr scs.md_count)
    SlabsCommon.vrefinedep_prop
    (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
      scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)

//TODO: should be abstract
let size_class_vprop_sc_ex
  (scs: size_class_struct_sc_ex)
  : vprop
  =
  vrefinedep
    (R.vptr scs.md_count)
    SlabsCommon2.vrefinedep_prop
    (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
      scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)

val size_class_vprop
  (scs: size_class_struct)
  : vprop

val size_class_vprop_reveal
  (scs: size_class_struct)
  : Lemma
  (size_class_vprop scs ==
    (if scs.is_extended
    then size_class_vprop_sc_ex scs
    else size_class_vprop_sc scs)
  )

val allocate_size_class_sc
  (scs: size_class_struct_sc)
  : Steel (array U8.t)
  (size_class_vprop_sc scs)
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    size_class_vprop_sc scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let sc_size = get_sc scs.size in
    not (A.is_null r) ==> (
      A.length r == U32.v sc_size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v (get_u32 scs.size)) == 0 /\
      array_u8_alignment r 16ul /\
      True
      //((U32.v page_size) % (U32.v scs.size) == 0 ==> array_u8_alignment r scs.size)
    )
  )

val deallocate_size_class_sc
  (scs: size_class_struct_sc)
  (ptr: array U8.t)
  (diff: US.t)
  : Steel bool
  (A.varray ptr `star`
  size_class_vprop_sc scs)
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    size_class_vprop_sc scs)
  (requires fun h0 ->
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of scs.slab_region) in
    0 <= diff' /\
    US.v diff = diff' /\
    (diff' % U32.v page_size) % U32.v (get_u32 scs.size) == 0 /\
    A.length ptr == U32.v (get_u32 scs.size) /\
    same_base_array ptr scs.slab_region)
  (ensures fun h0 _ h1 -> True)

val allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let sc_size = get_u32 scs.size in
    not (A.is_null r) ==> (
      A.length r == U32.v sc_size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      (scs.is_extended ==> (
        (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % US.v slab_size == 0 /\
        //((U32.v page_size) % (U32.v scs.size) == 0 ==> array_u8_alignment r scs.size)
        True
      )) /\
      (not scs.is_extended ==> (
        ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v (get_u32 scs.size)) == 0 /\
        True
        //array_u8_alignment r slab_size
      )) /\
      array_u8_alignment r 16ul
    )
  )

val deallocate_size_class
  (scs: size_class_struct)
  (ptr: array U8.t)
  (diff: US.t)
  : Steel bool
  (A.varray ptr `star`
  size_class_vprop scs)
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    size_class_vprop scs)
  (requires fun h0 ->
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of scs.slab_region) in
    0 <= diff' /\
    US.v diff = diff' /\
    (scs.is_extended ==> (
      diff' % US.v slab_size == 0
    )) /\
    (not scs.is_extended ==> (
      (diff' % U32.v page_size) % U32.v (get_u32 scs.size) == 0
    )) /\
    A.length ptr == U32.v (get_u32 scs.size) /\
    same_base_array ptr scs.slab_region)
  (ensures fun h0 _ h1 -> True)
