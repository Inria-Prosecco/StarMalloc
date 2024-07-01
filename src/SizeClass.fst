module SizeClass

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module US = FStar.SizeT

module G = FStar.Ghost

module AL = ArrayList

module P = Steel.FractionalPermission
module SM = Steel.Memory
module A = Steel.Array

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

open Constants
open Config
open Utils2

open SlabsAlloc

#reset-options "--fuel 1 --ifuel 1"
#push-options "--ide_id_info_off"

noeq
type size_class_struct' = {
  size: sc_union;
  is_extended: bool;
  slabs_idxs: A.array US.t;
  md_count: ref US.t;
  slab_region: array U8.t;
  md_bm_region: array U64.t;
  md_bm_region_b: array bool;
  md_region: array AL.cell;
}

open Prelude
open FStar.Mul

let slab_region_size = SlabsCommon2.slab_region_size

let metadata_max_ex = SlabsCommon2.metadata_max_ex

let slab_size = SlabsCommon2.slab_size

let slab_region_size_eq_lemma (_:unit)
  : Lemma
  (slab_region_size = US.mul metadata_max_ex slab_size)
  =
  ()

//inline_for_extraction noextract
//let slab_size : (v:US.t{US.v v == US.v metadata_max * U32.v page_size /\ US.v v > 0})
//  = US.mul metadata_max (US.of_u32 page_size)

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

let size_class_vprop_sc
  (scs: size_class_struct_sc)
  : vprop
  =
  vrefinedep
    (vptr scs.md_count)
    SlabsCommon.vrefinedep_prop
    (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
      scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)

let size_class_vprop_sc_ex
  (scs: size_class_struct_sc_ex)
  : vprop
  =
  vrefinedep
    (vptr scs.md_count)
    SlabsCommon2.vrefinedep_prop
    (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
      scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)

let size_class_vprop
  (scs: size_class_struct)
  : vprop
  =
  if scs.is_extended
  then size_class_vprop_sc_ex scs
  else size_class_vprop_sc scs

let allocate_size_class_sl_lemma1_ex
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (size_class_vprop scs)) m /\
    scs.is_extended
  )
  (ensures
    SM.interp (hp_of (
      vrefinedep
        (vptr scs.md_count)
        SlabsCommon2.vrefinedep_prop
        (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
          scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    )) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      vrefinedep
        (vptr scs.md_count)
        SlabsCommon2.vrefinedep_prop
        (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
          scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

let allocate_size_class_sl_lemma1
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (size_class_vprop scs)) m /\
    not (scs.is_extended)
  )
  (ensures
    SM.interp (hp_of (
      //if scs.is_extended
      //then emp
      //else
        vrefinedep
          (vptr scs.md_count)
          SlabsCommon.vrefinedep_prop
          (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
            scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    )) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      //if scs.is_extended
      //then emp
      //else
        vrefinedep
          (vptr scs.md_count)
          SlabsCommon.vrefinedep_prop
          (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
            scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

let allocate_size_class_sl_lemma2_ex
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    scs.is_extended /\
    SM.interp (hp_of (
        vrefinedep
          (vptr scs.md_count)
          SlabsCommon2.vrefinedep_prop
          (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
            scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    )) m
  )
  (ensures
    SM.interp (hp_of (size_class_vprop scs)) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
        vrefinedep
          (vptr scs.md_count)
          SlabsCommon2.vrefinedep_prop
          (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
            scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

let allocate_size_class_sl_lemma2
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    not (scs.is_extended) /\
    SM.interp (hp_of (
        vrefinedep
          (vptr scs.md_count)
          SlabsCommon.vrefinedep_prop
          (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
            scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    )) m
  )
  (ensures
    SM.interp (hp_of (size_class_vprop scs)) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
        vrefinedep
          (vptr scs.md_count)
          SlabsCommon.vrefinedep_prop
          (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
            scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()




open MiscArith
#push-options "--fuel 0 --ifuel 0"
let mod_arith_lemma_applied
  (n: nat) (page_size sc align: pos)
  : Lemma
  (requires
    sc % align == 0 /\
    page_size % align == 0 /\
    (n % page_size) % sc == 0 /\
    align <= sc /\
    sc <= page_size
  )
  (ensures n % align == 0)
  =
  Math.Lemmas.euclidean_division_definition n page_size;
  assert (n % page_size == n - (n/page_size)*page_size);
  let n' = n % page_size in
  Math.Lemmas.euclidean_division_definition n' sc;
  assert (n' % sc == n' - (n'/sc)*sc);
  assert (n' % sc == 0);
  assert (n' == n'/sc*sc);
  assert (n - (n/page_size)*page_size == n'/sc*sc);
  assert (n = (n/page_size)*page_size + n'/sc*sc);
  lemma_mod_mul2 (n'/sc) sc align;
  lemma_mod_plus2 ((n/page_size)*page_size) (n'/sc*sc) align;
  assert (n % align = (n/page_size)*page_size % align);
  lemma_mod_mul2 (n/page_size) page_size align;
  lemma_mod_plus2 0 ((n/page_size)*page_size) align
#pop-options

#push-options "--fuel 0 --ifuel 0"
let mod_arith_lemma_applied2
  (n: nat) (page_size sc align: pos)
  : Lemma
  (requires
    sc % align == 0 /\
    page_size % align == 0 /\
    (n % page_size) % sc == 0 /\
    align <= sc /\
    sc <= page_size
  )
  (ensures n % align == 0)
  =
  Math.Lemmas.euclidean_division_definition n page_size;
  assert (n % page_size == n - (n/page_size)*page_size);
  let n' = n % page_size in
  Math.Lemmas.euclidean_division_definition n' sc;
  assert (n' % sc == n' - (n'/sc)*sc);
  assert (n' % sc == 0);
  assert (n' == n'/sc*sc);
  assert (n - (n/page_size)*page_size == n'/sc*sc);
  assert (n = (n/page_size)*page_size + n'/sc*sc);
  lemma_mod_mul2 (n'/sc) sc align;
  lemma_mod_plus2 ((n/page_size)*page_size) (n'/sc*sc) align;
  assert (n % align = (n/page_size)*page_size % align);
  lemma_mod_mul2 (n/page_size) page_size align;
  lemma_mod_plus2 0 ((n/page_size)*page_size) align
#pop-options

//let allocate_size_class_aux
//  (scs: size_class_struct)
//  (r: array U8.t)
//  : Lemma
//  (requires
//    (not scs.is_extended) /\
//    not (A.is_null r) ==> (
//      A.length r == U32.v (get_sc scs.size) /\
//      same_base_array r scs.slab_region /\
//      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
//      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v (get_sc scs.size)) == 0
//    )
//  )
//  (ensures
//    (not scs.is_extended) /\
//    not (A.is_null r) ==> (
//      A.length r == U32.v (get_sc scs.size) /\
//      same_base_array r scs.slab_region /\
//      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
//      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v (get_sc scs.size)) == 0 /\
//      array_u8_alignment r 16ul /\
//      ((U32.v page_size) % (U32.v (get_sc scs.size)) == 0 ==> array_u8_alignment r (get_sc scs.size))
//    )
//  )
//  =
//  if not (A.is_null r)
//  then (
//    assert (same_base_array r scs.slab_region);
//    assert (same_base_array scs.slab_region r);
//    assert (array_u8_alignment scs.slab_region page_size);
//    mod_arith_lemma_applied
//      (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
//      (U32.v page_size)
//      (U32.v (get_sc scs.size))
//      16;
//    assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % 16 == 0);
//    array_u8_alignment_lemma scs.slab_region r page_size 16ul;
//    if ((U32.v page_size) % (U32.v scs.size) = 0) then (
//      mod_arith_lemma_applied
//        (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
//        (U32.v page_size)
//        (U32.v scs.size)
//        (U32.v scs.size);
//      assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % (U32.v scs.size) == 0);
//      array_u8_alignment_lemma scs.slab_region r page_size scs.size
//    ) else ()
//  ) else ()

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --compat_pre_typed_indexed_effects"
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
      //((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v scs.size) == 0 /\
      array_u8_alignment r 16ul /\
      True
      //((U32.v page_size) % (U32.v scs.size) == 0 ==> array_u8_alignment r scs.size)
    )
  )

let allocate_size_class scs
  =
  if scs.is_extended
  then (
    change_slprop_rel
      (size_class_vprop scs)
      (size_class_vprop_sc_ex scs)
      (fun x y -> y == x)
      (fun m -> admit ());
      //allocate_size_class_sl_lemma1_ex scs m);
    let result = SlabsAlloc2.allocate_slab
      (get_sc_ex scs.size)
      scs.slab_region scs.md_bm_region_b scs.md_region
      scs.md_count scs.slabs_idxs in
    change_slprop_rel
      (size_class_vprop_sc_ex scs)
      (size_class_vprop scs)
      (fun x y -> x == y)
      (fun m -> admit ());
      // allocate_size_class_sl_lemma2_ex scs m);
    assume (not (A.is_null result) ==> array_u8_alignment result 16ul);
    return result
  ) else (
    change_slprop_rel
      (size_class_vprop scs)
      (size_class_vprop_sc scs)
      (fun x y -> y == x)
      (fun m -> admit ());
      //allocate_size_class_sl_lemma1_ex scs m);
    let result = SlabsAlloc.allocate_slab
      (get_sc scs.size)
      scs.slab_region scs.md_bm_region scs.md_region
      scs.md_count scs.slabs_idxs in
    change_slprop_rel
      (size_class_vprop_sc scs)
      (size_class_vprop scs)
      (fun x y -> x == y)
      (fun m -> admit ());
      // allocate_size_class_sl_lemma2_ex scs m);
    assume (not (A.is_null result) ==> array_u8_alignment result 16ul);
    return result
  )

module UP = FStar.PtrdiffT

open Steel.ArrayArith

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
    (diff' % U32.v page_size) % U32.v (get_u32 scs.size) == 0 /\
    A.length ptr == U32.v (get_u32 scs.size) /\
    same_base_array ptr scs.slab_region)
  (ensures fun h0 _ h1 -> True)

let deallocate_size_class scs ptr diff
  =
  if scs.is_extended
  then (
    change_slprop_rel
      (size_class_vprop scs)
      (size_class_vprop_sc_ex scs)
      (fun x y -> y == x)
      (fun m -> admit ());
      //allocate_size_class_sl_lemma1_ex scs m);
    let b = SlabsFree2.deallocate_slab ptr
      (get_sc_ex scs.size)
      scs.slab_region scs.md_bm_region_b scs.md_region
      scs.md_count scs.slabs_idxs
      diff in
    change_slprop_rel
      (size_class_vprop_sc_ex scs)
      (size_class_vprop scs)
      (fun x y -> x == y)
      (fun m -> admit ());
      // allocate_size_class_sl_lemma2_ex scs m);
    return b
  ) else (
    change_slprop_rel
      (size_class_vprop scs)
      (size_class_vprop_sc scs)
      (fun x y -> y == x)
      (fun m -> admit ());
      //allocate_size_class_sl_lemma1_ex scs m);
    let b = SlabsFree.deallocate_slab ptr
      (get_sc scs.size)
      scs.slab_region scs.md_bm_region scs.md_region
      scs.md_count scs.slabs_idxs
      diff in
    change_slprop_rel
      (size_class_vprop_sc scs)
      (size_class_vprop scs)
      (fun x y -> x == y)
      (fun m -> admit ());
      // allocate_size_class_sl_lemma2_ex scs m);
    return b
  )
