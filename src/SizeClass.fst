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
  size: sc_full;
  slabs_idxs: A.array US.t;
  md_count: ref US.t;
  slab_region: array U8.t;
  md_bm_region: array U64.t;
  md_region: array AL.cell;
}

open Prelude
open FStar.Mul

inline_for_extraction noextract
let sc_slab_region_size : (v:US.t{US.v v == US.v metadata_max * U32.v page_size /\ US.v v > 0})
  = US.mul metadata_max (US.of_u32 page_size)

type size_class_struct = s:size_class_struct'{
  A.length s.slab_region == US.v sc_slab_region_size /\
  array_u8_alignment s.slab_region max_slab_size /\
  A.length s.md_bm_region == US.v metadata_max * 4 /\
  A.length s.md_region == US.v metadata_max /\
  A.length s.slabs_idxs == 7
}

open SteelVRefineDep

let size_class_vprop
  (scs: size_class_struct)
  : vprop
  =
  vrefinedep
    (vptr scs.md_count)
    (vrefinedep_prop scs.size)
    (size_class_vprop_aux scs.size
      scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)

let allocate_size_class_sl_lemma1
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (size_class_vprop scs)) m
  )
  (ensures
    SM.interp (hp_of (
      vrefinedep
        (vptr scs.md_count)
        (vrefinedep_prop scs.size)
        (size_class_vprop_aux scs.size
          scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    )) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      vrefinedep
        (vptr scs.md_count)
        (vrefinedep_prop scs.size)
        (size_class_vprop_aux scs.size
          scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

let allocate_size_class_sl_lemma2
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      vrefinedep
        (vptr scs.md_count)
        (vrefinedep_prop scs.size)
        (size_class_vprop_aux scs.size
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
        (vrefinedep_prop scs.size)
        (size_class_vprop_aux scs.size
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

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
val allocate_size_class_aux
  (scs: size_class_struct)
  (r: array U8.t)
  : Lemma
  (requires
    not (A.is_null r) ==> (
      A.length r == U32.v scs.size.sc /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v scs.size.slab_size) % (U32.v scs.size.sc) == 0
    )
  )
  (ensures
    not (A.is_null r) ==> (
      A.length r == U32.v scs.size.sc /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v scs.size.slab_size) % (U32.v scs.size.sc) == 0 /\
      //(U32.v scs.size.sc <= U32.v page_size ==>
      array_u8_alignment r 16ul /\
      ((U32.v scs.size.slab_size) % (U32.v scs.size.sc) == 0 ==> array_u8_alignment r scs.size.sc)
    )
  )

let allocate_size_class_aux scs r
  =
  if not (A.is_null r)
  then (
    assert (same_base_array r scs.slab_region);
    assert (same_base_array scs.slab_region r);
    assert (array_u8_alignment scs.slab_region max_slab_size);
    mod_arith_lemma_applied
      (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
      (U32.v scs.size.slab_size)
      (U32.v scs.size.sc)
      16;
    assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % 16 == 0);
    array_u8_alignment_lemma scs.slab_region r max_slab_size 16ul;
    // no boundary crossing of allocations for size classes <= 4096
    // allows to retrieve alignment, see Constants.fst
    if ((U32.v scs.size.slab_size) % (U32.v scs.size.sc) = 0) then (
      mod_arith_lemma_applied
        (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
        (U32.v scs.size.slab_size)
        (U32.v scs.size.sc)
        (U32.v scs.size.sc);
      assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % (U32.v scs.size.sc) == 0);
      array_u8_alignment_lemma scs.slab_region r max_slab_size scs.size.sc
    ) else ()
  ) else ()

let allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    not (A.is_null r) ==> (
      A.length r == U32.v scs.size.sc /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v scs.size.slab_size) % (U32.v scs.size.sc) == 0 /\
      //(U32.v scs.size.sc <= U32.v page_size ==>
      array_u8_alignment r 16ul /\
      ((U32.v scs.size.slab_size) % (U32.v scs.size.sc) == 0 ==> array_u8_alignment r scs.size.sc)
    )
  )
  =
  change_slprop_rel
    (size_class_vprop scs)
    (vrefinedep
      (vptr scs.md_count)
      (vrefinedep_prop scs.size)
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let result = allocate_slab
    scs.size
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count scs.slabs_idxs in
  change_slprop_rel
    (vrefinedep
      (vptr scs.md_count)
      (vrefinedep_prop scs.size)
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (size_class_vprop scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  allocate_size_class_aux scs result;
  return result

open SlabsFree

module UP = FStar.PtrdiffT

open Steel.ArrayArith

let deallocate_size_class
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
    (diff' % U32.v scs.size.slab_size) % U32.v scs.size.sc == 0 /\
    A.length ptr == U32.v scs.size.sc /\
    same_base_array ptr scs.slab_region)
  (ensures fun h0 _ h1 -> True)
  =
  change_slprop_rel
    (size_class_vprop scs)
    (vrefinedep
      (vptr scs.md_count)
      (vrefinedep_prop scs.size)
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let b = deallocate_slab ptr
    scs.size
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count scs.slabs_idxs diff in
  change_slprop_rel
    (vrefinedep
      (vptr scs.md_count)
      (vrefinedep_prop scs.size)
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (size_class_vprop scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  return b
