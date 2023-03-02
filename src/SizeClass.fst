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

open Utils2
open SlabsAlloc

#reset-options "--fuel 1 --ifuel 1"
#push-options "--ide_id_info_off"

//TODO: remove blob, use ptrdiff style
//TODO: improve max_sc bound, use better spec'ed ffs64

open FStar.Mul
noeq
type size_class_struct' = {
  size: sc;
  // empty
  empty_slabs: ref US.t;
  // partial
  partial_slabs: ref US.t;
  // full
  full_slabs: ref US.t;
  // guard
  guard_slabs: ref US.t;
  md_count: ref U32.t;
  slab_region: array U8.t;
  //TODO: due to karamel extraction issue + sl proof workaround
  md_bm_region: array U64.t;
  md_region: array AL.cell;
  //lock: ref bool;
}

open Prelude

inline_for_extraction noextract
let slab_size : (v:US.t{US.v v == U32.v metadata_max * U32.v page_size})
  = US.of_u32 2147483648ul

type size_class_struct = s:size_class_struct'{
  A.length s.slab_region == US.v slab_size /\
  A.length s.md_bm_region == U32.v metadata_max * 4 /\
  A.length s.md_region == U32.v metadata_max
}

open SteelVRefineDep

let size_class_vprop
  (scs: size_class_struct)
  : vprop
  =
  vrefinedep
    (vptr scs.md_count)
    vrefinedep_prop
    (size_class_vprop_aux scs.size
      scs.slab_region scs.md_bm_region scs.md_region
      scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs)

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
        vrefinedep_prop
        (size_class_vprop_aux scs.size
          scs.slab_region scs.md_bm_region scs.md_region
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs)
    )) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      vrefinedep
        (vptr scs.md_count)
        vrefinedep_prop
        (size_class_vprop_aux scs.size
          scs.slab_region scs.md_bm_region scs.md_region
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs)
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
        vrefinedep_prop
        (size_class_vprop_aux scs.size
          scs.slab_region scs.md_bm_region scs.md_region
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs)
    )) m
  )
  (ensures
    SM.interp (hp_of (size_class_vprop scs)) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      vrefinedep
        (vptr scs.md_count)
        vrefinedep_prop
        (size_class_vprop_aux scs.size
          scs.slab_region scs.md_bm_region scs.md_region
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs)
    ) m
  )
  = ()

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  change_slprop_rel
    (size_class_vprop scs)
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let result = allocate_slab
    scs.size
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count
    scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs in
  change_slprop_rel
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs))
    (size_class_vprop scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  return result

open SlabsFree

module UP = FStar.PtrdiffT

open Steel.ArrayArith

inline_for_extraction noextract
let deallocate_size_class
  (scs: size_class_struct)
  (ptr: array U8.t)
  : Steel bool
  (A.varray ptr `star`
  size_class_vprop scs)
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    size_class_vprop scs)
  (requires fun h0 ->
    within_bounds (A.split_l scs.slab_region 0sz) ptr (A.split_r scs.slab_region slab_size))
  (ensures fun h0 _ h1 -> True)
  =
  change_slprop_rel
    (size_class_vprop scs)
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let diff = G.hide (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of scs.slab_region)) in
  [@inline_let]
  let a0 = A.split_l scs.slab_region 0sz in
  [@inline_let]
  let a1 = A.split_r scs.slab_region slab_size in
  within_bounds_elim a0 a1 ptr;
  // Needed for the assert below
  A.intro_fits_ptrdiff32 ();
  assume (UP.fits (G.reveal diff));
  let b = deallocate_slab ptr
    scs.size
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count
    scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs in
  change_slprop_rel
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs))
    (size_class_vprop scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  return b
