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

open Config
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
  // quarantine
  quarantine_slabs: ref US.t;
  md_count: ref US.t;
  slab_region: array U8.t;
  //TODO: due to karamel extraction issue + sl proof workaround
  md_bm_region: array U64.t;
  md_region: array AL.cell;
  //lock: ref bool;
}

open Prelude

inline_for_extraction noextract
let slab_size : (v:US.t{US.v v == US.v metadata_max * U32.v page_size})
  = US.mul metadata_max (US.of_u32 page_size)

type size_class_struct = s:size_class_struct'{
  A.length s.slab_region == US.v slab_size /\
  array_u8_proper_alignment s.slab_region /\
  A.length s.md_bm_region == US.v metadata_max * 4 /\
  A.length s.md_region == US.v metadata_max
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
      scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs)

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
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs)
    )) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      vrefinedep
        (vptr scs.md_count)
        vrefinedep_prop
        (size_class_vprop_aux scs.size
          scs.slab_region scs.md_bm_region scs.md_region
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs)
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
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs)
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
          scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs)
    ) m
  )
  = ()

#push-options "--fuel 0 --ifuel 0"
let mod_arith_lemma
  (n: nat) (k1 k2: pos)
  : Lemma
  (requires
    k1 % k2 == 0 /\
    k2 <= k1
  )
  (ensures
    (n % k1) % k2 == n % k2
  )
  =
  calc (==) {
    ((n / k1) * k1) % k2;
    == { Math.Lemmas.lemma_mod_mul_distr_r (n / k1) k1 k2 }
    ((n / k1) * (k1 % k2)) % k2;
    == { () }
    0;
  };
  assert (((n / k1) * k1) % k2 == 0);
  calc (==) {
    (n % k1) % k2;
    == { FStar.Math.Lemmas.euclidean_division_definition n k1 }
    (n - (n / k1) * k1) % k2;
    == { FStar.Math.Lemmas.lemma_mod_sub_distr n ((n / k1) * k1) k2 }
    (n - ((n / k1) * k1) % k2) % k2;
    == { () }
    n % k2;
  }

let lemma_mod_plus2 (a k: int) (n: pos)
  : Lemma
  (requires
    k % n == 0
  )
  (ensures
    (a + k) % n == a % n
  )
  =
  assert (k == k/n*n);
  let k' = k/n in
  Math.Lemmas.lemma_mod_plus a k' n

let lemma_mod_mul2 (a k: int) (n: pos)
  : Lemma
  (requires
    k % n == 0
  )
  (ensures
    (a * k) % n == 0
  )
  =
  Math.Lemmas.lemma_mod_mul_distr_r a k n

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

let allocate_size_class_aux
  (scs: size_class_struct)
  (r: array U8.t)
  : Lemma
  (requires
    not (A.is_null r) ==> (
      A.length r == U32.v scs.size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v scs.size) == 0
    )
  )
  (ensures
    not (A.is_null r) ==> (
      A.length r == U32.v scs.size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v scs.size) == 0 /\
      array_u8_proper_alignment r
    )
  )
  =
  if not (A.is_null r)
  then (
    assert (same_base_array r scs.slab_region);
    assert (same_base_array scs.slab_region r);
    assert (array_u8_proper_alignment scs.slab_region);
    mod_arith_lemma_applied
      (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
      (U32.v page_size)
      (U32.v scs.size)
      16;
    assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % 16 == 0);
    array_u8_proper_alignment_lemma scs.slab_region r
  ) else ()

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
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
      A.length r == U32.v scs.size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v scs.size) == 0 /\
      array_u8_proper_alignment r
    )
  )
  =
  change_slprop_rel
    (size_class_vprop scs)
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let result = allocate_slab
    scs.size
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count
    scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs in
  change_slprop_rel
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs))
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
    (diff' % U32.v page_size) % U32.v scs.size == 0 /\
    A.length ptr == U32.v scs.size /\
    same_base_array ptr scs.slab_region)
  (ensures fun h0 _ h1 -> True)
  =
  change_slprop_rel
    (size_class_vprop scs)
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let b = deallocate_slab ptr
    scs.size
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count
    scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs diff in
  change_slprop_rel
    (vrefinedep
      (vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size
        scs.slab_region scs.md_bm_region scs.md_region
        scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs))
    (size_class_vprop scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  return b
