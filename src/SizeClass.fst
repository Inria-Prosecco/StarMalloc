module SizeClass


module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Ghost

module SL = Selectors.LList
open Steel.FractionalPermission
module Mem = Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SR = Steel.Reference
module A = Steel.Array

open Utils2
open SlabsUtils

assume val f (md: slab_metadata) : arr:array U8.t{A.length arr = U32.v page_size}

[@@ __reduce__]
unfold let p (size_class: sc)
  =
  fun (md: slab_metadata)
  ->
  (A.varray md `star`
  slab_vprop size_class (f md) 0 (U32.v (nb_slots size_class)))

[@@ __reduce__]
unfold let p_empty (size_class: sc)
  =
  fun (md: slab_metadata)
  ->
  (A.varray md `vrefine`
    (fun s ->
      Seq.index s 0 = 0UL /\
      Seq.index s 1 = 0UL /\
      Seq.index s 2 = 0UL /\
      Seq.index s 3 = 0UL))
  `star`
  slab_vprop size_class (f md) 0 (U32.v (nb_slots size_class))

noeq
type size_class_struct = {
  size: sc;
  partial_slabs: ref (SL.t slab_metadata);
  empty_slabs: ref (SL.t slab_metadata);
  region_start: array (arr:array U8.t{A.length arr = U32.v page_size});
  lock: ref bool;
  metadata_allocated: U32.t;
}

noeq
type blob = {
  scs_v: size_class_struct;
  partial_slabs_v: SL.t slab_metadata;
  empty_slabs_v: SL.t slab_metadata;
}

let size_class_sl'
  (r: ref size_class_struct)
  (blob: blob)
  : Mem.slprop u#1
  =
  pts_to_sl r full_perm (blob.scs_v) `Mem.star`
  pts_to_sl (blob.scs_v.partial_slabs) full_perm (blob.partial_slabs_v) `Mem.star`
  //SL.ind_llist_sl (p_empty blob.scs_v.size) (blob.scs_v.empty_slabs)
  pts_to_sl (blob.scs_v.empty_slabs) full_perm (blob.empty_slabs_v)

let size_class_sl
  (r: ref size_class_struct)
  =
  Mem.h_exists (size_class_sl' r)

let size_class_sel_full'
  (r: ref size_class_struct)
  : selector' blob (size_class_sl r)
  =
  fun h ->
    let b = Mem.id_elim_exists (size_class_sl' r) h in
    b

let size_class_sl'_witinv (r: ref size_class_struct)
  : Lemma (Mem.is_witness_invariant (size_class_sl' r))
  =
  let aux (b1 b2: blob) (m: Mem.mem)
  : Lemma
  (requires
    Mem.interp (size_class_sl' r b1) m /\
    Mem.interp (size_class_sl' r b2) m
  )
  (ensures b1 == b2)
  =
  pts_to_witinv r full_perm;
  assert (b1.scs_v == b2.scs_v);
  pts_to_witinv (b1.scs_v.partial_slabs) full_perm;
  pts_to_witinv (b1.scs_v.empty_slabs) full_perm
  in
  Classical.forall_intro_3 (Classical.move_requires_3 aux)

let size_class_sel_depends_only_on
  (r: ref size_class_struct)
  (m0:Mem.hmem (size_class_sl r)) (m1:Mem.mem{Mem.disjoint m0 m1})
  : Lemma
  (size_class_sel_full' r m0 == size_class_sel_full' r (Mem.join m0 m1))
  =
  let m' = Mem.join m0 m1 in
  let b1 = reveal (Mem.id_elim_exists (size_class_sl' r) m0) in
  let b2 = reveal (Mem.id_elim_exists (size_class_sl' r) m') in
  size_class_sl'_witinv r;
  Mem.elim_wi (size_class_sl' r) b1 b2 m'

let size_class_sel_depends_only_on_core
  (r: ref size_class_struct)
  (m0:Mem.hmem (size_class_sl r))
  : Lemma
  (size_class_sel_full' r m0 == size_class_sel_full' r (Mem.core_mem m0))
  =
  let b1 = reveal (Mem.id_elim_exists (size_class_sl' r) m0) in
  let b2 = reveal (Mem.id_elim_exists (size_class_sl' r) (Mem.core_mem m0)) in
  size_class_sl'_witinv r;
  Mem.elim_wi (size_class_sl' r) b1 b2 (Mem.core_mem m0)

let size_class_sel (r: ref size_class_struct)
  : selector blob (size_class_sl r)
  =
  Classical.forall_intro_2 (size_class_sel_depends_only_on r);
  Classical.forall_intro (size_class_sel_depends_only_on_core r);
  size_class_sel_full' r

[@@ __steel_reduce__]
let size_class_full' (r: ref size_class_struct) : vprop'
  = {
    hp = size_class_sl r;
    t = blob;
    sel = size_class_sel r;
  }
unfold
let size_class_full (r: ref size_class_struct) = VUnit (size_class_full' r)

[@@ __steel_reduce__]
let v_sc_full (#p: vprop) (r: ref size_class_struct)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (size_class_full r) /\ True)})
  = h (size_class_full r)

let unpack_sc_lemma
  (r: ref size_class_struct)
  (b: blob)
  (m: Mem.mem)
  : Lemma
  (requires
    Mem.interp (size_class_sl r) m /\
    size_class_sel r m == b
  )
  (ensures (
    Mem.interp (
      SR.ptr r `Mem.star`
      SR.ptr (b.scs_v.partial_slabs) `Mem.star`
      SR.ptr (b.scs_v.empty_slabs)
    ) m /\
    sel_of (vptr r) m == b.scs_v /\
    sel_of (vptr b.scs_v.partial_slabs) m == b.partial_slabs_v /\
    sel_of (vptr b.scs_v.empty_slabs) m == b.empty_slabs_v
  ))
  =
  let p1 = pts_to_sl r full_perm b.scs_v in
  let p2 = pts_to_sl (b.scs_v.partial_slabs) full_perm (b.partial_slabs_v) in
  let p3 = pts_to_sl (b.scs_v.empty_slabs) full_perm (b.empty_slabs_v) in
  let sl = p1 `Mem.star` p2 `Mem.star` p3 in
  assert (Mem.interp sl m);

  let m12, m3 = Mem.id_elim_star (p1 `Mem.star` p2) p3 m in
  let m1, m2 = Mem.id_elim_star p1 p2 m12 in
  // #1
  intro_ptr_interp r b.scs_v m1;
  ptr_sel_interp r m1;
  pts_to_witinv r full_perm;
  // #2
  intro_ptr_interp (b.scs_v.partial_slabs) (b.partial_slabs_v) m2;
  ptr_sel_interp (b.scs_v.partial_slabs) m2;
  pts_to_witinv (b.scs_v.partial_slabs) full_perm;
  // #3
  intro_ptr_interp (b.scs_v.empty_slabs) (b.empty_slabs_v) m3;
  ptr_sel_interp (b.scs_v.empty_slabs) m3;
  pts_to_witinv (b.scs_v.empty_slabs) full_perm;
  Mem.intro_star
    (SR.ptr r)
    (SR.ptr (b.scs_v.partial_slabs)) m1 m2;
  assert (reveal m12 == Mem.join m1 m2);
  Mem.intro_star
    (SR.ptr r `Mem.star` SR.ptr (b.scs_v.partial_slabs))
    (SR.ptr (b.scs_v.empty_slabs)) m12 m3;
  assert (m == Mem.join m12 m3);
  //@2
  admit ()


let unpack_sc (r: ref size_class_struct)
  : Steel size_class_struct
  (size_class_full r)
  (fun scs ->
    vptr r `star`
    vptr scs.partial_slabs `star`
    vptr scs.empty_slabs
  )
  (requires fun _ -> True)
  (ensures fun h0 scs h1 ->
    let b = v_sc_full r h0 in
    sel r h1 == scs /\
    True
    //@2 b.scs_v.partial_slabs == sel scs.partial_slabs h1 /\
    //@2 b.scs_v.empty_slabs == sel scs.empty_slabs h1
  )
  =
  let h = get () in
  let b = hide (v_sc_full r h) in
  change_slprop
    (size_class_full r)
    (vptr r `star`
    vptr b.scs_v.partial_slabs `star`
    vptr b.scs_v.empty_slabs)
    b
    ((b.scs_v, b.partial_slabs_v), b.empty_slabs_v)
    (fun m -> unpack_sc_lemma r (reveal b) m);
  let scs = read r in
  change_slprop_rel
    (vptr b.scs_v.partial_slabs)
    (vptr scs.partial_slabs)
    (fun x y -> x == y)
    (fun _ -> ());
  change_slprop_rel
    (vptr b.scs_v.empty_slabs)
    (vptr scs.empty_slabs)
    (fun x y -> x == y)
    (fun _ -> ());
  return scs

let pack_sc_lemma
  (r: ref size_class_struct)
  (b: blob)
  (m: Mem.mem)
  : Lemma
  (requires
    Mem.interp (
      SR.ptr r `Mem.star`
      SR.ptr (b.scs_v.partial_slabs) `Mem.star`
      SR.ptr (b.scs_v.empty_slabs)
    ) m /\
    sel_of (vptr r) m == b.scs_v /\
    sel_of (vptr b.scs_v.partial_slabs) m == b.partial_slabs_v /\
    sel_of (vptr b.scs_v.empty_slabs) m == b.empty_slabs_v
  )
  (ensures (
    Mem.interp (size_class_sl r) m /\
    size_class_sel r m == b
  ))
  =
  admit ()

let pack_sc (#opened:_)
  (r: ref size_class_struct)
  (scs: size_class_struct)
  : SteelGhost unit opened
  (vptr r `star`
  vptr scs.partial_slabs `star`
  vptr scs.empty_slabs)
  (fun _ -> size_class_full r)
  (requires fun h0 -> sel r h0 == scs)
  (ensures fun _ _ _ ->
    //@2
    True)
  =
  let h0 = get () in
  let b : erased blob = hide ({
    scs_v = scs;
    partial_slabs_v = sel scs.partial_slabs h0;
    empty_slabs_v = sel scs.empty_slabs h0;
  }) in
  change_slprop
    (vptr r `star`
    vptr b.scs_v.partial_slabs `star`
    vptr b.scs_v.empty_slabs)
    (size_class_full r)
    ((b.scs_v, b.partial_slabs_v), b.empty_slabs_v)
    b
    (fun m -> pack_sc_lemma r (reveal b) m)

// TODO
// - intermediate step with lemmas in order to have packing/unpacking
// @2- vptr -> llist: which predicate ?

let temp (r1 r2: ref size_class_struct)
  : SteelT U32.t
  (size_class_full r1)
  (fun _ -> size_class_full r1)
  =
  let scs = unpack_sc r1 in
  pack_sc r1 scs;
  return 0ul
