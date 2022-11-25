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

#push-options "--ide_id_info_off"

noextract
let is_empty
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : prop
  =
  let max = FStar.Int.max_int U64.n in
  let bound = U32.v (nb_slots size_class) / 64 in
  (U64.v (Seq.index s 0) = 0) /\
  (bound > 1 && (U64.v (Seq.index s 1) = 0)) /\
  (bound > 2 && (U64.v (Seq.index s 2) = 0)) /\
  (bound > 3 && (U64.v (Seq.index s 3) = 0))

// TODO: bad constants
noextract
let has_free_slot
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  let max = FStar.Int.max_int U64.n in
  let bound = U32.v (nb_slots size_class) / 64 in
  (U64.v (Seq.index s 0) < max) ||
  (bound > 1 && (U64.v (Seq.index s 1) <> 0)) ||
  (bound > 2 && (U64.v (Seq.index s 2) <> 0)) ||
  (bound > 3 && (U64.v (Seq.index s 3) <> 0))

noextract
let has_nonfree_slot
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  let bound = U32.v (nb_slots size_class) / 64 in
  (U64.v (Seq.index s 0) > 0) ||
  (bound > 1 && (U64.v (Seq.index s 1) > 0)) ||
  (bound > 2 && (U64.v (Seq.index s 2) > 0)) ||
  (bound > 3 && (U64.v (Seq.index s 3) > 0))

assume val f (md: slab_metadata) : arr:array U8.t{A.length arr = U32.v page_size}

[@@ __reduce__]
//unfold
let p (size_class: sc)
  =
  fun (md: slab_metadata)
  ->
  (A.varray md `star` slab_vprop size_class (f md) md)
//[@@ __reduce__; __steel_reduce__]
//[@@ __steel_reduce__]
//unfold

let p_empty (size_class: sc)
  =
  fun (md: slab_metadata)
  ->
  ((A.varray md `vrefine` (fun s -> is_empty size_class s))
  `star`
  slab_vprop size_class (f md) md)

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
  partial_slabs_v: list slab_metadata;
  empty_slabs_v: list slab_metadata;
}

let size_class_sl'
  (r: ref size_class_struct)
  (scs: size_class_struct)
  : Mem.slprop u#1
  =
  pts_to_sl r full_perm scs `Mem.star`
  SL.ind_llist_sl (p_empty scs.size) (scs.partial_slabs) `Mem.star`
  SL.ind_llist_sl (p_empty scs.size) (scs.empty_slabs)

let size_class_sl
  (r: ref size_class_struct)
  =
  Mem.h_exists (size_class_sl' r)

let size_class_sl'_witinv (r: ref size_class_struct)
  : Lemma (Mem.is_witness_invariant (size_class_sl' r))
  =
  let aux (scs1 scs2: size_class_struct) (m: Mem.mem)
  : Lemma
  (requires
    Mem.interp (size_class_sl' r scs1) m /\
    Mem.interp (size_class_sl' r scs2) m
  )
  (ensures scs1 == scs2)
  =
  pts_to_witinv r full_perm;
  assert (scs1 == scs2);
  pts_to_witinv (scs1.partial_slabs) full_perm;
  pts_to_witinv (scs1.empty_slabs) full_perm
  in
  Classical.forall_intro_3 (Classical.move_requires_3 aux)

let size_class_sel_full'
  (r: ref size_class_struct)
  : selector' blob (size_class_sl r)
  =
  fun (h:_) ->
    let scs : size_class_struct = reveal (Mem.id_elim_exists (size_class_sl' r) h) in
    assert (Mem.interp (size_class_sl' r scs) h);
    let p1 = pts_to_sl r full_perm scs in
    let p2 = SL.ind_llist_sl (p_empty scs.size) scs.partial_slabs in
    let p3 = SL.ind_llist_sl (p_empty scs.size) scs.empty_slabs in
    let sl = p1 `Mem.star` p2 `Mem.star` p3 in
    assert (Mem.interp sl h);
    let partial_slabs_v = SL.ind_llist_sel (p_empty scs.size) scs.partial_slabs h in
    let empty_slabs_v = SL.ind_llist_sel (p_empty scs.size) scs.empty_slabs h in
    let b = {
      scs_v = reveal scs;
      partial_slabs_v = partial_slabs_v;
      empty_slabs_v = empty_slabs_v;
    } in
    b

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
      SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.partial_slabs `Mem.star`
      SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs
    ) m /\
    sel_of (vptr r) m == b.scs_v /\
    SL.ind_llist_sel (p_empty b.scs_v.size) b.scs_v.partial_slabs m == b.partial_slabs_v /\
    SL.ind_llist_sel (p_empty b.scs_v.size) b.scs_v.empty_slabs m == b.empty_slabs_v /\
    True
  ))
  =
  let p1 = pts_to_sl r full_perm b.scs_v in
  let p2 = SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.partial_slabs in
  let p3 = SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs in
  let sl = p1 `Mem.star` p2 `Mem.star` p3 in
  assert (Mem.interp sl m);

  let m12, m3 = Mem.id_elim_star (p1 `Mem.star` p2) p3 m in
  let m1, m2 = Mem.id_elim_star p1 p2 m12 in
  // #1
  intro_ptr_interp r b.scs_v m1;
  ptr_sel_interp r m1;
  pts_to_witinv r full_perm;
  // #2
  // #3
  //
  Mem.intro_star
    (SR.ptr r) p2 m1 m2;
  assert (reveal m12 == Mem.join m1 m2);
  Mem.intro_star
    (SR.ptr r `Mem.star` p2) p3 m12 m3;
  assert (m == Mem.join m12 m3);
  ()

let unpack_sc (r: ref size_class_struct)
  : Steel size_class_struct
  (size_class_full r)
  (fun scs ->
    vptr r `star`
    SL.ind_llist (p_empty scs.size) scs.partial_slabs `star`
    SL.ind_llist (p_empty scs.size) scs.empty_slabs
  )
  (requires fun _ -> True)
  (ensures fun h0 scs h1 ->
    let b = v_sc_full r h0 in
    sel r h1 == scs /\
    sel r h1 == b.scs_v /\
    SL.v_ind_llist (p_empty scs.size) scs.partial_slabs h1 == b.partial_slabs_v /\
    SL.v_ind_llist (p_empty scs.size) scs.empty_slabs h1 == b.empty_slabs_v
  )
  =
  let h = get () in
  let b = hide (v_sc_full r h) in
  change_slprop
    (size_class_full r)
    (vptr r `star`
    SL.ind_llist (p_empty b.scs_v.size) b.scs_v.partial_slabs `star`
    SL.ind_llist (p_empty b.scs_v.size) b.scs_v.empty_slabs)
    b
    ((b.scs_v, b.partial_slabs_v), b.empty_slabs_v)
    (fun m -> unpack_sc_lemma r (reveal b) m);
  let scs = read r in
  change_slprop_rel
    (SL.ind_llist (p_empty b.scs_v.size) b.scs_v.partial_slabs)
    (SL.ind_llist (p_empty scs.size) scs.partial_slabs)
    (fun x y -> x == y)
    (fun _ -> ());
  change_slprop_rel
    (SL.ind_llist (p_empty b.scs_v.size) b.scs_v.empty_slabs)
    (SL.ind_llist (p_empty scs.size) scs.empty_slabs)
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
      SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.partial_slabs `Mem.star`
      SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs
    ) m /\
    sel_of (vptr r) m == b.scs_v /\
    SL.ind_llist_sel (p_empty b.scs_v.size) b.scs_v.partial_slabs m == b.partial_slabs_v /\
    SL.ind_llist_sel (p_empty b.scs_v.size) b.scs_v.empty_slabs m == b.empty_slabs_v
  )
  (ensures
    Mem.interp (size_class_sl r) m /\
    size_class_sel r m == b
  )
  =
  let p1 = SR.ptr r in
  let p2 = SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.partial_slabs in
  let p3 = SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs in
  let sl = p1 `Mem.star` p2 `Mem.star` p3 in
  assert (Mem.interp sl m);

  let m12, m3 = Mem.id_elim_star (p1 `Mem.star` p2) p3 m in
  let m1, m2 = Mem.id_elim_star p1 p2 m12 in
  // #1
  ptr_sel_interp r m1;
  let p1' = pts_to_sl r full_perm b.scs_v in
  // #2
  // #3
  //
  Mem.intro_star p1' p2 m1 m2;
  Mem.intro_star (p1' `Mem.star` p2) p3 m12 m3;
  Mem.intro_h_exists b.scs_v (size_class_sl' r) m;
  size_class_sl'_witinv r

let pack_sc (#opened:_)
  (r: ref size_class_struct)
  (scs: size_class_struct)
  : SteelGhost unit opened
  (vptr r `star`
  SL.ind_llist (p_empty scs.size) scs.partial_slabs `star`
  SL.ind_llist (p_empty scs.size) scs.empty_slabs)
  (fun _ -> size_class_full r)
  (requires fun h0 -> sel r h0 == scs)
  (ensures fun h0 _ h1 ->
    let b = v_sc_full r h1 in
    b.scs_v == sel r h0 /\
    b.scs_v == scs /\
    b.partial_slabs_v == SL.v_ind_llist (p_empty scs.size) scs.partial_slabs h0 /\
    b.empty_slabs_v == SL.v_ind_llist (p_empty scs.size) scs.empty_slabs h0
  )
  =
  let h0 = get () in
  assert (scs == sel r h0);
  let partial_slabs_v : list slab_metadata =
    hide (SL.v_ind_llist (p_empty scs.size) scs.partial_slabs h0) in
  let empty_slabs_v : list slab_metadata =
    hide (SL.v_ind_llist (p_empty scs.size) scs.empty_slabs h0) in
  let m : erased ((size_class_struct * list slab_metadata) * list slab_metadata) =
    hide ((scs, reveal partial_slabs_v), reveal empty_slabs_v) in
  let b : blob = hide ({
    scs_v = scs;
    partial_slabs_v = reveal partial_slabs_v;
    empty_slabs_v = reveal empty_slabs_v;
  }) in
  change_slprop
    (vptr r `star`
    SL.ind_llist (p_empty scs.size) scs.partial_slabs `star`
    SL.ind_llist (p_empty scs.size) scs.empty_slabs)
    (size_class_full r)
    m
    b
    (fun m -> pack_sc_lemma r (reveal b) m);
  ()

let temp (r1 r2: ref size_class_struct)
  : Steel U32.t
  (size_class_full r1)
  (fun _ -> size_class_full r1)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    v_sc_full r1 h0 == v_sc_full r1 h1
  )
  =
  let scs = unpack_sc r1 in
  pack_sc r1 scs;
  return 0ul
