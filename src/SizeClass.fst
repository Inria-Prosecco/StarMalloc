module SizeClass

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module G =  FStar.Ghost

module SL = Selectors.LList

open Steel.FractionalPermission
module Mem = Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SR = Steel.Reference
module A = Steel.Array
module P = Steel.FractionalPermission

open Utils2
open Slabs

//TODO: use ptrdiff
//assume val f (md: slab_metadata) : arr:array U8.t{A.length arr = U32.v page_size}

// Given a size, return a size_class
// TODO: improve max_sc bound
// (requires an improved Steel while loop)


noeq
type size_class_struct = {
  size: sc;
  partial_slabs: ref (SL.t blob);
  empty_slabs: ref (SL.t blob);
  md_count: ref U32.t;
  slab_region: array U8.t;
  //TODO: duplicata due to karamel extraction issue
  md_bm_region: array U64.t;
  md_region: array (SL.cell blob);
  //lock: ref bool;
}

noeq
type blob2 = {
  scs_v: size_class_struct;
  partial_slabs_v: list blob;
  empty_slabs_v: list blob;
  md_count_v: U32.t;
  slab_region_v: Seq.seq U8.t;
  md_bm_region_v: Seq.seq U64.t;
  md_region_v: Seq.seq (SL.cell blob);
}

let size_class_sl'
  (r: ref size_class_struct)
  (scs: size_class_struct)
  : Mem.slprop u#1
  =
  pts_to_sl r full_perm scs `Mem.star`
  SL.ind_llist_sl (p_partial scs.size) (scs.partial_slabs) `Mem.star`
  SL.ind_llist_sl (p_empty scs.size) (scs.empty_slabs) `Mem.star`
  hp_of (A.varray scs.slab_region) `Mem.star`
  hp_of (A.varray scs.md_bm_region) `Mem.star`
  hp_of (A.varray scs.md_region) `Mem.star`
  hp_of (vptr scs.md_count)

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
  assert (scs1 == scs2)
  in
  Classical.forall_intro_3 (Classical.move_requires_3 aux)

let size_class_sel_full'
  (r: ref size_class_struct)
  : selector' blob2 (size_class_sl r)
  =
  fun (h:_) ->
    let scs : size_class_struct = G.reveal (Mem.id_elim_exists (size_class_sl' r) h) in
    assert (Mem.interp (size_class_sl' r scs) h);
    let p1 = pts_to_sl r full_perm scs in
    let p2 = SL.ind_llist_sl (p_partial scs.size) scs.partial_slabs in
    let p3 = SL.ind_llist_sl (p_empty scs.size) scs.empty_slabs in
    let p4 = hp_of (A.varray scs.slab_region) in
    let p5 = hp_of (A.varray scs.md_bm_region) in
    let p6 = hp_of (A.varray scs.md_region) in
    let p7 = SR.ptr scs.md_count in
    let sl =
      p1 `Mem.star` p2 `Mem.star` p3 `Mem.star`
      p4 `Mem.star` p5 `Mem.star` p6 `Mem.star`
      p7 in
    assert (Mem.interp sl h);
    let partial_slabs_v = SL.ind_llist_sel (p_partial scs.size) scs.partial_slabs h in
    let empty_slabs_v = SL.ind_llist_sel (p_empty scs.size) scs.empty_slabs h in
    let slab_region_v = A.varrayp_sel scs.slab_region P.full_perm h in
    let md_bm_region_v = A.varrayp_sel scs.md_bm_region P.full_perm h in
    let md_region_v = A.varrayp_sel scs.md_region P.full_perm h in
    let md_count_v = SR.ptrp_sel scs.md_count P.full_perm h in
    let b = {
      scs_v = G.reveal scs;
      partial_slabs_v = partial_slabs_v;
      empty_slabs_v = empty_slabs_v;
      md_count_v = md_count_v;
      slab_region_v = slab_region_v;
      md_bm_region_v = md_bm_region_v;
      md_region_v = md_region_v;
    } in
    b

let size_class_sel_depends_only_on
  (r: ref size_class_struct)
  (m0:Mem.hmem (size_class_sl r)) (m1:Mem.mem{Mem.disjoint m0 m1})
  : Lemma
  (size_class_sel_full' r m0 == size_class_sel_full' r (Mem.join m0 m1))
  =
  let m' = Mem.join m0 m1 in
  let b1 = G.reveal (Mem.id_elim_exists (size_class_sl' r) m0) in
  let b2 = G.reveal (Mem.id_elim_exists (size_class_sl' r) m') in
  size_class_sl'_witinv r;
  Mem.elim_wi (size_class_sl' r) b1 b2 m'

let size_class_sel_depends_only_on_core
  (r: ref size_class_struct)
  (m0:Mem.hmem (size_class_sl r))
  : Lemma
  (size_class_sel_full' r m0 == size_class_sel_full' r (Mem.core_mem m0))
  =
  let b1 = G.reveal (Mem.id_elim_exists (size_class_sl' r) m0) in
  let b2 = G.reveal (Mem.id_elim_exists (size_class_sl' r) (Mem.core_mem m0)) in
  size_class_sl'_witinv r;
  Mem.elim_wi (size_class_sl' r) b1 b2 (Mem.core_mem m0)

let size_class_sel (r: ref size_class_struct)
  : selector blob2 (size_class_sl r)
  =
  Classical.forall_intro_2 (size_class_sel_depends_only_on r);
  Classical.forall_intro (size_class_sel_depends_only_on_core r);
  size_class_sel_full' r

[@@ __steel_reduce__]
let size_class_full' (r: ref size_class_struct) : vprop'
  = {
    hp = size_class_sl r;
    t = blob2;
    sel = size_class_sel r;
  }
//TODO: FIXME: extracts despite noextract qualifier
unfold
noextract
let size_class_full (r: ref size_class_struct) = VUnit (size_class_full' r)

[@@ __steel_reduce__]
let v_sc_full (#p: vprop) (r: ref size_class_struct)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (size_class_full r) /\ True)})
  = h (size_class_full r)

let unpack_sc_lemma
  (r: ref size_class_struct)
  (b: blob2)
  (m: Mem.mem)
  : Lemma
  (requires
    Mem.interp (size_class_sl r) m /\
    size_class_sel r m == b
  )
  (ensures (
    Mem.interp (
      SR.ptr r `Mem.star`
      SL.ind_llist_sl (p_partial b.scs_v.size) b.scs_v.partial_slabs `Mem.star`
      SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs `Mem.star`
      hp_of (A.varray b.scs_v.slab_region) `Mem.star`
      hp_of (A.varray b.scs_v.md_bm_region) `Mem.star`
      hp_of (A.varray b.scs_v.md_region) `Mem.star`
      hp_of (vptr b.scs_v.md_count)
    ) m /\
    sel_of (vptr r) m == b.scs_v /\
    SL.ind_llist_sel (p_partial b.scs_v.size) b.scs_v.partial_slabs m == b.partial_slabs_v /\
    SL.ind_llist_sel (p_empty b.scs_v.size) b.scs_v.empty_slabs m == b.empty_slabs_v /\
    A.varrayp_sel b.scs_v.slab_region P.full_perm m == b.slab_region_v /\
    A.varrayp_sel b.scs_v.md_bm_region P.full_perm m == b.md_bm_region_v /\
    A.varrayp_sel b.scs_v.md_region P.full_perm m == b.md_region_v /\
    sel_of (vptr b.scs_v.md_count) m == b.md_count_v
  ))
  =
  let p1 = pts_to_sl r full_perm b.scs_v in
  let p2 = SL.ind_llist_sl (p_partial b.scs_v.size) b.scs_v.partial_slabs in
  let p3 = SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs in
  let p4 = hp_of (A.varray b.scs_v.slab_region) in
  let p5 = hp_of (A.varray b.scs_v.md_bm_region) in
  let p6 = hp_of (A.varray b.scs_v.md_region) in
  let p7 = hp_of (vptr b.scs_v.md_count) in
  let sl =
    p1 `Mem.star` p2 `Mem.star` p3 `Mem.star`
    p4 `Mem.star` p5 `Mem.star` p6 `Mem.star`
    p7 in
  assert (Mem.interp sl m);


  let m123456, m7 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star`
    p4 `Mem.star` p5 `Mem.star` p6)
    p7 m in
  let m12345, m6 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4 `Mem.star` p5)
    p6 m123456 in
  let m1234, m5 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4)
    p5 m12345 in
  let m123, m4 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3)
    p4 m1234 in
  let m12, m3 = Mem.id_elim_star
    (p1 `Mem.star` p2)
    p3 m123 in
  let m1, m2 = Mem.id_elim_star p1 p2 m12 in
  // #1
  intro_ptr_interp r b.scs_v m1;
  ptr_sel_interp r m1;
  pts_to_witinv r full_perm;
  // #2-#6: empty
  Mem.intro_star
    (SR.ptr r) p2 m1 m2;
  Mem.intro_star
    (SR.ptr r `Mem.star` p2)
    p3 m12 m3;
  Mem.intro_star
    (SR.ptr r `Mem.star` p2 `Mem.star` p3)
    p4 m123 m4;
  Mem.intro_star
    (SR.ptr r `Mem.star` p2 `Mem.star` p3 `Mem.star` p4)
    p5 m1234 m5;
  Mem.intro_star
    (SR.ptr r `Mem.star` p2 `Mem.star` p3 `Mem.star` p4 `Mem.star` p5)
    p6 m12345 m6;
  Mem.intro_star
    (SR.ptr r `Mem.star` p2 `Mem.star` p3 `Mem.star` p4 `Mem.star` p5 `Mem.star` p6)
    p7 m123456 m7

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 50"
let unpack_sc (r: ref size_class_struct)
  : Steel size_class_struct
  (size_class_full r)
  (fun scs ->
    vptr r `star`
    SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
    SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
    A.varray scs.slab_region `star`
    A.varray scs.md_bm_region `star`
    A.varray scs.md_region `star`
    vptr scs.md_count
  )
  (requires fun _ -> True)
  (ensures fun h0 scs h1 ->
    let b = v_sc_full r h0 in
    sel r h1 == scs /\
    sel r h1 == b.scs_v /\
    SL.v_ind_llist (p_partial scs.size) scs.partial_slabs h1 == b.partial_slabs_v /\
    SL.v_ind_llist (p_empty scs.size) scs.empty_slabs h1 == b.empty_slabs_v /\
    A.asel scs.slab_region h1 == b.slab_region_v /\
    A.asel scs.md_bm_region h1 == b.md_bm_region_v /\
    A.asel scs.md_region h1 == b.md_region_v /\
    sel scs.md_count h1 == b.md_count_v
  )
  =
  let h = get () in
  let b = G.hide (v_sc_full r h) in
  change_slprop
    (size_class_full r)
    (vptr r `star`
    SL.ind_llist (p_partial b.scs_v.size) b.scs_v.partial_slabs `star`
    SL.ind_llist (p_empty b.scs_v.size) b.scs_v.empty_slabs `star`
    A.varray b.scs_v.slab_region `star`
    A.varray b.scs_v.md_bm_region `star`
    A.varray b.scs_v.md_region `star`
    vptr b.scs_v.md_count)
    b
    ((((((b.scs_v,
      b.partial_slabs_v),
      b.empty_slabs_v),
      b.slab_region_v),
      b.md_bm_region_v),
      b.md_region_v),
      b.md_count_v)
    (fun m -> unpack_sc_lemma r (G.reveal b) m);
  let scs = read r in
  change_slprop_rel
    (SL.ind_llist (p_partial b.scs_v.size) b.scs_v.partial_slabs `star`
    SL.ind_llist (p_empty b.scs_v.size) b.scs_v.empty_slabs `star`
    A.varray b.scs_v.slab_region `star`
    A.varray b.scs_v.md_bm_region `star`
    A.varray b.scs_v.md_region `star`
    vptr b.scs_v.md_count)
    (SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
    SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
    A.varray scs.slab_region `star`
    A.varray scs.md_bm_region `star`
    A.varray scs.md_region `star`
    vptr scs.md_count)
    (fun x y -> x == y)
    (fun _ -> ());
  return scs
#pop-options

let pack_sc_lemma
  (r: ref size_class_struct)
  (b: blob2)
  (m: Mem.mem)
  : Lemma
  (requires
    Mem.interp (
      SR.ptr r `Mem.star`
      SL.ind_llist_sl (p_partial b.scs_v.size) b.scs_v.partial_slabs `Mem.star`
      SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs `Mem.star`
      hp_of (A.varray b.scs_v.slab_region) `Mem.star`
      hp_of (A.varray b.scs_v.md_bm_region) `Mem.star`
      hp_of (A.varray b.scs_v.md_region) `Mem.star`
      hp_of (vptr b.scs_v.md_count)
    ) m /\
    sel_of (vptr r) m == b.scs_v /\
    SL.ind_llist_sel (p_partial b.scs_v.size) b.scs_v.partial_slabs m == b.partial_slabs_v /\
    SL.ind_llist_sel (p_empty b.scs_v.size) b.scs_v.empty_slabs m == b.empty_slabs_v /\
    A.varrayp_sel b.scs_v.slab_region P.full_perm m == b.slab_region_v /\
    A.varrayp_sel b.scs_v.md_bm_region P.full_perm m == b.md_bm_region_v /\
    A.varrayp_sel b.scs_v.md_region P.full_perm m == b.md_region_v /\
    sel_of (vptr b.scs_v.md_count) m == b.md_count_v
  )
  (ensures
    Mem.interp (size_class_sl r) m /\
    size_class_sel r m == b
  )
  =
  let p1 = SR.ptr r in
  let p2 = SL.ind_llist_sl (p_partial b.scs_v.size) b.scs_v.partial_slabs in
  let p3 = SL.ind_llist_sl (p_empty b.scs_v.size) b.scs_v.empty_slabs in
  let p4 = hp_of (A.varray b.scs_v.slab_region) in
  let p5 = hp_of (A.varray b.scs_v.md_bm_region) in
  let p6 = hp_of (A.varray b.scs_v.md_region) in
  let p7 = hp_of (vptr b.scs_v.md_count) in
  let sl =
    p1 `Mem.star` p2 `Mem.star` p3 `Mem.star`
    p4 `Mem.star` p5 `Mem.star` p6 `Mem.star`
    p7 in
  assert (Mem.interp sl m);

  let m123456, m7 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4 `Mem.star` p5 `Mem.star` p6)
    p7 m in
  let m12345, m6 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4 `Mem.star` p5)
    p6 m123456 in
  let m1234, m5 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4)
    p5 m12345 in
  let m123, m4 = Mem.id_elim_star
    (p1 `Mem.star` p2 `Mem.star` p3)
    p4 m1234 in
  let m12, m3 = Mem.id_elim_star
    (p1 `Mem.star` p2)
    p3 m123 in
  let m1, m2 = Mem.id_elim_star p1 p2 m12 in
  // #1
  ptr_sel_interp r m1;
  let p1' = pts_to_sl r full_perm b.scs_v in
  // #2-#6: empty
  Mem.intro_star
    p1' p2 m1 m2;
  Mem.intro_star
    (p1' `Mem.star` p2)
    p3 m12 m3;
  Mem.intro_star
    (p1' `Mem.star` p2 `Mem.star` p3)
    p4 m123 m4;
  Mem.intro_star
    (p1' `Mem.star` p2 `Mem.star` p3 `Mem.star` p4)
    p5 m1234 m5;
  Mem.intro_star
    (p1' `Mem.star` p2 `Mem.star` p3 `Mem.star` p4 `Mem.star` p5)
    p6 m12345 m6;
  Mem.intro_star
    (p1' `Mem.star` p2 `Mem.star` p3 `Mem.star` p4 `Mem.star` p5 `Mem.star` p6)
    p7 m123456 m7;
  Mem.intro_h_exists b.scs_v (size_class_sl' r) m;
  size_class_sl'_witinv r

//TODO: FIXME: BLOCKER
//#push-options "--lax"
#push-options "--compat_pre_typed_indexed_effects --z3rlimit 50"
let pack_sc (#opened:_)
  (r: ref size_class_struct)
  (scs: size_class_struct)
  : SteelGhost unit opened
  (vptr r `star`
    SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
    SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
    A.varray scs.slab_region `star`
    A.varray scs.md_bm_region `star`
    A.varray scs.md_region `star`
    vptr scs.md_count)
  (fun _ -> size_class_full r)
  (requires fun h0 -> sel r h0 == scs)
  (ensures fun h0 _ h1 ->
    let b = v_sc_full r h1 in
    b.scs_v == sel r h0 /\
    b.scs_v == scs /\
    b.partial_slabs_v == SL.v_ind_llist (p_partial scs.size) scs.partial_slabs h0 /\
    b.empty_slabs_v == SL.v_ind_llist (p_empty scs.size) scs.empty_slabs h0 /\
    b.slab_region_v == A.asel scs.slab_region h0 /\
    b.md_bm_region_v == A.asel scs.md_bm_region h0 /\
    b.md_region_v == A.asel scs.md_region h0 /\
    b.md_count_v == sel scs.md_count h0
  )
  =
  let h0 = get () in
  assert (scs == sel r h0);
  //let partial_slabs_v : list blob
  //  = G.hide (SL.v_ind_llist (p_partial scs.size) scs.partial_slabs h0) in
  //let empty_slabs_v : list blob
  //  = G.hide (SL.v_ind_llist (p_empty scs.size) scs.empty_slabs h0) in
  //let slab_region_v : Seq.seq U8.t
  //  = G.hide (A.asel scs.slab_region h0) in
  //let md_bm_region_v : Seq.seq U64.t
  //  = G.hide (A.asel scs.md_bm_region h0) in
  //let md_region_v : Seq.seq blob
  //  = G.hide (A.asel scs.md_region h0) in
  ////let m : G.erased ((size_class_struct * list blob) * list blob) =
  //  //G.hide ((scs, G.reveal partial_slabs_v), G.reveal empty_slabs_v) in
  //let b : blob2 = G.hide ({
  //  scs_v = scs;
  //  partial_slabs_v = G.reveal partial_slabs_v;
  //  empty_slabs_v = G.reveal empty_slabs_v;
  //  md_counter_v = U32.v scs.metadata_allocated;
  //  slab_region_v = G.reveal slab_region_v;
  //  md_bm_region_v = G.reveal md_bm_region_v;
  //  md_region_v = G.reveal md_region_v;
  //}) in
  //change_slprop_rel
  //  (SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
  //  SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
  //  A.varray scs.slab_region `star`
  //  A.varray scs.md_bm_region `star`
  //  A.varray scs.md_region)
  //  (SL.ind_llist (p_partial b.scs_v.size) b.scs_v.partial_slabs `star`
  //  SL.ind_llist (p_empty b.scs_v.size) b.scs_v.empty_slabs `star`
  //  A.varray b.scs_v.slab_region `star`
  //  A.varray b.scs_v.md_bm_region `star`
  //  A.varray b.scs_v.md_region)
  //  (fun x y -> x == y)
  //  (fun _ -> ());
  //change_slprop
  //  (vptr r `star`
  //  SL.ind_llist (p_partial b.scs_v.size) b.scs_v.partial_slabs `star`
  //  SL.ind_llist (p_empty b.scs_v.size) b.scs_v.empty_slabs `star`
  //  A.varray b.scs_v.slab_region `star`
  //  A.varray b.scs_v.md_bm_region `star`
  //  A.varray b.scs_v.md_region)
  //  (size_class_full r)
  //  (((((b.scs_v,
  //    b.partial_slabs_v),
  //    b.empty_slabs_v),
  //    b.slab_region_v),
  //    b.md_bm_region_v),
  //    b.md_region_v)
  //  b
  //  (fun m -> admit ())
  //  //(fun m -> pack_sc_lemma r (G.reveal b) m);
  sladmit ();
  admit ()
#pop-options

let temp (r: ref size_class_struct)
  : Steel U32.t
  (size_class_full r)
  (fun _ -> size_class_full r)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    v_sc_full r h0 == v_sc_full r h1
  )
  =
  let scs = unpack_sc r in
  pack_sc r scs;
  return 0ul

let size_class_refinement (b2: blob2)
  =
  Cons? b2.partial_slabs_v \/
  Cons? b2.empty_slabs_v \/
  U32.v b2.md_count_v < U32.v metadata_max

let size_class_vprop (r: ref size_class_struct)
  =
  size_class_full r
  `vrefine`
  (fun b2 -> size_class_refinement b2)

let temp2 (r: ref size_class_struct)
  : Steel U32.t
  (size_class_vprop r)
  (fun _ -> size_class_vprop r)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    h0 (size_class_vprop r)
    ==
    h0 (size_class_vprop r)
  )
  =
  elim_vrefine
    (size_class_full r)
    (fun b2 -> size_class_refinement b2);
  let scs = unpack_sc r in
  pack_sc r scs;
  intro_vrefine
    (size_class_full r)
    (fun b2 -> size_class_refinement b2);
  return 0ul

let allocate_size_class
  (r: ref size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop r)
  (fun result ->
    A.varray result `star`
    size_class_vprop r)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  elim_vrefine
    (size_class_full r)
    (fun b2 -> size_class_refinement b2);
  let scs = unpack_sc r in
  let result = allocate_slab
    scs.size scs.partial_slabs scs.empty_slabs
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count in
  pack_sc r scs;
  let h0 = get () in
  let scs_v = G.hide (v_sc_full r h0) in
  assume (size_class_refinement scs_v);
  intro_vrefine
    (size_class_full r)
    (fun b2 -> size_class_refinement b2);
  return result

(*)
let select_size_class2 (size: U32.t)
  (sc16 sc32 sc64: ref size_class_struct)
  : Steel (ref size_class_struct & G.erased U32.t)
  (size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (fun _ -> size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (requires fun h0 ->
    (v_sc_full sc16 h0).scs_v.size == 16ul /\
    (v_sc_full sc32 h0).scs_v.size == 32ul /\
    (v_sc_full sc64 h0).scs_v.size == 64ul /\
    U32.v size <= max_sc)
  (ensures fun h0 r h1 ->
    U32.lte size (snd r))
  =

  if U32.lte size 16ul then (
    let sc_size = G.hide 16ul in
    return (sc16, sc_size)
  ) else if U32.lte size 32ul then (
    let sc_size = G.hide 32ul in
    return (sc32, sc_size)
  ) else (
    let sc_size = G.hide 64ul in
    return (sc64, sc_size)
  )

let size_classes : list sc = [16ul ; 32ul ; 64ul]

let scl_to_vprop (scl: list (ref size_class_struct))
  : vprop
  = starl (L.map (fun sc -> size_class_full sc) scl)

let f ()
  =
  assert (L.memP 16ul size_classes);
  assert_norm (L.memP 32ul size_classes);
  assert_norm (L.memP 64ul size_classes)


(*)
let rec select_size_class3
  (scl: list (ref size_class_struct))
  (size: U32.t)
  : Steel (ref size_class_struct)
  (scl_to_vprop scl)
  (fun r ->
    size_class_full r `star`
    scl_to_vprop (L.filter (fun r2 -> r2 =!= r) scl)
  )
  (requires fun h0 -> Cons? scl)
  (ensures fun h0 r h1 ->
    not (is_null r)
  )
  =
  let r = L.hd scl in




  admit ();
  return null

let a = 42
(*)

  (fun r ->
    size_class_full r `star`
    SL.ind_llist (fun sc -> size_class_full sc) size_classes)
  (requires fun h0 ->
    Cons? (SL.v_ind_llist (fun sc -> size_class_full sc) size_classes h0))
  (ensures fun h0 r h1 ->

  )



  (size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (fun _ -> size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (requires fun h0 ->
    (v_sc_full sc16 h0).scs_v.size == 16ul /\
    (v_sc_full sc32 h0).scs_v.size == 32ul /\
    (v_sc_full sc64 h0).scs_v.size == 64ul /\
    U32.v size <= max_sc)
  (ensures fun h0 r h1 ->
    U32.lte size (snd r))
  =

  if U32.lte size 16ul then (
    let sc_size = G.hide 16ul in
    return (sc16, sc_size)
  ) else if U32.lte size 32ul then (
    let sc_size = G.hide 32ul in
    return (sc32, sc_size)
  ) else (
    let sc_size = G.hide 64ul in
    return (sc64, sc_size)
  )



(*)
//noextract
//let size_classes : list nzn = [
//  //(* 0 *) 0;
//  (* 16 *) 16; 32; 48; 64; 80; 96; 112; 128;
//  (* 32 *) 160; 192; 224; 256;
//  (* 64 *) 320; 384; 448; 512;
//]
//
//
//noextract
//let size_class_slots : list nzn =
//  L.map nb_of_slots size_classes
//
//let f (_:unit) =
//  let v = L.nth size_class_slots 0 in
//  assert(Some?.v v == 256);
//  ()

let page_size = 4096ul

let nzn = x:U32.t{U32.v x > 0 /\ U32.v x <= U32.v page_size}
let slab = slab:array U8.t{A.length slab == U32.v page_size}

let nb_slots (x: nzn) : nzn = U32.div page_size x

let slab_metadata (size_class: nzn)
  = Seq.lseq bool (U32.v (nb_slots size_class))
