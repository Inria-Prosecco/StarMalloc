module SizeClass2

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module G = FStar.Ghost

module SL = Selectors.LList

module P = Steel.FractionalPermission
module SM = Steel.Memory
module A = Steel.Array

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

open Utils2
open Slabs

//TODO: remove blob, use ptrdiff style
//TODO: improve max_sc bound, use better spec'ed ffs64

open FStar.Mul
noeq
type size_class_struct = {
  size: sc;
  partial_slabs: ref (SL.t blob);
  empty_slabs: ref (SL.t blob);
  md_count: ref U32.t;
  slab_region: slab_region:array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size};
  //TODO: duplicata due to karamel extraction issue
  md_bm_region: md_bm_region:array U64.t{A.length md_bm_region = U32.v metadata_max * 4};
  md_region: md_region:array (SL.cell blob){A.length md_region = U32.v metadata_max};
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

open SteelVRefineDep

let size_class_sl'
  (r: ref size_class_struct)
  (scs: size_class_struct)
  : SM.slprop u#1
  =
  pts_to_sl r P.full_perm scs `SM.star`
  SL.ind_llist_sl (p_partial scs.size) (scs.partial_slabs) `SM.star`
  SL.ind_llist_sl (p_empty scs.size) (scs.empty_slabs) `SM.star`
  vrefinedep_hp
    (vptr scs.md_count)
    //TODO: hideous coercion
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
      A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
      A.varray (A.split_r scs.md_region (u32_to_sz v)))

let size_class_sl
  (r: ref size_class_struct)
  : SM.slprop u#1
  =
  SM.h_exists (size_class_sl' r)


let size_class_sl'_witinv (r: ref size_class_struct)
  : Lemma (SM.is_witness_invariant (size_class_sl' r))
  =
  let aux (scs1 scs2: size_class_struct) (m: SM.mem)
  : Lemma
  (requires
    SM.interp (size_class_sl' r scs1) m /\
    SM.interp (size_class_sl' r scs2) m
  )
  (ensures scs1 == scs2)
  =
  pts_to_witinv r P.full_perm;
  assert (scs1 == scs2)
  in
  Classical.forall_intro_3 (Classical.move_requires_3 aux)

let size_class_sel_full'
  (r: ref size_class_struct)
  : selector' blob2 (size_class_sl r)
  =
  fun (h:_) ->
    let scs : size_class_struct = G.reveal (SM.id_elim_exists (size_class_sl' r) h) in
    assert (SM.interp (size_class_sl' r scs) h);
    let p1 = pts_to_sl r P.full_perm scs in
    let p2 = SL.ind_llist_sl (p_partial scs.size) scs.partial_slabs in
    let p3 = SL.ind_llist_sl (p_empty scs.size) scs.empty_slabs in
    let p4 = vrefinedep_hp
      (vptr scs.md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r scs.md_region (u32_to_sz v))) in
    let sl = p1 `SM.star` p2 `SM.star` p3 `SM.star` p4 in
    assert (SM.interp sl h);
    let partial_slabs_v = SL.ind_llist_sel (p_partial scs.size) scs.partial_slabs h in
    let empty_slabs_v = SL.ind_llist_sel (p_empty scs.size) scs.empty_slabs h in
    let x = vrefinedep_sel
      (vptr scs.md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r scs.md_region (u32_to_sz v))) h in
    let md_count_v = dfst x in
    //let y  ->
    //    A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
    //    A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
    //    A.varray (A.split_r scs.md_region (u32_to_sz v))
    //)
    let y
    : t_of (
        A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
        A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
        A.varray (A.split_r scs.md_region (u32_to_sz md_count_v)))
    = dsnd x in
    let slab_region_v : Seq.seq U8.t = normalize_term ((fun (a, _, _) -> a) y) in
    let md_bm_region_v : Seq.seq U64.t = (fun (_, b, _) -> b) y in
    let md_region_v : Seq.seq (SL.cell blob) = (fun (_, _, c) -> c) y in
    //let (slab_region_v, md_bm_region_v, md_region_v) = y in
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
