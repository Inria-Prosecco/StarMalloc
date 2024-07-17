module SlabsAlloc2

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module G = FStar.Ghost
module FU = FStar.UInt
module L = FStar.List.Tot

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

module VR2 = SteelVRefine2
module AL = ArrayList
module ALG = ArrayListGen

open Prelude

open Config
open Utils2

open SteelStarSeqUtils
open FStar.Mul
open SlabsCommon2

#restart-solver

#push-options "--z3rlimit 75 --fuel 1 --ifuel 1"
inline_for_extraction noextract
let allocate_slab_aux_cond
  (size_class: sc_ex)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = US.v slab_size})
  : Steel bool
  (slab_vprop size_class arr md)
  (fun _ -> slab_vprop size_class arr md)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let blob0
      : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let blob1
      : t_of (slab_vprop size_class arr md)
      = h1 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq bool 1 = dfst (fst blob0) in
    dfst (fst blob0) == dfst (fst blob1) /\
    dsnd (fst blob0) == dsnd (fst blob1) /\
    blob0 == blob1 /\
    r == is_full (Seq.index v0 0)
  )
  =
  assert (t_of (A.varray md) == Seq.lseq bool 1);
  let md_as_seq : G.erased (Seq.lseq bool 1)
    = elim_slab_vprop size_class arr md in
  let b = A.index md 0sz in
  let r = is_full b in
  intro_slab_vprop size_class arr md md_as_seq;
  return r
#pop-options

//#push-options "--fuel 1 --ifuel 1 --z3rlimit 100 --compat_pre_typed_indexed_effects"
//let slab_region_mon_split
//  (#opened:_)
//  (sc: sc_ex)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_count: US.t{US.v md_count < US.v metadata_max_ex})
//  : SteelGhost unit opened
//  (A.varray (A.split_r slab_region (US.mul md_count slab_size)))
//  (fun _ ->
//    A.varray (slab_array sc slab_region md_count) `star`
//    A.varray (A.split_r slab_region (US.mul (US.add md_count 1sz) slab_size))
//  )
//  (requires fun h0 ->
//    zf_u8 (A.asel (A.split_r slab_region (US.mul md_count slab_size)) h0))
//  (ensures fun h0 _ h1 ->
//    zf_u8 (A.asel (slab_array sc slab_region md_count) h1) /\
//    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.add md_count 1sz) slab_size)) h1)
//  )
//  =
//  let h0 = get () in
//  A.ghost_split
//    (A.split_r slab_region (US.mul md_count slab_size))
//    slab_size;
//  zf_u8_slice
//    (A.asel (A.split_r slab_region (US.mul md_count slab_size)) h0)
//    0
//    (US.v (u32_to_sz page_size));
//  zf_u8_slice
//    (A.asel (A.split_r slab_region (US.mul md_count slab_size)) h0)
//    (US.v slab_size)
//    (A.length (A.split_r slab_region (US.mul md_count slab_size)));
//  pack_slab_array sc slab_region md_count;
//  let x1 = A.split_r (A.split_r slab_region (US.mul md_count slab_size)) slab_size in
//  let x2 = A.split_r slab_region (US.mul (US.add md_count 1sz) slab_size) in
//  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
//  assert (A.length x1 = A.length x2);
//  assert (x1 == x2);
//  change_equal_slprop
//    (A.varray (A.split_r (A.split_r slab_region (US.mul md_count slab_size)) slab_size))
//    (A.varray (A.split_r slab_region (US.mul (US.add md_count 1sz) slab_size)))
//
//let md_bm_region_mon_split
//  (#opened:_)
//  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
//  (md_count: US.t{US.v md_count < US.v metadata_max_ex})
//  : SteelGhost unit opened
//  (A.varray (A.split_r md_bm_region (US.mul md_count 4sz)))
//  (fun _ ->
//    A.varray (md_bm_array md_bm_region md_count) `star`
//    A.varray (A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz))
//  )
//  (requires fun h0 ->
//    zf_u64 (A.asel (A.split_r md_bm_region (US.mul md_count 4sz)) h0))
//  (ensures fun h0 _ h1 ->
//    zf_u64 (A.asel (md_bm_array md_bm_region md_count) h1) /\
//    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz)) h1)
//  )
//  =
//  let h0 = get () in
//  A.ghost_split
//    (A.split_r md_bm_region (US.mul md_count 4sz))
//    4sz;
//  zf_u64_slice (A.asel (A.split_r md_bm_region (US.mul md_count 4sz)) h0) 0 (US.v 4sz);
//  zf_u64_slice (A.asel (A.split_r md_bm_region (US.mul md_count 4sz)) h0) (US.v 4sz) (A.length (A.split_r md_bm_region (US.mul md_count 4sz)));
//  pack_md_bm_array md_bm_region md_count;
//  let x1 = A.split_r (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz in
//  let x2 = A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz) in
//  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
//  assert (A.length x1 = A.length x2);
//  assert (x1 == x2);
//  change_equal_slprop
//    (A.varray (A.split_r (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz))
//    (A.varray (A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz)))
//
//let md_region_mon_split
//  (#opened:_)
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count: US.t{US.v md_count < US.v metadata_max})
//  : SteelGhostT unit opened
//  (A.varray (A.split_r md_region md_count))
//  (fun _ ->
//    A.varray (md_array md_region md_count) `star`
//    A.varray (A.split_r md_region (US.add md_count 1sz))
//  )
//  =
//  A.ghost_split
//    (A.split_r md_region md_count)
//    1sz;
//  pack_md_array md_region md_count;
//  let x1 = A.split_r (A.split_r md_region md_count) 1sz in
//  let x2 = A.split_r md_region (US.add md_count 1sz) in
//  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
//  assert (A.length x1 = A.length x2);
//  assert (x1 == x2);
//  change_equal_slprop
//    (A.varray (A.split_r (A.split_r md_region md_count) 1sz))
//    (A.varray (A.split_r md_region (US.add md_count 1sz)))
//#pop-options

open SteelVRefineDep

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200 --compat_pre_typed_indexed_effects"
// Slab moves from empty to partial
//inline_for_extraction noextract
//let allocate_slab_aux_1_partial
//  (size_class: sc_ex)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1: US.t{US.v idx1 < US.v md_count_v})
//  (idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  : Steel unit
//  (
//    vptr md_count `star`
//    A.varray r_idxs `star`
//    (AL.varraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
//    starseq
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
//      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
//      (SeqUtils.init_us_refined (US.v md_count_v))
//  )
//  (fun _ ->
//    vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//  )
//  (requires fun h0 ->
//    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
//    let idxs0 = A.asel r_idxs h0 in
//    US.v md_count_v <> AL.null /\
//    sel md_count h0 == md_count_v /\
//    Seq.index idxs0 0 == idx1 /\
//    Seq.index idxs0 1 == idx2 /\
//    Seq.index idxs0 2 == idx3 /\
//    Seq.index idxs0 3 == idx4 /\
//    Seq.index idxs0 4 == idx5 /\
//    Seq.index idxs0 5 == idx6 /\
//    Seq.index idxs0 6 == idx7 /\
//    idx1 <> AL.null_ptr /\
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
//  )
//  (ensures fun _ _ h1 ->
//    let blob1
//      = h1 (vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//    ) in
//    md_count_v == dfst blob1)
//  =
//  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
//  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
//  let idx1' = AL.remove1 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) idx1 in
//  AL.insert2 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    idx2 (G.hide (US.v idx1')) (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) idx1 1ul;
//
//  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  A.upd r_idxs 0sz idx1';
//  A.upd r_idxs 1sz idx1;
//  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  assert (G.reveal gs_idxs1
//  == Seq.upd (Seq.upd (G.reveal gs_idxs0) 0 idx1') 1 idx1);
//
//  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idx1') (US.v idx1) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
//  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
//          ALG.ptrs_all #AL.status (US.v idx1') (US.v idx1) (US.v idx3) (US.v idx4) (US.v idx5) gs1);
//
//  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
//    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
//    idx1' idx1 idx3 idx4 idx5 idx6 idx7

// Slab moves from empty to full
inline_for_extraction noextract
let allocate_slab_aux_1_full
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1: US.t{US.v idx1 < US.v md_count_v})
  (idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel unit
  (
    vptr md_count `star`
    A.varray r_idxs `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let idxs0 = A.asel r_idxs h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    Seq.index idxs0 0 == idx1 /\
    Seq.index idxs0 1 == idx2 /\
    Seq.index idxs0 2 == idx3 /\
    Seq.index idxs0 3 == idx4 /\
    Seq.index idxs0 4 == idx5 /\
    Seq.index idxs0 5 == idx6 /\
    Seq.index idxs0 6 == idx7 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
  let idx1' = AL.remove1 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) idx1 in
  AL.insert3 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx3 (G.hide (US.v idx1')) (G.hide (US.v idx2)) (G.hide (US.v  idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) idx1 2ul;

  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  A.upd r_idxs 0sz idx1';
  A.upd r_idxs 2sz idx1;
  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  assert (G.reveal gs_idxs1
  == Seq.upd (Seq.upd (G.reveal gs_idxs0) 0 idx1') 2 idx1);

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1') (US.v idx2) (US.v idx1) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1') (US.v idx2) (US.v idx1) (US.v idx4) (US.v idx5) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
    idx1' idx2 idx1 idx4 idx5 idx6 idx7

#restart-solver

// Slab initially empty
inline_for_extraction noextract
let allocate_slab_aux_1
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    A.varray r_idxs `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun r ->
    A.varray r `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let idxs0 = A.asel r_idxs h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    Seq.index idxs0 0 == idx1 /\
    Seq.index idxs0 1 == idx2 /\
    Seq.index idxs0 2 == idx3 /\
    Seq.index idxs0 3 == idx4 /\
    Seq.index idxs0 4 == idx5 /\
    Seq.index idxs0 5 == idx6 /\
    Seq.index idxs0 6 == idx7 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun _ r h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
    ) in
    md_count_v == dfst blob1 /\
    A.length r == U32.v size_class /\
    same_base_array r slab_region /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region) >= 0 /\
    True
    //((A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region)) % U32.v page_size) % (U32.v size_class) == 0
  )
  =
  (**) ALG.lemma_head1_in_bounds pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7);
  (**) starseq_unpack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx1);

  (**) ALG.lemma_head1_implies_pred1 pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4 idx5 idx6 idx7;

  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in

  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v idx1);
  (**) SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx1);
  (**) change_equal_slprop
     (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx1)))
     (p_empty size_class (md_bm_array md_bm_region idx1, slab_array slab_region idx1));

  (**) p_empty_unpack size_class
     (md_bm_array md_bm_region idx1, slab_array slab_region idx1)
     (md_bm_array md_bm_region idx1, slab_array slab_region idx1);
  let r = allocate_slot size_class
    (slab_array slab_region idx1)
    (md_bm_array md_bm_region idx1)
  in
  (**) pack_slab_starseq size_class
    slab_region md_bm_region md_region md_count
    md_count_v md_region_lv idx1 2ul;
  allocate_slab_aux_1_full size_class
    slab_region md_bm_region md_region md_count r_idxs
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
  return r

#restart-solver

//// Slab moves from partial to full
//inline_for_extraction noextract
//let allocate_slab_aux_2_full
//  (size_class: sc_ex)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1: US.t)
//  (idx2: US.t{US.v idx2 < US.v md_count_v})
//  (idx3 idx4 idx5 idx6 idx7: US.t)
//  : Steel unit
//  (
//    vptr md_count `star`
//    A.varray r_idxs `star`
//    (AL.varraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
//    starseq
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
//      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
//      (SeqUtils.init_us_refined (US.v md_count_v))
//  )
//  (fun _ ->
//    vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//  )
//  (requires fun h0 ->
//    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
//   let idxs0 = A.asel r_idxs h0 in
//    US.v md_count_v <> AL.null /\
//    sel md_count h0 == md_count_v /\
//    Seq.index idxs0 0 == idx1 /\
//    Seq.index idxs0 1 == idx2 /\
//    Seq.index idxs0 2 == idx3 /\
//    Seq.index idxs0 3 == idx4 /\
//    Seq.index idxs0 4 == idx5 /\
//    Seq.index idxs0 5 == idx6 /\
//    Seq.index idxs0 6 == idx7 /\
//    idx2 <> AL.null_ptr /\
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
//  )
//  (ensures fun _ _ h1 ->
//    let blob1
//      = h1 (vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//    ) in
//    md_count_v == dfst blob1)
//  =
//  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
//  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
//  let idx2' = AL.remove2 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    (G.hide (US.v idx1)) idx2 (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) idx2 in
//  AL.insert3 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    idx3 (G.hide (US.v idx1)) (G.hide (US.v idx2')) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) idx2 2ul;
//
//  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  A.upd r_idxs 1sz idx2';
//  A.upd r_idxs 2sz idx2;
//  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  assert (G.reveal gs_idxs1
//  == Seq.upd (Seq.upd (G.reveal gs_idxs0) 1 idx2') 2 idx2);
//
//  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idx1) (US.v idx2') (US.v idx2) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
//  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
//          ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2') (US.v idx2) (US.v idx4) (US.v idx5) gs1);
//
//  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
//    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
//    idx1 idx2' idx2 idx4 idx5 idx6 idx7
//
//#restart-solver
//
//#restart-solver
//
//// Slab moves from partial to partial
//inline_for_extraction noextract
//let allocate_slab_aux_2_partial
//  (size_class: sc_ex)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1: US.t)
//  (idx2: US.t{US.v idx2 < US.v md_count_v})
//  (idx3 idx4 idx5 idx6 idx7: US.t)
//  : Steel unit
//  (
//    vptr md_count `star`
//    A.varray r_idxs `star`
//    (AL.varraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
//    starseq
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
//      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
//      (SeqUtils.init_us_refined (US.v md_count_v))
//  )
//  (fun _ ->
//    vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//  )
//  (requires fun h0 ->
//    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
//    let idxs0 = A.asel r_idxs h0 in
//    US.v md_count_v <> AL.null /\
//    sel md_count h0 == md_count_v /\
//    Seq.index idxs0 0 == idx1 /\
//    Seq.index idxs0 1 == idx2 /\
//    Seq.index idxs0 2 == idx3 /\
//    Seq.index idxs0 3 == idx4 /\
//    Seq.index idxs0 4 == idx5 /\
//    Seq.index idxs0 5 == idx6 /\
//    Seq.index idxs0 6 == idx7 /\
//    idx2 <> AL.null_ptr /\
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
//  )
//  (ensures fun _ _ h1 ->
//    let blob1
//      = h1 (vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//    ) in
//    md_count_v == dfst blob1)
//  =
//  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
//    md_count_v md_region_lv
//    idx1 idx2 idx3 idx4 idx5 idx6 idx7
//
//#restart-solver
//
//#restart-solver

//#push-options "--fuel 1 --ifuel 1 --compat_pre_typed_indexed_effects --z3rlimit 300"
//inline_for_extraction noextract
//let allocate_slab_aux_2_aux
//  (size_class: sc_ex)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1: US.t)
//  (idx2: US.t{US.v idx2 < US.v md_count_v})
//  (idx3 idx4 idx5 idx6 idx7: US.t)
//  : Steel unit
//  (
//    slab_vprop size_class
//      (slab_array slab_region idx2)
//      (md_bm_array md_bm_region idx2) `star`
//    (vptr md_count `star`
//    A.varray r_idxs `star`
//    (AL.varraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
//    starseq
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v md_region_lv)
//      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v idx2)) `star`
//    starseq
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v md_region_lv)
//      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx2 + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
//  )
//  (fun _ ->
//    vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//  )
//  (requires fun h0 ->
//    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
//    let idxs0 = A.asel r_idxs h0 in
//    let blob0
//      : t_of (slab_vprop size_class
//        (slab_array slab_region idx2)
//        (md_bm_array md_bm_region idx2))
//      = h0 (slab_vprop size_class
//        (slab_array slab_region idx2)
//        (md_bm_array md_bm_region idx2)) in
//    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
//    not (is_empty size_class v0) /\
//    US.v md_count_v <> AL.null /\
//    sel md_count h0 == md_count_v /\
//    Seq.index idxs0 0 == idx1 /\
//    Seq.index idxs0 1 == idx2 /\
//    Seq.index idxs0 2 == idx3 /\
//    Seq.index idxs0 3 == idx4 /\
//    Seq.index idxs0 4 == idx5 /\
//    Seq.index idxs0 5 == idx6 /\
//    Seq.index idxs0 6 == idx7 /\
//    idx2 <> AL.null_ptr /\
//    G.reveal md_region_lv `Seq.equal` Seq.upd (G.reveal md_region_lv) (US.v idx2) 1ul /\
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
//  )
//  (ensures fun _ r h1 ->
//    let blob1
//      = h1 (vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//    ) in
//    md_count_v == dfst blob1
//  )
//  =

//// Slab initially partial
//inline_for_extraction noextract
//let allocate_slab_aux_2
//  (size_class: sc_ex)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  : Steel (array U8.t)
//  (
//    vptr md_count `star`
//    A.varray r_idxs `star`
//    (AL.varraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
//    starseq
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v md_region_lv)
//      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//      (SeqUtils.init_us_refined (US.v md_count_v))
//  )
//  (fun r ->
//    A.varray r `star`
//    vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//  )
//  (requires fun h0 ->
//    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
//    let idxs0 = A.asel r_idxs h0 in
//    US.v md_count_v <> AL.null /\
//    sel md_count h0 == md_count_v /\
//    Seq.index idxs0 0 == idx1 /\
//    Seq.index idxs0 1 == idx2 /\
//    Seq.index idxs0 2 == idx3 /\
//    Seq.index idxs0 3 == idx4 /\
//    Seq.index idxs0 4 == idx5 /\
//    Seq.index idxs0 5 == idx6 /\
//    Seq.index idxs0 6 == idx7 /\
//    idx2 <> AL.null_ptr /\
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
//  )
//  (ensures fun _ r h1 ->
//    let blob1
//      = h1 (vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//    ) in
//    md_count_v == dfst blob1 /\
//    A.length r == U32.v size_class /\
//    same_base_array r slab_region /\
//    A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region) >= 0 /\
//    True
//    //((A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region)) % U32.v page_size) % (U32.v size_class) == 0
//  )
//  =
//  (**) ALG.lemma_head2_in_bounds pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7);
//  (**) starseq_unpack_s
//    #_
//    #(pos:US.t{US.v pos < US.v md_count_v})
//    #(t size_class)
//    (f size_class slab_region md_bm_region md_count_v md_region_lv)
//    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//    (SeqUtils.init_us_refined (US.v md_count_v))
//    (US.v idx2);
//
//  (**) ALG.lemma_head2_implies_pred2 pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
//
//  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
//
//  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v idx2);
//  (**) SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx2);
//  (**) change_equal_slprop
//     (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx2)))
//     (p_partial size_class (md_bm_array md_bm_region idx2, slab_array slab_region idx2));
//  (**) p_partial_unpack size_class
//     (md_bm_array md_bm_region idx2, slab_array slab_region idx2)
//     (md_bm_array md_bm_region idx2, slab_array slab_region idx2);
//
//  let r = allocate_slot size_class
//    (md_bm_array md_bm_region idx2)
//    (slab_array slab_region idx2)
//  in
//  (**) pack_slab_starseq size_class
//    slab_region md_bm_region md_region md_count
//    md_count_v md_region_lv idx2 2ul;
//  allocate_slab_aux_2_full size_class
//    slab_region md_bm_region md_region md_count r_idxs
//    md_count_v md_region_lv;
//  return r
//#pop-options

#restart-solver

let alloc_metadata_sl1
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: G.erased (v:US.t{US.v v < US.v metadata_max}))
  (md_count_v0: US.t{US.v md_count_v0 < US.v metadata_max})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (US.mul (G.reveal md_count_v) (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul (G.reveal md_count_v) 4sz)) `star`
      A.varray (A.split_r md_region (G.reveal md_count_v)))
    ) m /\
    G.reveal md_count_v == md_count_v0
  )
  (ensures
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (US.mul md_count_v0 (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul md_count_v0 4sz)) `star`
      A.varray (A.split_r md_region md_count_v0))
    ) m /\
    sel_of
      (A.varray (A.split_r slab_region (US.mul (G.reveal md_count_v) (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul (G.reveal md_count_v) 4sz)) `star`
      A.varray (A.split_r md_region (G.reveal md_count_v)))
      m
    ==
    sel_of
      (A.varray (A.split_r slab_region (US.mul md_count_v0 (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul md_count_v0 4sz)) `star`
      A.varray (A.split_r md_region md_count_v0))
      m
  )
  =
  ()

let alloc_metadata_sl2
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: G.erased (v:US.t{US.v v < US.v metadata_max}))
  (md_count_v0: US.t{US.v md_count_v0 < US.v metadata_max})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (US.mul (US.add md_count_v0 1sz) (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul (US.add md_count_v0 1sz) 4sz)) `star`
      A.varray (A.split_r md_region (US.add md_count_v0 1sz)))
    ) m /\
    G.reveal md_count_v == md_count_v0
  )
  (ensures
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (US.mul (US.add (G.reveal md_count_v) 1sz) (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul (US.add (G.reveal md_count_v) 1sz) 4sz)) `star`
      A.varray (A.split_r md_region (US.add (G.reveal md_count_v) 1sz)))
    ) m /\
    sel_of
      (A.varray (A.split_r slab_region (US.mul (US.add md_count_v0 1sz) (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul (US.add md_count_v0 1sz) 4sz)) `star`
      A.varray (A.split_r md_region (US.add md_count_v0 1sz)))
      m
    ==
    sel_of
      (A.varray (A.split_r slab_region (US.mul (US.add (G.reveal md_count_v) 1sz) (u32_to_sz page_size))) `star`
      A.varray (A.split_r md_bm_region (US.mul (US.add (G.reveal md_count_v) 1sz) 4sz)) `star`
      A.varray (A.split_r md_region (US.add (G.reveal md_count_v) 1sz)))
      m
  )
  =
  ()

#restart-solver

let right_vprop_sl_lemma1
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (v: US.t{US.v v + 1 <= US.v metadata_max_ex})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    right_vprop slab_region md_bm_region md_region v
  )) m)
  (ensures SM.interp (hp_of (
    (A.varray (A.split_r slab_region (US.mul v slab_size))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region v)
      `vrefine` zf_b) `star`
    A.varray (A.split_r md_region v)
  )) m /\
  sel_of (
    (A.varray (A.split_r slab_region (US.mul v slab_size))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region v)
      `vrefine` zf_b) `star`
    A.varray (A.split_r md_region v)
  ) m
  ==
  sel_of (right_vprop slab_region md_bm_region md_region v) m
  )
  = ()

let right_vprop_sl_lemma2
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (v: US.t{US.v v <= US.v metadata_max_ex})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    (A.varray (A.split_r slab_region (US.mul v slab_size))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region v)
      `vrefine` zf_b) `star`
    A.varray (A.split_r md_region v)
  )) m)
  (ensures SM.interp (hp_of (
    right_vprop slab_region md_bm_region md_region v
  )) m /\
  sel_of (
    (A.varray (A.split_r slab_region (US.mul v slab_size))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region v)
      `vrefine` zf_b) `star`
    A.varray (A.split_r md_region v)
  ) m
  ==
  sel_of (right_vprop slab_region md_bm_region md_region v) m
  )
  = ()

#restart-solver

// Extension function, auxiliar
inline_for_extraction noextract
let allocate_slab_aux_3_1_varraylist
  (#opened: _)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : SteelGhost unit opened
  (
    AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) `star`
    A.varray (A.split_l (A.split_r md_region md_count_v) 1sz)
  )
  (fun _ ->
    AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7))
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    //US.v md_count_v <> AL.null /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5))
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h1 in
    Seq.length gs1 == US.v md_count_v + US.v 1sz /\
    Seq.slice gs1 0 (US.v md_count_v) == gs0 /\
    ALG.partition #AL.status (Seq.slice gs1 0 (US.v md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    ~ (ALG.mem_all #AL.status (US.v md_count_v + 0)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs1)
  )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  AL.extend_aux 1sz
    md_region
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)
    md_count_v
    0ul;
  let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region (md_count_v `US.add` 1sz))
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (Seq.slice gs1 0 (US.v md_count_v)) `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0)


#restart-solver

let split_r_r (#opened:_) (#a: Type)
  (k1: US.t)
  (k2: US.t{US.fits (US.v k1 + US.v k2)})
  (arr: array a{US.v (US.add k1 k2) <= A.length arr})
  : SteelGhost unit opened
  (A.varray (
    A.split_r (A.split_r arr k1) k2
  ))
  (fun _ -> A.varray (
    A.split_r arr (US.add k1 k2)
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel (A.split_r (A.split_r arr k1) k2) h0
    ==
    A.asel (A.split_r arr (US.add k1 k2)) h1
  )
  =
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_r (A.split_r arr k1) k2))
    (A.ptr_of (A.split_r arr (US.add k1 k2)));
  change_equal_slprop
    (A.varray (A.split_r (A.split_r arr k1) k2))
    (A.varray (A.split_r arr (US.add k1 k2)))

let split_r_r_mul (#opened:_) (#a: Type)
  (k1: US.t)
  (k2: US.t{US.fits (US.v k1 + US.v k2)})
  (n: US.t{US.fits (US.v n * (US.v k1 + US.v k2))})
  (arr: array a{US.v (US.mul (US.add k1 k2) n) <= A.length arr})
  : SteelGhost unit opened
  (A.varray (
    A.split_r (A.split_r arr (US.mul k1 n)) (US.mul k2 n)
  ))
  (fun _ -> A.varray (
    A.split_r arr (US.mul (US.add k1 k2) n)
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel (A.split_r (A.split_r arr (US.mul k1 n)) (US.mul k2 n)) h0
    ==
    A.asel (A.split_r arr (US.mul (US.add k1 k2) n)) h1
  )
  =
  split_r_r (US.mul k1 n) (US.mul k2 n) arr;
  change_equal_slprop
    (A.varray (A.split_r arr (US.add (US.mul k1 n) (US.mul k2 n))))
    (A.varray (A.split_r arr (US.mul (US.add k1 k2) n)))

// Extension function, auxiliar
#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects --query_stats --fuel 1 --ifuel 1"
let allocate_slab_aux_3_1_right_aux
  (#opened: _)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  : SteelGhost unit opened
  (
    A.varray (A.split_r slab_region (US.mul md_count_v slab_size)) `star`
    A.varray (A.split_r md_bm_region md_count_v) `star`
    A.varray (A.split_r md_region md_count_v)
  )
  (fun _ ->
    ((A.varray (A.split_r slab_region
      (US.mul (US.add md_count_v 1sz) slab_size))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region
      (US.add md_count_v 1sz))
      `vrefine` zf_b) `star`
    A.varray (A.split_r md_region
      (US.add md_count_v 1sz))) `star`
    A.varray (A.split_l
      (A.split_r slab_region (US.mul md_count_v slab_size))
        slab_size) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region md_count_v)
      1sz) `star`
    A.varray (A.split_l
      (A.split_r md_region md_count_v)
      1sz)
  )
  (requires fun h0 ->
    zf_u8 (A.asel
      (A.split_r slab_region (US.mul md_count_v slab_size))
      h0
    ) /\
    zf_b (A.asel
      (A.split_r md_bm_region md_count_v)
      h0
    )
  )
  (ensures fun _ _ h1 ->
    zf_b (A.asel
      (A.split_l (A.split_r md_bm_region md_count_v) 1sz) h1)
  )
  =
  let slab_region0 = gget (A.varray (A.split_r slab_region (US.mul md_count_v slab_size))) in
  let md_bm_region0 = gget (A.varray (A.split_r md_bm_region md_count_v)) in
  zf_u8_split slab_region0 (US.v slab_size);
  zf_b_split md_bm_region0 (US.v 1sz);
  A.ghost_split
    (A.split_r slab_region (US.mul md_count_v slab_size))
    slab_size;
  change_equal_slprop
    (A.varray (A.split_r (A.split_r slab_region (US.mul md_count_v slab_size))
      slab_size))
    (A.varray (A.split_r (A.split_r slab_region (US.mul md_count_v slab_size))
      (US.mul 1sz slab_size)));
  A.ghost_split
    (A.split_r md_bm_region md_count_v)
    1sz;
  A.ghost_split
    (A.split_r md_region md_count_v)
    1sz;
  split_r_r_mul md_count_v 1sz slab_size slab_region;
  split_r_r md_count_v 1sz md_bm_region;
  split_r_r md_count_v 1sz md_region;
  intro_vrefine
    (A.varray (A.split_r slab_region
      (US.mul (US.add md_count_v 1sz) slab_size)))
    zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region
      (US.add md_count_v 1sz)))
    zf_b

let allocate_slab_aux_3_1_right
  (#opened: _)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  : SteelGhost unit opened
  (
    right_vprop slab_region md_bm_region md_region md_count_v
  )
  (fun _ ->
    right_vprop slab_region md_bm_region md_region (md_count_v `US.add` 1sz) `star`
    A.varray (A.split_l
      (A.split_r slab_region (US.mul md_count_v slab_size))
      slab_size) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region md_count_v)
      1sz) `star`
    A.varray (A.split_l
      (A.split_r md_region md_count_v)
      1sz)
  )
  (requires fun _ -> True)
  (ensures fun _ _ h1 ->
    zf_b (A.asel
      (A.split_l
        (A.split_r md_bm_region md_count_v)
        1sz) h1)
  )
  =
  change_slprop_rel
    (right_vprop slab_region md_bm_region md_region md_count_v)
    ((A.varray (A.split_r slab_region (US.mul md_count_v slab_size))
     `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region md_count_v)
     `vrefine` zf_b) `star`
    A.varray (A.split_r md_region md_count_v))
    (fun x y -> x == y)
    (fun m -> right_vprop_sl_lemma1 slab_region md_bm_region md_region md_count_v m);
  elim_vrefine
    (A.varray (A.split_r slab_region (US.mul md_count_v slab_size)))
    zf_u8;
  elim_vrefine
    (A.varray (A.split_r md_bm_region md_count_v))
    zf_b;
  allocate_slab_aux_3_1_right_aux
    slab_region md_bm_region md_region md_count_v;
  change_slprop_rel
    ((A.varray (A.split_r slab_region (US.mul (US.add md_count_v 1sz) slab_size))
     `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.add md_count_v 1sz))
     `vrefine` zf_b) `star`
    A.varray (A.split_r md_region (US.add md_count_v 1sz)))
    (right_vprop slab_region md_bm_region md_region (US.add md_count_v 1sz))
    (fun x y -> x == y)
    (fun m -> right_vprop_sl_lemma2 slab_region md_bm_region md_region (US.add md_count_v 1sz) m)

// Extension function, is SteelGhost
inline_for_extraction noextract
let allocate_slab_aux_3_1
  (#opened: _)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : SteelGhost unit opened
  (
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7))
  )
  (fun _ ->
    right_vprop slab_region md_bm_region md_region (md_count_v `US.add` 1sz) `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    A.varray (A.split_l
      (A.split_r slab_region (US.mul md_count_v slab_size))
      slab_size) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region md_count_v)
      1sz)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h1 in
    Seq.length gs1 == US.v md_count_v + 1 /\
    Seq.slice gs1 0 (US.v md_count_v) == gs0 /\
    ALG.partition #AL.status (Seq.slice gs1 0 (US.v md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    (~ (ALG.mem_all #AL.status (US.v md_count_v + 0) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs1)) /\
    zf_b (A.asel (A.split_l (A.split_r md_bm_region md_count_v) 1sz) h1)
  )
  =
  allocate_slab_aux_3_1_right
    slab_region md_bm_region md_region md_count_v;
  allocate_slab_aux_3_1_varraylist
    md_region md_count_v idx1 idx2 idx3 idx4 idx5 idx6 idx7;
  let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7))
  in
  ()

#restart-solver

module FS = FStar.FiniteSet.Base

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let allocate_slab_aux_3_2_seq_equality
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (s1 s2: Seq.lseq AL.cell (US.v md_count_v + 1))
  : Lemma
  (requires
    ALG.dataify s2 == Seq.upd (ALG.dataify s1) (US.v md_count_v) 0ul
  )
  (ensures
    ALG.dataify s2
    == Seq.append
      (Seq.slice (ALG.dataify s1) 0 (US.v md_count_v))
      (Seq.create 1 0ul)
  )
  =
  Seq.lemma_split (ALG.dataify s1) (US.v md_count_v);
  Seq.lemma_split (ALG.dataify s2) (US.v md_count_v);
  Seq.lemma_eq_intro
    (Seq.slice (ALG.dataify s2) 0 (US.v md_count_v))
    (Seq.slice (ALG.dataify s1) 0 (US.v md_count_v));
  Seq.lemma_eq_intro
    (Seq.slice (ALG.dataify s2) (US.v md_count_v) (US.v md_count_v + 1))
    (Seq.create 1 0ul)

let fs_subset_elim
  (pred: nat -> bool)
  (s1 s2: FS.set nat)
  : Lemma
  (requires
    FS.subset s1 s2 /\
    (forall (i:nat{pred i}). FS.mem i s1)
  )
  (ensures
    (forall (i:nat{pred i}). FS.mem i s2)
  )
  = ()

let allocate_slab_aux_3_2_list_partition
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (s1 s2: Seq.lseq AL.cell (US.v md_count_v + 1))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Lemma
  (requires
    ALG.is_dlist pred1 (US.v idx1) s1 /\
    ALG.is_dlist pred2 (US.v idx2) s1 /\
    ALG.is_dlist pred3 (US.v idx3) s1 /\
    ALG.is_dlist pred4 (US.v idx4) s1 /\
    ALG.is_dlist pred5 (US.v idx5) s1 /\
    ALG.partition (Seq.slice s1 0 (US.v md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    (~ (ALG.mem_all #AL.status (US.v md_count_v) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) s1)) /\
    // s2 wrt s1
    ALG.ptrs_in (US.v md_count_v) s2
    == FS.insert
      (US.v md_count_v)
      (ALG.ptrs_in (US.v idx1) s1) /\
    ALG.ptrs_in (US.v idx2) s2
    == ALG.ptrs_in (US.v idx2) s1 /\
    ALG.ptrs_in (US.v idx3) s2
    == ALG.ptrs_in (US.v idx3) s1 /\
    ALG.ptrs_in (US.v idx4) s2
    == ALG.ptrs_in (US.v idx4) s1 /\
    ALG.ptrs_in (US.v idx5) s2
    == ALG.ptrs_in (US.v idx5) s1
  )
  (ensures
    ALG.partition s2
      (US.v md_count_v)
      (US.v idx2)
      (US.v idx3)
      (US.v idx4)
      (US.v idx5)
  )
  =
  ALG.lemma_extend_dlist_subset_slice_all
    pred1 pred2 pred3 pred4 pred5
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)
    s1
    (US.v md_count_v);
  let s1' = Seq.slice s1 0 (US.v md_count_v) in
  let ps1' = ALG.ptrs_all (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) s1' in
  let ps1 = ALG.ptrs_all (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) s1 in
  let ps2 = ALG.ptrs_all (US.v md_count_v) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) s1 in
  assert (FS.subset ps1' ps1);
  assert (forall (i:nat{i < US.v md_count_v}).
    FS.mem i ps1
  );
  assume (FS.subset ps1 ps2);
  fs_subset_elim (fun i -> i < US.v md_count_v) ps1 ps2;
  assert (FS.mem (US.v md_count_v) (ALG.ptrs_in (US.v md_count_v) s2));
  assume (FS.mem (US.v md_count_v) ps2);
  assert (forall (i:nat{i < US.v md_count_v + 1}).
    FS.mem i ps2
  );
  admit ();
  ()

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
// Insertion function
inline_for_extraction noextract
let allocate_slab_aux_3_2
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel unit
  (
    AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idx5) (US.v idx6) (US.v idx7)
  )
  (fun _ ->
    AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v md_count_v)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idx5) (US.v idx6) (US.v idx7)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    ALG.partition #AL.status (Seq.slice gs0 0 (US.v md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    (~ (ALG.mem_all #AL.status (US.v md_count_v) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0))
  )
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v md_count_v)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idx5) (US.v idx6) (US.v idx7) h1 in
    ALG.dataify gs1
    == Seq.append
      (Seq.slice (ALG.dataify gs0) 0 (US.v md_count_v))
      (Seq.create 1 0ul) /\
    ALG.partition #AL.status gs1
      (US.v md_count_v) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  assert (~ (ALG.mem_all #AL.status (US.v md_count_v) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0));
  AL.insert1
    (A.split_l md_region (md_count_v `US.add` 1sz))
    idx1 (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)
    md_count_v
    0ul;
  let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v md_count_v) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  allocate_slab_aux_3_2_seq_equality md_count_v gs0 gs1;
  allocate_slab_aux_3_2_list_partition md_count_v gs0 gs1
    idx1 idx2 idx3 idx4 idx5 idx6 idx7
#pop-options

let lemma_slab_aux_3_3_1
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : Lemma
    (let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
     let f2 = f size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul)) in
     let s1 = SeqUtils.init_us_refined (US.v md_count_v) in
     let s2 = Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz))) 0 (US.v md_count_v) in
     forall (k:nat{k < Seq.length s1}). f1 (Seq.index s1 k) == f2 (Seq.index s2 k))
  =
  let md_region_lv' = Seq.append md_region_lv (Seq.create 1 0ul) in
  let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
  let f2 = f size_class slab_region md_bm_region (US.add md_count_v 1sz) md_region_lv' in
  let s1 = SeqUtils.init_us_refined (US.v md_count_v) in
  let s2 = Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz))) 0 (US.v md_count_v) in

  let aux (k:nat{k < Seq.length s1}) : Lemma (f1 (Seq.index s1 k) == f2 (Seq.index s2 k))
    = SeqUtils.init_us_refined_index (US.v md_count_v) k;
      SeqUtils.init_us_refined_index (US.v (US.add md_count_v 1sz)) k
  in Classical.forall_intro aux

#restart-solver

let allocate_slab_aux_3_3_1 (#opened:_)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : SteelGhost unit opened
  (
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz))) 0 (US.v md_count_v))
  )
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  lemma_slab_aux_3_3_1 size_class slab_region md_bm_region md_region md_count_v md_region_lv;

  starseq_weakening_ref
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz))) 0 (US.v md_count_v))

let split_l_l (#opened:_) (#a: Type)
  (k1: US.t)
  (k2: US.t{US.v k1 <= US.v k2})
  (arr: array a{US.v k2 <= A.length arr})
  : SteelGhost unit opened
  (A.varray (
    A.split_l (A.split_l arr k2) k1
  ))
  (fun _ -> A.varray (
    A.split_l arr k1
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel (A.split_l (A.split_l arr k2) k1) h0
    ==
    A.asel (A.split_l arr k1) h1
  )
  =
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_l (A.split_l arr k2) k1))
    (A.ptr_of (A.split_l arr k1));
  change_equal_slprop
    (A.varray (A.split_l (A.split_l arr k2) k1))
    (A.varray (A.split_l arr k1))

let split_l_l_mul (#opened:_) (#a: Type)
  (k1: US.t)
  (k2: US.t{US.v k1 <= US.v k2})
  (n: US.t{US.fits (US.v k2 * US.v n)})
  (arr: array a{US.v k2 * US.v n <= A.length arr})
  : SteelGhost unit opened
  (A.varray (
    A.split_l (A.split_l arr (US.mul k2 n)) (US.mul k1 n)
  ))
  (fun _ -> A.varray (
    A.split_l arr (US.mul k1 n)
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel (A.split_l (A.split_l arr (US.mul k2 n)) (US.mul k1 n)) h0
    ==
    A.asel (A.split_l arr (US.mul k1 n)) h1
  )
  =
  split_l_l (US.mul k1 n) (US.mul k2 n) arr

//let allocate_slab_aux_3_3_2_1_aux2 (#opened:_)
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (i: US.t{0 < US.v i /\ US.v i < US.v guard_pages_interval})
//  : SteelGhost unit opened
//  (
//    A.varray (A.split_r (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul i (u32_to_sz page_size)))
//        (US.mul (US.sub i 1sz) (u32_to_sz page_size))) `star`
//    A.varray (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul i 4sz))
//        (US.mul (US.sub i 1sz) 4sz))
//  )
//  (fun _ ->
//    starseq
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v md_count_v + US.v i - 1)
//        (US.v md_count_v + US.v i)
//      )
//  )
//  (requires fun h0 ->
//    zf_u64 (A.asel (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul i 4sz))
//        (US.mul (US.sub i 1sz) 4sz)) h0)
//  )
//  (ensures fun _ _ _ -> True)
//  =
//  A.ptr_base_offset_inj
//    (A.ptr_of (A.split_r (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul i (u32_to_sz page_size)))
//        (US.mul (US.sub i 1sz) (u32_to_sz page_size))))
//    (A.ptr_of (slab_array slab_region (US.add md_count_v (US.sub i 1sz))));
//  A.ptr_base_offset_inj
//    (A.ptr_of (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul i 4sz))
//        (US.mul (US.sub i 1sz) 4sz)))
//    (A.ptr_of (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz))));
//  change_equal_slprop
//    (A.varray (A.split_r (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul i (u32_to_sz page_size)))
//        (US.mul (US.sub i 1sz) (u32_to_sz page_size))))
//    (A.varray (slab_array slab_region (US.add md_count_v (US.sub i 1sz))));
//  change_equal_slprop
//    (A.varray (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul i 4sz))
//        (US.mul (US.sub i 1sz) 4sz)))
//    (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz))));
//
//  let md_as_seq = gget (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)))) in
//  assert (G.reveal md_as_seq == Seq.create 4 0UL);
//  slab_to_slots size_class (slab_array slab_region (US.add md_count_v (US.sub i 1sz)));
//  empty_md_is_properly_zeroed size_class;
//  intro_slab_vprop size_class
//    (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)))
//    (Seq.create 4 0UL)
//    (slab_array slab_region (US.add md_count_v (US.sub i 1sz)));
//  p_empty_pack size_class
//    (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)),
//    slab_array slab_region (US.add md_count_v (US.sub i 1sz)))
//    (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)),
//    slab_array slab_region (US.add md_count_v (US.sub i 1sz)));
//  SeqUtils.init_us_refined_index
//    (US.v (US.add md_count_v guard_pages_interval))
//    (US.v (US.add md_count_v (US.sub i 1sz)));
//  change_equal_slprop
//    (p_empty size_class
//      (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)),
//      slab_array slab_region (US.add md_count_v (US.sub i 1sz))))
//    (f size_class slab_region md_bm_region
//      (US.add md_count_v guard_pages_interval)
//      (Seq.append md_region_lv (Seq.append
//        (Seq.create (US.v guard_pages_interval - 1) 0ul)
//        (Seq.create 1 3ul)))
//      (Seq.index (SeqUtils.init_us_refined
//        (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v (US.add md_count_v (US.sub i 1sz)))));
//  starseq_intro_singleton
//    #_
//    #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//    #(t size_class)
//    (f size_class slab_region md_bm_region
//      (US.add md_count_v guard_pages_interval)
//      (Seq.append md_region_lv (Seq.append
//        (Seq.create (US.v guard_pages_interval - 1) 0ul)
//        (Seq.create 1 3ul))))
//    (f_lemma size_class slab_region md_bm_region
//      (US.add md_count_v guard_pages_interval)
//      (Seq.append md_region_lv (Seq.append
//        (Seq.create (US.v guard_pages_interval - 1) 0ul)
//        (Seq.create 1 3ul))))
//    (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//    (US.v (US.add md_count_v (US.sub i 1sz)))
//    (US.v md_count_v + US.v i - 1)
//    (US.v md_count_v + US.v i)
//
//let rec allocate_slab_aux_3_3_2_1_aux (#opened:_)
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (i: US.t{US.v i < US.v guard_pages_interval})
//  : SteelGhost unit opened
//  (
//    A.varray (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul i (u32_to_sz page_size))) `star`
//    A.varray (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul i 4sz))
//  )
//  (fun _ ->
//    starseq
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v md_count_v)
//        (US.v md_count_v + US.v i)
//      )
//  )
//  (requires fun h0 ->
//    zf_u64 (A.asel (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//      (US.mul i 4sz)) h0)
//  )
//  (ensures fun _ _ _ -> True)
//  (decreases US.v i)
//  =
//  match US.v i with
//  | 0 ->
//    // 2 arrays of length 0
//    //TODO: add corresponding builtin (at least in lib_misc)
//    drop (A.varray (A.split_l
//           (A.split_r slab_region
//             (US.mul md_count_v (u32_to_sz page_size)))
//             (US.mul i (u32_to_sz page_size))));
//    drop (A.varray (A.split_l
//            (A.split_r md_bm_region
//              (US.mul md_count_v 4sz))
//              (US.mul i 4sz)));
//    starseq_intro_empty
//      #_
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v md_count_v)
//        (US.v md_count_v + US.v i))
//  | _ ->
//    A.ghost_split (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul i (u32_to_sz page_size)))
//      (US.mul (US.sub i 1sz) (u32_to_sz page_size));
//    let s0 = gget (A.varray (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul i 4sz))) in
//    zf_u64_split s0 (US.v (US.mul (US.sub i 1sz) 4sz));
//    A.ghost_split (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul i 4sz))
//      (US.mul (US.sub i 1sz) 4sz);
//    split_l_l_mul
//      (US.sub i 1sz)
//      i
//      (u32_to_sz page_size)
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)));
//    split_l_l_mul
//      (US.sub i 1sz)
//      i
//      4sz
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz));
//    allocate_slab_aux_3_3_2_1_aux size_class
//      slab_region md_bm_region md_region
//      md_count_v md_region_lv
//      (US.sub i 1sz);
//    //dedicated lemma
//    allocate_slab_aux_3_3_2_1_aux2 size_class
//      slab_region md_bm_region md_region
//      md_count_v md_region_lv
//      i;
//    change_equal_slprop
//      (starseq
//        #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//        #(t size_class)
//        (f size_class slab_region md_bm_region
//          (US.add md_count_v guard_pages_interval)
//          (Seq.append md_region_lv (Seq.append
//            (Seq.create (US.v guard_pages_interval - 1) 0ul)
//            (Seq.create 1 3ul))))
//        (f_lemma size_class slab_region md_bm_region
//          (US.add md_count_v guard_pages_interval)
//          (Seq.append md_region_lv (Seq.append
//            (Seq.create (US.v guard_pages_interval - 1) 0ul)
//            (Seq.create 1 3ul))))
//        (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//          (US.v md_count_v)
//          (US.v md_count_v + US.v (US.sub i 1sz))
//        ))
//      (starseq
//        #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//        #(t size_class)
//        (f size_class slab_region md_bm_region
//          (US.add md_count_v guard_pages_interval)
//          (Seq.append md_region_lv (Seq.append
//            (Seq.create (US.v guard_pages_interval - 1) 0ul)
//            (Seq.create 1 3ul))))
//        (f_lemma size_class slab_region md_bm_region
//          (US.add md_count_v guard_pages_interval)
//          (Seq.append md_region_lv (Seq.append
//            (Seq.create (US.v guard_pages_interval - 1) 0ul)
//            (Seq.create 1 3ul))))
//        (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//          (US.v md_count_v)
//          (US.v md_count_v + US.v i - 1))
//      );
//    starseq_append_s
//      #_
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//      (US.v md_count_v)
//      (US.v md_count_v + US.v i - 1)
//      (US.v md_count_v + US.v i)
//

//let allocate_slab_aux_3_3_2_1 (#opened:_)
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  : SteelGhost unit opened
//  (
//    A.varray (A.split_l (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul guard_pages_interval (u32_to_sz page_size)))
//      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))) `star`
//    A.varray (A.split_l (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul guard_pages_interval 4sz))
//      (US.mul (US.sub guard_pages_interval 1sz) 4sz))
//  )
//  (fun _ ->
//    starseq
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v md_count_v)
//        (US.v md_count_v + US.v guard_pages_interval - 1)
//      )
//  )
//  (requires fun h0 ->
//    zf_u64 (A.asel (A.split_l (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul guard_pages_interval 4sz))
//      (US.mul (US.sub guard_pages_interval 1sz) 4sz)) h0)
//  )
//  (ensures fun _ _ _ -> True)
//  =
//  split_l_l_mul
//    (US.sub guard_pages_interval 1sz)
//    guard_pages_interval
//    (u32_to_sz page_size)
//    (A.split_r slab_region
//      (US.mul md_count_v (u32_to_sz page_size)));
//  split_l_l_mul
//    (US.sub guard_pages_interval 1sz)
//    guard_pages_interval
//    4sz
//    (A.split_r md_bm_region
//      (US.mul md_count_v 4sz));
//  allocate_slab_aux_3_3_2_1_aux size_class
//    slab_region md_bm_region md_region
//    md_count_v md_region_lv
//    (US.sub guard_pages_interval 1sz);
//  change_slprop_rel
//    (starseq
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v md_count_v)
//        (US.v md_count_v + US.v (US.sub guard_pages_interval 1sz))))
//    (starseq
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v md_count_v)
//        (US.v md_count_v + US.v guard_pages_interval - 1)))
//    (fun x y -> x == y)
//    (fun _ -> assert_norm (
//      US.v (US.sub guard_pages_interval 1sz)
//      ==
//      US.v guard_pages_interval - 1
//    ))
//
//open Guards
//
//let allocate_slab_aux_3_3_2_2
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  : Steel unit
//  (
//    A.varray (A.split_r (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul guard_pages_interval (u32_to_sz page_size)))
//      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))) `star`
//    A.varray (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul guard_pages_interval 4sz))
//      (US.mul (US.sub guard_pages_interval 1sz) 4sz))
//  )
//  (fun _ ->
//    starseq
//      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//      #(t size_class)
//      (f size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (f_lemma size_class slab_region md_bm_region
//        (US.add md_count_v guard_pages_interval)
//        (Seq.append md_region_lv (Seq.append
//          (Seq.create (US.v guard_pages_interval - 1) 0ul)
//          (Seq.create 1 3ul))))
//      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v md_count_v + US.v guard_pages_interval - 1)
//        (US.v md_count_v + US.v guard_pages_interval)
//      )
//  )
//  (requires fun h0 ->
//    zf_u64 (A.asel (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul guard_pages_interval 4sz))
//      (US.mul (US.sub guard_pages_interval 1sz) 4sz)) h0))
//  (ensures fun h0 _ h1 -> True)
//  =
//  //normalization
//  A.ptr_base_offset_inj
//    (A.ptr_of (A.split_r (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul guard_pages_interval (u32_to_sz page_size)))
//      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))))
//    (A.ptr_of (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
//  change_equal_slprop
//    (A.varray(A.split_r (A.split_l
//      (A.split_r slab_region
//        (US.mul md_count_v (u32_to_sz page_size)))
//        (US.mul guard_pages_interval (u32_to_sz page_size)))
//      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))))
//    (A.varray (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
//  A.ptr_base_offset_inj
//    (A.ptr_of (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul guard_pages_interval 4sz))
//      (US.mul (US.sub guard_pages_interval 1sz) 4sz)))
//    (A.ptr_of (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
//  change_equal_slprop
//    (A.varray (A.split_r (A.split_l
//      (A.split_r md_bm_region
//        (US.mul md_count_v 4sz))
//        (US.mul guard_pages_interval 4sz))
//      (US.mul (US.sub guard_pages_interval 1sz) 4sz)))
//    (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
//  let md_as_seq = gget (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)))) in
//  assert (G.reveal md_as_seq == Seq.create 4 0UL);
//  slab_to_slots size_class (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)));
//  empty_md_is_properly_zeroed size_class;
//  intro_empty_slab_varray size_class
//    (Seq.create 4 0UL)
//    (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)));
//  mmap_trap_guard
//    (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)))
//    (u32_to_sz page_size);
//  p_guard_pack size_class
//    (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)),
//    slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)));
//  SeqUtils.init_us_refined_index
//    (US.v (US.add md_count_v guard_pages_interval))
//    (US.v (US.add md_count_v (US.sub guard_pages_interval 1sz)));
//  change_equal_slprop
//    (p_guard size_class
//      (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)),
//      slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz))))
//    (f size_class slab_region md_bm_region
//      (US.add md_count_v guard_pages_interval)
//      (Seq.append md_region_lv (Seq.append
//        (Seq.create (US.v guard_pages_interval - 1) 0ul)
//        (Seq.create 1 3ul)))
//      (Seq.index (SeqUtils.init_us_refined
//        (US.v (US.add md_count_v guard_pages_interval)))
//        (US.v (US.add md_count_v (US.sub guard_pages_interval 1sz)))));
//  starseq_intro_singleton
//    #_
//    #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
//    #(t size_class)
//    (f size_class slab_region md_bm_region
//      (US.add md_count_v guard_pages_interval)
//      (Seq.append md_region_lv (Seq.append
//        (Seq.create (US.v guard_pages_interval - 1) 0ul)
//        (Seq.create 1 3ul))))
//    (f_lemma size_class slab_region md_bm_region
//      (US.add md_count_v guard_pages_interval)
//      (Seq.append md_region_lv (Seq.append
//        (Seq.create (US.v guard_pages_interval - 1) 0ul)
//        (Seq.create 1 3ul))))
//    (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
//    (US.v (US.add md_count_v (US.sub guard_pages_interval 1sz)))
//    (US.v md_count_v + US.v guard_pages_interval - 1)
//    (US.v md_count_v + US.v guard_pages_interval)
//#pop-options

let allocate_slab_aux_3_3_2
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : Steel unit
  (
    A.varray (A.split_l
      (A.split_r slab_region (US.mul md_count_v slab_size))
      slab_size) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region md_count_v)
      1sz)
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz)))
        (US.v md_count_v)
        (US.v md_count_v + 1)
      )
  )
  (requires fun h0 ->
    zf_b (A.asel (A.split_l
      (A.split_r md_bm_region md_count_v)
      1sz) h0)
  )
  (ensures fun _ _ _ -> True)
  =
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_l
      (A.split_r slab_region (US.mul md_count_v slab_size))
      slab_size))
    (A.ptr_of (slab_array slab_region md_count_v));
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_l
      (A.split_r md_bm_region md_count_v)
      1sz))
    (A.ptr_of (md_bm_array md_bm_region md_count_v));
  change_equal_slprop
    (A.varray (A.split_l
      (A.split_r slab_region (US.mul md_count_v slab_size))
      slab_size))
    (A.varray (slab_array slab_region md_count_v));
  change_equal_slprop
    (A.varray (A.split_l
      (A.split_r md_bm_region md_count_v)
      1sz))
    (A.varray (md_bm_array md_bm_region md_count_v));
  let s
    : G.erased (Seq.lseq bool 1)
    = gget (A.varray (md_bm_array md_bm_region md_count_v)) in
  intro_slab_vprop_empty size_class
    (slab_array slab_region md_count_v)
    (md_bm_array md_bm_region md_count_v);
  p_empty_pack size_class
    (md_bm_array md_bm_region md_count_v,
    slab_array slab_region md_count_v)
    (md_bm_array md_bm_region md_count_v,
    slab_array slab_region md_count_v);
  SeqUtils.init_us_refined_index
    (US.v (US.add md_count_v 1sz))
    (US.v md_count_v);
  change_equal_slprop
    (p_empty size_class
      (md_bm_array md_bm_region md_count_v,
      slab_array slab_region md_count_v))
    (f size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul))
      (Seq.index (SeqUtils.init_us_refined
        (US.v (US.add md_count_v 1sz)))
        (US.v md_count_v)));
  starseq_intro_singleton
    #_
    #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
    #(t size_class)
    (f size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (f_lemma size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz)))
    (US.v md_count_v)
    (US.v md_count_v)
    (US.v md_count_v + 1)

let allocate_slab_aux_3_3
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : Steel unit
  (
    A.varray (A.split_l
      (A.split_r slab_region (US.mul md_count_v slab_size))
        slab_size) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region md_count_v)
        1sz) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz)))
  )
  (requires fun h0 ->
    zf_b (A.asel (A.split_l
      (A.split_r md_bm_region md_count_v)
        1sz) h0)
  )
  (ensures fun _ _ _ -> True)
  =
  allocate_slab_aux_3_3_1 size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv;
  allocate_slab_aux_3_3_2 size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv;
  starseq_append_s
    #_
    #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
    #(t size_class)
    (f size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (f_lemma size_class slab_region md_bm_region
      (US.add md_count_v 1sz)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (SeqUtils.init_us_refined
      (US.v (US.add md_count_v 1sz)))
    0
    (US.v md_count_v)
    (US.v md_count_v + 1);
  change_equal_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (Seq.slice (SeqUtils.init_us_refined
        (US.v (US.add md_count_v 1sz)))
        0 (US.v md_count_v + 1)))
    (starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (SeqUtils.init_us_refined
        (US.v (US.add md_count_v 1sz))))

#restart-solver

#push-options "--z3rlimit 100"
//inline_for_extraction noextract
let allocate_slab_aux_3
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v + 1 <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel unit//US.t
  (
    vptr md_count `star`
    A.varray r_idxs `star`
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vptr md_count `star`
    A.varray r_idxs `star`
    right_vprop slab_region md_bm_region md_region (US.add md_count_v 1sz) `star`
    AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v md_count_v)
      (US.v idx2)
      (US.v idx3)
      (US.v idx4)
      (US.v idx5)
      (US.v idx6)
      (US.v idx7) `star`
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v 1sz)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz)))
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    US.v md_count_v <> AL.null /\
    md_count_v == sel md_count h0 /\
    US.v md_count_v < US.v metadata_max_ex /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1 ) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region (md_count_v `US.add` 1sz))
      (US.v md_count_v)
      (US.v idx2)
      (US.v idx3)
      (US.v idx4)
      (US.v idx5)
      (US.v idx6)
      (US.v idx7) h1 in
    let idxs0 = A.asel r_idxs h0 in
    let idxs1 = A.asel r_idxs h1 in
    Seq.index idxs1 0 == md_count_v /\
    Seq.index idxs1 1 == Seq.index idxs0 1 /\
    Seq.index idxs1 2 == Seq.index idxs0 2 /\
    Seq.index idxs1 3 == Seq.index idxs0 3 /\
    Seq.index idxs1 4 == Seq.index idxs0 4 /\
    Seq.index idxs1 5 == Seq.index idxs0 5 /\
    Seq.index idxs1 6 == Seq.index idxs0 6 /\
    sel md_count h0 = md_count_v /\
    sel md_count h1 = US.add md_count_v 1sz /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.dataify gs1
    == Seq.append
      (G.reveal md_region_lv)
      (Seq.create 1 0ul) /\
    ALG.partition #AL.status gs1
      (US.v md_count_v)
      (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    True
  )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  allocate_slab_aux_3_1
    slab_region md_bm_region md_region md_count_v
    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
  let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region (md_count_v `US.add` 1sz))
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  ALG.lemma_dataify_slice #AL.status gs1 (US.v md_count_v);
  allocate_slab_aux_3_2
    md_region md_count_v
    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
  allocate_slab_aux_3_3 size_class
    slab_region md_bm_region md_region md_count_v md_region_lv;
  let v = read md_count in
  write md_count (US.add v 1sz);

  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  A.upd r_idxs 0sz md_count_v;
  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in

  return ()
#pop-options

module P = Steel.FractionalPermission

#restart-solver

//type bounded_pair' = US.t & US.t
//let bounded_pair (up: US.t) = s:bounded_pair'{US.v (fst s) < US.v up /\ US.v (snd s) < US.v up}

type bounded_tuple' : Type0
  = {x: US.t; y: US.t; z: US.t; w: US.t}
let bounded_tuple (up: US.t) = s:bounded_tuple'{
  US.v s.x < US.v up
  //US.v s.y < US.v up /\
  //US.v s.z < US.v up
  //US.v s.w < US.v up
}

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100 --query_stats --compat_pre_typed_indexed_effects"
let allocate_slab_aux_4_aux1
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel (bounded_tuple md_count_v)
  (
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7))
  )
  (fun idxs ->
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idxs.x)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idxs.y)
      (US.v idxs.z)
      (US.v idxs.w)
    )
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    //US.v md_count_v <> AL.null /\
    idx7 <> 0sz /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun h0 idxs h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idxs.x)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idxs.y)
      (US.v idxs.z)
      (US.v idxs.w) h1 in
    //US.v md_count_v <> AL.null /\
    idxs.x <> AL.null_ptr /\
    Seq.index md_region_lv (US.v idxs.x) = 4ul /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.dataify gs1 `Seq.equal` (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul) /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    ALG.partition #AL.status gs1 (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y)
  )
  =
  ALG.lemma_size5_not_null_implies_bounds pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) idx7;
  assert (US.v idx6 < US.v md_count_v);
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  ALG.lemma_tail5_implies_pred5 pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
  ALG.lemma_dataify_index #AL.status gs0 (US.v idx6);
  assert (Seq.index (ALG.dataify #AL.status gs0) (US.v idx6) = 4ul);
  lemma_partition_and_pred_implies_mem5
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
    (US.v idx5) (US.v idx6) (US.v idx7)
    gs0 (US.v idx6);
  assert (ALG.mem #AL.status (US.v idx6) (US.v idx5) gs0);

  let idxs : ALG.tuple3
    = AL.dequeue #pred1 #pred2 #pred3 #pred4 #pred5
      (A.split_l md_region md_count_v)
      idx5 idx6 idx7
      (G.hide (US.v idx1)) (G.hide (US.v idx2)) (G.hide (US.v idx3)) (G.hide (US.v idx4)) in

  AL.insert1 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idxs.x)) (G.hide (US.v idxs.y)) (G.hide (US.v idxs.z)) idx6 0ul;
  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx6) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.x) (US.v idxs.y) (US.v idxs.z)) in
  assert (ALG.dataify #AL.status gs1 `Seq.equal` Seq.upd (ALG.dataify #AL.status gs0) (US.v idx6) 0ul);
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx6) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.x) gs1);

  let r = {x = idx6; y = idxs.x; z = idxs.y; w = idxs.z} in
  change_slprop_rel
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx6)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idxs.x) (US.v idxs.y) (US.v idxs.z))
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v r.x)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v r.y) (US.v r.z) (US.v r.w))
    (fun x y -> x == y)
    (fun m -> ALG.varraylist_to_varraylist_lemma #AL.status
      #pred1 #pred2 #pred3 #pred4 #pred5
      (A.split_l md_region md_count_v)
      (US.v idx6)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idxs.x) (US.v idxs.y) (US.v idxs.z)
      (US.v r.x)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v r.y) (US.v r.z) (US.v r.w)
      m
    );
  return r

let allocate_slab_aux_4_aux2
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (idxs: bounded_tuple md_count_v)
  : Steel unit
  (
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    US.v idxs.x < US.v md_count_v /\
    Seq.index (G.reveal md_region_lv) (US.v idxs.x) == 4ul
  )
  (ensures fun _ _ _ -> True)
  =
  (**) starseq_unpack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idxs.x);
  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idxs.x);
  (**) change_equal_slprop
    (f size_class slab_region md_bm_region md_count_v md_region_lv
      (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idxs.x)))
    (p_quarantine size_class (md_bm_array md_bm_region idxs.x, slab_array slab_region idxs.x));
  p_quarantine_unpack size_class (md_bm_array md_bm_region idxs.x, slab_array slab_region idxs.x);
  Quarantine2.mmap_untrap_quarantine
    size_class
    (A.split_l (slab_array slab_region idxs.x) (u32_to_sz size_class))
    (u32_to_sz size_class);
  let md = gget (A.varray (md_bm_array md_bm_region idxs.x)) in
  assert (is_empty (Seq.index md 0));
  assert (md `Seq.equal` Seq.create 1 false);
  rewrite_slprop
    (A.varray (A.split_l (slab_array slab_region idxs.x) (u32_to_sz size_class)))
    (slab_vprop_aux size_class
              (A.split_l (slab_array slab_region idxs.x) (u32_to_sz size_class))
              (Seq.index (Seq.create 1 false) 0))
    (fun _ -> admit ());
  intro_slab_vprop size_class
    (slab_array slab_region idxs.x)
    (md_bm_array md_bm_region idxs.x)
    (Seq.create 1 false);
  pack_slab_starseq size_class
    slab_region md_bm_region md_region md_count
    md_count_v md_region_lv
    idxs.x 0ul

//inline_for_extraction noextract
val allocate_slab_aux_4
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  //(r_ringbuffer: A.array US.t{A.length r_ringbuffer == US.v max_size})
  //(r_in r_out r_size: ref US.t)
  //: Steel (bounded md_count_v & bounded md_count_v)
  //: Steel (US.t & US.t)
  : Steel (bounded_tuple md_count_v)
  (
    vptr md_count `star`
    A.varray r_idxs `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun idxs ->
    vptr md_count `star`
    A.varray r_idxs `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idxs.x)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idxs.y)
      (US.v idxs.z)
      (US.v idxs.w)
    ) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let idxs0 = A.asel r_idxs h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    Seq.index idxs0 0 == idx1 /\
    Seq.index idxs0 1 == idx2 /\
    Seq.index idxs0 2 == idx3 /\
    Seq.index idxs0 3 == idx4 /\
    Seq.index idxs0 4 == idx5 /\
    Seq.index idxs0 5 == idx6 /\
    Seq.index idxs0 6 == idx7 /\
    idx7 <> 0sz /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun h0 idxs h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idxs.x)
      (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idxs.y)
      (US.v idxs.z)
      (US.v idxs.w) h1 in
    let idxs0 = A.asel r_idxs h0 in
    let idxs1 = A.asel r_idxs h1 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel md_count h1 == md_count_v /\
    idxs.x <> AL.null_ptr /\
    Seq.index idxs0 0 == idx1 /\
    Seq.index idxs0 1 == idx2 /\
    Seq.index idxs0 2 == idx3 /\
    Seq.index idxs0 3 == idx4 /\
    Seq.index idxs0 4 == idx5 /\
    Seq.index idxs0 5 == idx6 /\
    Seq.index idxs0 6 == idx7 /\
    Seq.index idxs1 0 == idxs.x /\
    Seq.index idxs1 1 == idx2 /\
    Seq.index idxs1 2 == idx3 /\
    Seq.index idxs1 3 == idx4 /\
    Seq.index idxs1 4 == idxs.y /\
    Seq.index idxs1 5 == idxs.z /\
    Seq.index idxs1 6 == idxs.w /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.dataify gs1 `Seq.equal` (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul) /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    ALG.partition #AL.status gs1 (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y)
  )

#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects"
let allocate_slab_aux_4
  size_class
  slab_region
  md_bm_region
  md_region
  md_count
  r_idxs
  md_count_v
  md_region_lv
  idx1 idx2 idx3 idx4 idx5 idx6 idx7
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
 let r = allocate_slab_aux_4_aux1 size_class
    slab_region md_bm_region md_region md_count r_idxs
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5 idx6 idx7 in
  allocate_slab_aux_4_aux2 size_class
    slab_region md_bm_region md_region md_count r_idxs
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5 idx6 idx7 r;

  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  A.upd r_idxs 0sz r.x;
  A.upd r_idxs 4sz r.y;
  A.upd r_idxs 5sz r.z;
  A.upd r_idxs 6sz r.w;
  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in

  return r

#restart-solver

inline_for_extraction noextract
let allocate_slab'
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    A.varray r_idxs `star`
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let idxs0 = A.asel r_idxs h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    Seq.index idxs0 0 == idx1 /\
    Seq.index idxs0 1 == idx2 /\
    Seq.index idxs0 2 == idx3 /\
    Seq.index idxs0 3 == idx4 /\
    Seq.index idxs0 4 == idx5 /\
    Seq.index idxs0 5 == idx6 /\
    Seq.index idxs0 6 == idx7 /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv
  )
  (ensures fun _ r _ ->
    not (A.is_null r) ==> (
      A.length r == U32.v size_class /\
      same_base_array r slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region) >= 0 /\
      //((A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region)) % U32.v page_size) % (U32.v size_class) == 0
      True
    )
  )
  =
  if (idx1 <> AL.null_ptr) then (
    ALG.lemma_head1_in_bounds pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7);
    // Lemma above used to derive
    assert (US.v md_count_v <> AL.null);
    // TODO!
    let r = allocate_slab_aux_1 size_class
      slab_region md_bm_region md_region md_count r_idxs
      md_count_v md_region_lv
      idx1 idx2 idx3 idx4 idx5 idx6 idx7 in
    pack_right_and_refactor_vrefine_dep
      size_class slab_region md_bm_region md_region md_count
      r_idxs md_count_v;
    A.varrayp_not_null r P.full_perm;
    change_equal_slprop
      (A.varray r)
      (if (A.is_null r) then emp else A.varray r);
    return r
  ) else (
    let b = US.gte idx7 quarantine_queue_threshold in
    if enable_quarantine && b then (
      let idxs = allocate_slab_aux_4 size_class
        slab_region md_bm_region md_region md_count r_idxs
        md_count_v md_region_lv
        idx1 idx2 idx3 idx4 idx5 idx6 idx7 in
      let r = allocate_slab_aux_1 size_class
        slab_region md_bm_region md_region md_count r_idxs
        md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul))
        idxs.x idx2 idx3 idx4 idxs.y idxs.z idxs.w in
      A.varrayp_not_null r P.full_perm;
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r_idxs md_count_v;
      change_equal_slprop
        (A.varray r)
        (if (A.is_null r) then emp else A.varray r);
      return r
    ) else (
      let md_count_v' = read md_count in
      let b = US.lte (US.add md_count_v' 1sz) metadata_max_ex in
      if b then (
        allocate_slab_aux_3 size_class
          slab_region md_bm_region md_region md_count r_idxs
          md_count_v md_region_lv
          idx1 idx2 idx3 idx4 idx5 idx6 idx7;
        //change_slprop_rel
        //  (AL.varraylist pred1 pred2 pred3 pred4 pred5
        //    (A.split_l md_region (md_count_v `US.add` 1sz))
        //    (US.v md_count_v)
        //    (US.v idx2) (US.v idx3) (US.v idx4)
        //    (US.v idx5) (US.v idx6) (US.v idx7))
        //  (AL.varraylist pred1 pred2 pred3 pred4 pred5
        //    (A.split_l md_region (md_count_v `US.add` 1sz))
        //    (US.v md_cto)
        //    (US.v (US.sub (US.add md_count_v guard_pages_interval) 2sz))
        //    (US.v idx2) (US.v idx3)
        //    (US.v (US.sub (US.add md_count_v guard_pages_interval) 1sz))
        //    (US.v idx5)
        //    (US.v idx6)
        //    (US.v idx7))
        //  (fun x y -> x == y)
        //  (fun m -> ALG.varraylist_to_varraylist_lemma #AL.status
        //    #pred1 #pred2 #pred3 #pred4 #pred5
        //    (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
        //    (US.v md_count_v + US.v guard_pages_interval - 2)
        //    (US.v idx2) (US.v idx3)
        //    (US.v md_count_v + US.v guard_pages_interval - 1)
        //    (US.v idx5)
        //    (US.v idx6)
        //    (US.v idx7)
        //    (US.v (US.sub (US.add md_count_v guard_pages_interval) 2sz))
        //    (US.v idx2) (US.v idx3)
        //    (US.v (US.sub (US.add md_count_v guard_pages_interval) 1sz))
        //    (US.v idx5)
        //    (US.v idx6)
        //    (US.v idx7)
        //    m
        //  );
        let r = allocate_slab_aux_1 size_class
          slab_region md_bm_region md_region md_count r_idxs
          (US.add md_count_v 1sz)
          (G.hide (Seq.append
            (G.reveal md_region_lv)
            (Seq.create 1 0ul)))
          md_count_v
          idx2 idx3 idx4 idx5 idx6 idx7 in
        pack_right_and_refactor_vrefine_dep
          size_class slab_region md_bm_region md_region md_count
          r_idxs
          (US.add md_count_v 1sz);
        A.varrayp_not_null r P.full_perm;
        change_equal_slprop
          (A.varray r)
          (if (A.is_null r) then emp else A.varray r);
        return r
      ) else (
        pack_3 size_class
          slab_region md_bm_region md_region
          md_count r_idxs
          md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7;
        pack_right_and_refactor_vrefine_dep
          size_class slab_region md_bm_region md_region
          md_count
          r_idxs md_count_v;
        change_equal_slprop
          emp
          (if A.is_null A.null then emp else A.varray A.null);
        return (A.null #U8.t)
      )
    )
  )

#restart-solver

#restart-solver

#push-options "--z3rlimit 300 --compat_pre_typed_indexed_effects"
let allocate_slab
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
      //((A.offset (A.ptr_of r) - A.offset (A.ptr_of slab_region)) % U32.v page_size) % (U32.v size_class) == 0
      True
    )
  )
  =
  let md_count_v
    : G.erased _
    = elim_vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs) in

  let md_count_v_ = read md_count in

  change_equal_slprop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs (G.reveal md_count_v))
    (left_vprop size_class slab_region md_bm_region md_region
      r_idxs md_count_v_ `star`
    right_vprop slab_region md_bm_region md_region md_count_v_);
  change_equal_slprop
    (left_vprop size_class slab_region md_bm_region md_region
      r_idxs md_count_v_)
    (left_vprop1 md_region r_idxs md_count_v_
    `vdep`
    left_vprop2 size_class slab_region md_bm_region md_region r_idxs md_count_v_);

  let x
    : G.erased _
    = elim_vdep
    (left_vprop1 md_region r_idxs md_count_v_)
    (left_vprop2 size_class slab_region md_bm_region md_region r_idxs md_count_v_) in

  let idxs
    : G.erased _
    = elim_vdep
      (A.varray r_idxs)
      (ind_varraylist_aux (A.split_l md_region md_count_v_))
  in
  let idx1_ = A.index r_idxs 0sz in
  let idx2_ = A.index r_idxs 1sz in
  let idx3_ = A.index r_idxs 2sz in
  let idx4_ = A.index r_idxs 3sz in
  let idx5_ = A.index r_idxs 4sz in
  let idx6_ = A.index r_idxs 5sz in
  let idx7_ = A.index r_idxs 6sz in

  elim_vrefine
    (ind_varraylist_aux2 (A.split_l md_region md_count_v_) idxs)
    (ind_varraylist_aux_refinement (A.split_l md_region md_count_v_) idxs);
  // OK
  change_slprop_rel
    (ind_varraylist_aux2 (A.split_l md_region md_count_v_) idxs)
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v_)
      (US.v (Seq.index idxs 0))
      (US.v (Seq.index idxs 1))
      (US.v (Seq.index idxs 2))
      (US.v (Seq.index idxs 3))
      (US.v (Seq.index idxs 4))
      (US.v (Seq.index idxs 5))
      (US.v (Seq.index idxs 6)))
    (fun x y -> x == y)
    (fun _ -> ind_varraylist_aux2_lemma
      (A.split_l md_region md_count_v_)
      (G.reveal idxs)
      idx1_ idx2_ idx3_ idx4_ idx5_ idx6_ idx7_);
  change_slprop_rel
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v_)
      (US.v (Seq.index idxs 0))
      (US.v (Seq.index idxs 1))
      (US.v (Seq.index idxs 2))
      (US.v (Seq.index idxs 3))
      (US.v (Seq.index idxs 4))
      (US.v (Seq.index idxs 5))
      (US.v (Seq.index idxs 6)))
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v_)
      (US.v idx1_) (US.v idx2_) (US.v idx3_) (US.v idx4_) (US.v idx5_) (US.v idx6_) (US.v idx7_))
    (fun x y -> x == y)
    (fun m -> ALG.varraylist_to_varraylist_lemma #AL.status
      #pred1 #pred2 #pred3 #pred4 #pred5
      (A.split_l md_region md_count_v_)
      (US.v (Seq.index idxs 0))
      (US.v (Seq.index idxs 1))
      (US.v (Seq.index idxs 2))
      (US.v (Seq.index idxs 3))
      (US.v (Seq.index idxs 4))
      (US.v (Seq.index idxs 5))
      (US.v (Seq.index idxs 6))
      (US.v idx1_) (US.v idx2_) (US.v idx3_) (US.v idx4_) (US.v idx5_) (US.v idx6_) (US.v idx7_)
      m
    );

  let x' : Ghost.erased (Seq.lseq AL.status (US.v md_count_v_)) = ALG.dataify (dsnd x) in
  // NOT OK

  change_equal_slprop
    (left_vprop2 size_class slab_region md_bm_region md_region r_idxs md_count_v_ x)
    (left_vprop2_aux size_class slab_region md_bm_region md_count_v_ x');
  change_equal_slprop
    (left_vprop2_aux size_class slab_region md_bm_region md_count_v_ x')
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v_})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v_ x')
      (f_lemma size_class slab_region md_bm_region md_count_v_ x')
      (SeqUtils.init_us_refined (US.v md_count_v_)));

  let r = allocate_slab' size_class
    slab_region md_bm_region md_region md_count r_idxs
    md_count_v_ x' idx1_ idx2_ idx3_ idx4_ idx5_ idx6_ idx7_
  in

  return r
