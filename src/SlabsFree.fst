module SlabsFree

module UP = FStar.PtrdiffT
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module G = FStar.Ghost
module FI = FStar.Int
module L = FStar.List.Tot

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

module AL = ArrayList

open Prelude
open Config
open Utils2
open SlotsAlloc
open SlotsFree
open SlabsCommon

open FStar.Mul
open SteelStarSeqUtils
open SteelVRefineDep
module AL = ArrayList
module ALG = ArrayListGen

#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let deallocate_slab_aux_cond
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
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
    let v0 : Seq.lseq U64.t 4 = dfst blob0 in
    dfst blob0 == dfst blob1 /\
    dsnd blob0 == dsnd blob1 /\
    blob0 == blob1 /\
    r == is_empty size_class v0
  )
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  let md_as_seq : G.erased (Seq.lseq U64.t 4)
    = elim_slab_vprop size_class md arr in
  let r = is_empty_s size_class md in
  intro_slab_vprop size_class md md_as_seq arr;
  return r

module FS = FStar.FiniteSet.Base

inline_for_extraction noextract
let deallocate_slab_aux_1_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) in
  //assert (ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3));
  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
  (**) lemma_partition_and_pred_implies_mem3 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 (US.v pos);
  assert (ALG.mem #AL.status (US.v pos) (US.v idx3) gs0);

  let idx3' = AL.remove3 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    (G.hide (US.v idx1)) (G.hide (US.v idx2)) idx3 (G.hide (US.v idx4)) (G.hide (US.v idx5)) pos in
  AL.insert2 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx2 (G.hide (US.v idx1)) (G.hide (US.v idx3')) (G.hide (US.v idx4)) (G.hide (US.v idx5)) pos 1ul;
  write r3 idx3';
  write r2 pos;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v pos) (US.v idx3') (US.v idx4) (US.v idx5)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1) (US.v pos) (US.v idx3') (US.v idx4) (US.v idx5) gs1);
  //assert (ALG.partition #AL.status gs1 (US.v idx1) (US.v pos) (US.v idx3'));

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
    idx1 pos idx3' idx4 idx5

inline_for_extraction noextract
let deallocate_slab_aux_1_empty
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) in
  //assert (ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3));
  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
  (**) lemma_partition_and_pred_implies_mem3 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 (US.v pos);
  assert (ALG.mem #AL.status (US.v pos) (US.v idx3) gs0);

  let idx3' = AL.remove3 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    (G.hide (US.v idx1)) (G.hide (US.v idx2)) idx3 (G.hide (US.v idx4)) (G.hide (US.v idx5)) pos in
  AL.insert1 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3')) (G.hide (US.v idx4)) (G.hide (US.v idx5)) pos 0ul;
  write r3 idx3';
  write r1 pos;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v pos) (US.v idx2) (US.v idx3') (US.v idx4) (US.v idx5)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v pos) (US.v idx2) (US.v idx3') (US.v idx4) (US.v idx5) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
    pos idx2 idx3' idx4 idx5

#restart-solver

inline_for_extraction noextract
let deallocate_slab_aux_1_fail
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos) `star`
    (vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v pos)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos))
    = h0 (slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos)) in
    let md : Seq.lseq U64.t 4 = dfst md_blob in
    is_full size_class md /\
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  p_full_pack size_class
    (md_bm_array md_bm_region pos, slab_array slab_region pos)
    (md_bm_array md_bm_region pos, slab_array slab_region pos);
  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v pos);
  change_equal_slprop
    (p_full size_class (md_bm_array md_bm_region pos, slab_array slab_region pos))
    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos)));
  starseq_pack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v pos);
  pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5

#restart-solver

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
inline_for_extraction noextract
let deallocate_slab_aux_1
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{US.v pos < US.v md_count_v})
  (pos2: US.t{US.v pos2 < U32.v page_size})
  : Steel bool
  (
    A.varray ptr `star`
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    let arr' = slab_array slab_region pos in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr') in
    same_base_array arr' ptr /\
    0 <= diff /\
    diff < U32.v page_size /\
    US.v pos2 == diff /\
    (U32.v page_size) % (U32.v size_class) = 0 /\
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  (**) starseq_unpack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v pos);
  (**) SeqUtils.init_us_refined_index (US.v md_count_v) (US.v pos);
  (**) change_equal_slprop
    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos)))
    (p_full size_class (md_bm_array md_bm_region pos, slab_array slab_region pos));
  (**) p_full_unpack size_class
    (md_bm_array md_bm_region pos, slab_array slab_region pos)
    (md_bm_array md_bm_region pos, slab_array slab_region pos);
  let b = deallocate_slot size_class
    (md_bm_array md_bm_region pos)
    (slab_array slab_region pos)
    ptr pos2 in
  if b then (
    // deallocation success, slab no longer full
    let cond = deallocate_slab_aux_cond size_class
      (md_bm_array md_bm_region pos)
      (slab_array slab_region pos) in
    if cond then (
      pack_slab_starseq size_class
        slab_region md_bm_region md_region md_count
        md_count_v md_region_lv pos 0ul;
      deallocate_slab_aux_1_empty size_class
        slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos;
      return b
    ) else (
      pack_slab_starseq size_class
        slab_region md_bm_region md_region md_count
        md_count_v md_region_lv pos 1ul;
      deallocate_slab_aux_1_partial size_class
        slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos;
      return b
    )
  ) else (
    deallocate_slab_aux_1_fail size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
      md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos;
    return b
  )
#pop-options


inline_for_extraction noextract
let deallocate_slab_aux_2_empty
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)  h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) in
  //assert (ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3));
  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
  (**) lemma_partition_and_pred_implies_mem2 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 (US.v pos);
  assert (ALG.mem #AL.status (US.v pos) (US.v idx2) gs0);

  let idx2' = AL.remove2 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    (G.hide (US.v idx1)) idx2 (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) pos in
  AL.insert1 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx1 (G.hide (US.v idx2')) (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) pos 0ul;
  write r2 idx2';
  write r1 pos;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v pos) (US.v idx2') (US.v idx3) (US.v idx4) (US.v idx5)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v pos) (US.v idx2') (US.v idx3) (US.v idx4) (US.v idx5) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
    pos idx2' idx3 idx4 idx5

inline_for_extraction noextract
let deallocate_slab_aux_2_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{US.v pos < US.v md_count_v})
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5

inline_for_extraction noextract
let deallocate_slab_aux_2_fail
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos) `star`
    (vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v pos)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos + 1)
        (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos))
    = h0 (slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos)) in
    let md : Seq.lseq U64.t 4 = dfst md_blob in
    is_partial size_class md /\
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` Ghost.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  p_partial_pack size_class
    (md_bm_array md_bm_region pos, slab_array slab_region pos)
    (md_bm_array md_bm_region pos, slab_array slab_region pos);
  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v pos);
  change_equal_slprop
    (p_partial size_class (md_bm_array md_bm_region pos, slab_array slab_region pos))
    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos)));
  starseq_pack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v pos);
  pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5

#restart-solver

#push-options "--z3rlimit 100"
inline_for_extraction noextract
let deallocate_slab_aux_2
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (pos: US.t{US.v pos < US.v md_count_v})
  (pos2: US.t{US.v pos2 < U32.v page_size})
  : Steel bool
  (
    A.varray ptr `star`
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    let arr' = slab_array slab_region pos in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr') in
    same_base_array arr' ptr /\
    0 <= diff /\
    diff < U32.v page_size /\
    US.v pos2 == diff /\
    (U32.v page_size) % (U32.v size_class) = 0 /\
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  (**) starseq_unpack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v pos);
  (**) SeqUtils.init_us_refined_index (US.v md_count_v) (US.v pos);
  (**) change_equal_slprop
    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos)))
    (p_partial size_class (md_bm_array md_bm_region pos, slab_array slab_region pos));
  (**) p_partial_unpack size_class
    (md_bm_array md_bm_region pos, slab_array slab_region pos)
    (md_bm_array md_bm_region pos, slab_array slab_region pos);
  let b = deallocate_slot size_class
    (md_bm_array md_bm_region pos)
    (slab_array slab_region pos)
    ptr pos2 in
  if b then (
    // deallocation success, slab no longer full
    let cond = deallocate_slab_aux_cond size_class
      (md_bm_array md_bm_region pos)
      (slab_array slab_region pos) in
    if cond then (
      (**) pack_slab_starseq size_class
        slab_region md_bm_region md_region md_count
        md_count_v md_region_lv pos 0ul;
      deallocate_slab_aux_2_empty size_class
        slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos;
      return b
    ) else (
      (**) pack_slab_starseq size_class
        slab_region md_bm_region md_region md_count
        md_count_v md_region_lv pos 1ul;
      assert (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul `Seq.equal` md_region_lv);
    (**) starseq_weakening
      #_
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
      (SeqUtils.init_us_refined (US.v md_count_v));
      deallocate_slab_aux_2_partial size_class
        slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos;
      return b
    )
  ) else (
    deallocate_slab_aux_2_fail size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
      md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos;
    return b
  )
#pop-options

#restart-solver

inline_for_extraction noextract
let deallocate_slab_fail
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  : Steel bool
  (
    A.varray ptr `star`
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    US.v md_count_v <> AL.null /\
    md_count_v == sel md_count h0 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
   )
  (ensures fun _ _ _ -> True)
  =
  let b = false in
  pack_3 size_class
    slab_region md_bm_region md_region
    md_count r1 r2 r3 r4 r5
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5;
  pack_right_and_refactor_vrefine_dep
    size_class slab_region md_bm_region md_region md_count
    r1 r2 r3 r4 r5 md_count_v;
  change_equal_slprop
    (A.varray ptr)
    (if b then emp else A.varray ptr);
  return b

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
inline_for_extraction noextract
let deallocate_slab'
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  (diff: US.t)
  : Steel bool
  (
    A.varray ptr `star`
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab_region) in
    0 <= diff' /\
    //UP.v diff < US.v metadata_max * U32.v page_size /\
    US.v diff == diff' /\
    same_base_array ptr slab_region /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    US.v md_count_v <> AL.null /\
    md_count_v == sel md_count h0 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun _ _ _ -> True)
  =
  //let diff_sz = UP.ptrdifft_to_sizet diff in
  assert_norm (4 < FI.max_int 16);
  let pos = US.div diff (u32_to_sz page_size) in
  let pos2 = US.rem diff (u32_to_sz page_size) in
  // check diff/page_size < md_count
  if US.lt pos md_count_v then (
    A.ptr_shift_zero (A.ptr_of slab_region);
    let r = slab_array slab_region pos in
    assert (same_base_array ptr (slab_array slab_region pos));
    assert (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (slab_array slab_region pos)) >= 0);
    assert (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (slab_array slab_region pos)) < U32.v page_size);
    // selector equality propagation
    let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) in
    ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
    let status1 = AL.read_in_place
        (A.split_l md_region md_count_v)
        (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) pos in
    if (U32.eq status1 2ul) then (
      let b = deallocate_slab_aux_1 ptr size_class
        slab_region md_bm_region md_region
        md_count r1 r2 r3 r4 r5
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos pos2 in
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r1 r2 r3 r4 r5 md_count_v;
      return b
    ) else if (U32.eq status1 1ul) then (
      let b = deallocate_slab_aux_2 ptr size_class
        slab_region md_bm_region md_region
        md_count r1 r2 r3 r4 r5
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 pos pos2 in
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r1 r2 r3 r4 r5 md_count_v;
      return b
    ) else (
      deallocate_slab_fail ptr size_class
        slab_region md_bm_region md_region
        md_count r1 r2 r3 r4 r5
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5
    )
  ) else (
    deallocate_slab_fail ptr size_class
      slab_region md_bm_region md_region
      md_count r1 r2 r3 r4 r5
      md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5
  )

#restart-solver

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 150"
let deallocate_slab
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (diff_: US.t)
  : Steel bool
  (
    A.varray ptr `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun _ ->
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab_region) in
    0 <= diff' /\
    US.v diff_ == diff' /\
    same_base_array ptr slab_region)
  (ensures fun _ _ _ -> True)
  =
  let md_count_v
    : G.erased _
    = elim_vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5) in

  let md_count_v_ = read md_count in

  change_equal_slprop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 (G.reveal md_count_v))
    (left_vprop size_class slab_region md_bm_region md_region
      r1 r2 r3 r4 r5 md_count_v_ `star`
    right_vprop slab_region md_bm_region md_region md_count_v_);

  let x
    : G.erased _
    = elim_vdep
    (left_vprop1 md_region r1 r2 r3 r4 r5 md_count_v_)
    (left_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 md_count_v_) in

  change_equal_slprop
    (left_vprop1 md_region r1 r2 r3 r4 r5 md_count_v_)
    (ind_varraylist
      (A.split_l md_region md_count_v_)
       r1 r2 r3 r4 r5);

  let idxs
    : G.erased _
    = elim_vdep
      (vptr r1 `star` vptr r2 `star` vptr r3 `star` vptr r4 `star` vptr r5)
      (ind_varraylist_aux (A.split_l md_region md_count_v_))
  in
  let idx1_ = read r1 in
  let idx2_ = read r2 in
  let idx3_ = read r3 in
  let idx4_ = read r4 in
  let idx5_ = read r5 in

  elim_vrefine
    (ind_varraylist_aux2
      (A.split_l md_region md_count_v_) idxs)
    (ind_varraylist_aux_refinement
      (A.split_l md_region md_count_v_) idxs);

  change_slprop_rel
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v_)
      (US.v (fst (fst (fst (fst (G.reveal idxs))))))
      (US.v (snd (fst (fst (fst (G.reveal idxs))))))
      (US.v (snd (fst (fst (G.reveal idxs)))))
      (US.v (snd (fst (G.reveal idxs))))
      (US.v (snd (G.reveal idxs))))
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v_)
      (US.v idx1_) (US.v idx2_) (US.v idx3_) (US.v idx4_) (US.v idx5_))
    (fun x y -> x == y)
    (fun _ ->
      assert (idx1_ == fst (fst (fst (fst (G.reveal idxs)))));
      assert (idx2_ == snd (fst (fst (fst (G.reveal idxs)))));
      assert (idx3_ == snd (fst (fst (G.reveal idxs))));
      assert (idx4_ == snd (fst (G.reveal idxs)));
      assert (idx5_ == snd (G.reveal idxs))
    );

  let x' : G.erased (Seq.lseq AL.status (US.v md_count_v_)) = ALG.dataify (dsnd x) in

  change_equal_slprop
    (left_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 md_count_v_ x)
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v_})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v_ x')
      (f_lemma size_class slab_region md_bm_region md_count_v_ x')
      (SeqUtils.init_us_refined (US.v md_count_v_)));
  //let diff = A.ptrdiff ptr (A.split_l slab_region 0sz) in

  let b : bool = deallocate_slab' ptr size_class
    slab_region md_bm_region md_region md_count r1 r2 r3 r4 r5
    md_count_v_ x' idx1_ idx2_ idx3_ idx4_ idx5_ diff_ in
  return b
