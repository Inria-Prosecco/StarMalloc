module SlabsFree2

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

open Prelude
open Config
open Utils2
//open SlotsAlloc
//open SlotsFree
//open SlabsCommon
open SlabsCommon2

open FStar.Mul
open SteelStarSeqUtils
open SteelVRefineDep
module AL = ArrayList
module ALG = ArrayListGen

type tuple4 : Type0
  = {x: US.t; y: US.t; z: US.t; w: US.t}

//let bounded_tuple (up: US.t) = s:bounded_tuple'{
//  US.v s.x < US.v up
//  //US.v s.y < US.v up /\
//  //US.v s.z < US.v up
//  //US.v s.w < US.v quarantine_queue_length
//}

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100 --compat_pre_typed_indexed_effects"

// TODO: improve naming
// Whether the quarantine queue is full
// needs to be taken into account when enqueuing an element.
// If so, an element of it is dequeued before this operation.
// This is the role of the update_quarantine* functions:
// [ok] - update_quarantine_spec is the spec
// [ok] - update_quarantine2_aux unconditionnaly updates the varraylist
//   (only varraylist + varraylist indexes operations),
//   [corresponding memory region = md_region]
// [ok] - update_quarantine3_aux unconditionnally updates the starseq
//   (ghost operations + removing the memory trap as ro perms)
//   [corresponding memory regions = slab_region + md_region] ;
//   this one is reused, where?
// - update_quarantine2 updates the varraylist if needed
// - update_quarantine3 updates the varraylist if needed
// [ok] - update_quarantine uses update_quarantine{2,3} if needed

// [todo] - update_quarantine_aux unconditionnally updates both
//   to be used in SlabsAlloc, as allocate_aux_4
// [ok] - update_quarantine uses update_quarantine{2,3} if needed
//   to be used in SlabsFree

let update_quarantine_spec
  (md_count_v: US.t)
  (idx7: US.t)
  (idxs: tuple4{
    US.v idx7 >= US.v quarantine_queue_length
    ==>
    US.v idxs.x < US.v md_count_v
  })
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : G.erased (Seq.lseq AL.status (US.v md_count_v))
  =
  if US.lt idx7 quarantine_queue_length
  then
    md_region_lv
  else
    G.hide (Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul)

#restart-solver

let update_quarantine_spec_lemma
  (md_count_v: US.t)
  (idx7: US.t)
  (idxs: tuple4{
    US.v idx7 >= US.v quarantine_queue_length
    ==>
    US.v idxs.x < US.v md_count_v
  })
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (pos: US.t)
  (v: AL.status)
  : Lemma
  (requires
    US.v pos < US.v md_count_v /\
    idxs.x <> pos)
  (ensures
    Seq.upd (update_quarantine_spec md_count_v idx7 idxs md_region_lv) (US.v pos) v
    `Seq.equal`
    update_quarantine_spec md_count_v idx7 idxs (Seq.upd md_region_lv (US.v pos) v)
  )
  = ()

module FS = FStar.FiniteSet.Base

// returns idxs such that:
// - idxs.x is the new hd of empty list
// - idxs.y is the new hd of quarantine list
// - idxs.z is the new tl of quarantine list
// - idxs.w is the new sz of quarantine list
let update_quarantine2_aux
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel tuple4
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
      (US.v idxs.w))
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    //US.v md_count_v <> AL.null /\
    //idx5 <> AL.null_ptr /\
    idx7 <> 0sz /\
    //US.v idx7 == US.v quarantine_queue_length /\
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
    US.v idxs.x < US.v md_count_v /\
    US.v idxs.w < US.v quarantine_queue_length /\
    FS.mem (US.v idxs.x) (ALG.ptrs_in #AL.status (US.v idxs.x) gs1) /\
    ALG.ptrs_all #AL.status
      (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y) gs1
    `FS.equal`
    ALG.ptrs_all #AL.status
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    Seq.index (G.reveal md_region_lv) (US.v idxs.x) = 4ul /\
    ALG.dataify gs1 `Seq.equal` Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul /\
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

  let idxs : ALG.tuple3 = AL.dequeue #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx5 idx6 idx7
    (G.hide (US.v idx1)) (G.hide (US.v idx2))
    (G.hide (US.v idx3)) (G.hide (US.v idx4)) in

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

#restart-solver

/// AF: The regular noop does not seem to pick the equality of selectors, not sure why
val noop (#opened:_) (#p:vprop) (_:unit)
  : SteelGhostF unit opened p (fun _ -> p) (requires fun _ -> True) (ensures fun h0 _ h1 -> h0 p == h1 p)
let noop () = noop ()

let lemma_head1_implies_pred1 (#opened:_)
  (r:A.array AL.cell)
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:US.t) :
  SteelGhost unit opened
    (AL.varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
    (fun _ -> AL.varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
    (requires fun h ->
      hd1 = AL.null_ptr \/ US.v hd1 < A.length r
    )
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (AL.varraylist pred1 pred2 pred3 pred4 pred5 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
      let gs1 = h1 (AL.varraylist pred1 pred2 pred3 pred4 pred5 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
      // Framing
      gs1 == gs0 /\
      (hd1 = AL.null_ptr \/ US.v hd1 < A.length r) /\
      // Functional property
      (hd1 <> ALG.null_ptr ==>
        pred1 (ALG.get_data (Seq.index gs1 (US.v hd1))) /\
        Seq.index (ALG.dataify gs1) (US.v hd1) = 0ul)
    )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5 r
    (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
  if hd1 <> ALG.null_ptr
  then (
    ALG.lemma_dataify_index #AL.status gs0 (US.v hd1);
    ALG.lemma_head1_implies_pred1 #AL.status #_
      pred1 pred2 pred3 pred4 pred5
      r
      hd1 hd2 hd3 hd4 hd5 tl5 sz5
  ) else (
    noop ()
  )

let update_quarantine2
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel tuple4
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
      (US.v idxs.w))
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    //US.v md_count_v <> AL.null /\
    //idx5 <> AL.null_ptr /\
    //US.v idx7 == US.v quarantine_queue_length /\
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
    (US.v idx7 >= US.v quarantine_queue_length ==>
      (US.v idxs.x < US.v md_count_v /\
      Seq.index (G.reveal md_region_lv) (US.v idxs.x) = 4ul)) /\
    (US.v idxs.x < US.v md_count_v ==>
      (Seq.index (G.reveal md_region_lv) (US.v idxs.x) = 4ul \/
      Seq.index (G.reveal md_region_lv) (US.v idxs.x) = 0ul)
    ) /\
    US.v idxs.w < US.v quarantine_queue_length /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.dataify gs1 `Seq.equal` update_quarantine_spec md_count_v idx7 idxs (G.reveal md_region_lv) /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    ALG.partition #AL.status gs1 (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y)
  )
  =
  if (US.lt idx7 quarantine_queue_length) then (
    let r = { x = idx1; y = idx5; z = idx6; w = idx7; } in
    ALG.lemma_head1_in_bounds pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7);
    lemma_head1_implies_pred1 
      (A.split_l md_region md_count_v)
      idx1 idx2 idx3 idx4 idx5 idx6 idx7;
    change_slprop_rel
      (AL.varraylist pred1 pred2 pred3 pred4 pred5
        (A.split_l md_region md_count_v)
        (US.v idx1)
        (US.v idx2) (US.v idx3) (US.v idx4)
        (US.v idx5) (US.v idx6) (US.v idx7))
      (AL.varraylist pred1 pred2 pred3 pred4 pred5
        (A.split_l md_region md_count_v)
        (US.v r.x)
        (US.v idx2) (US.v idx3) (US.v idx4)
        (US.v r.y) (US.v r.z) (US.v r.w))
      (fun x y -> x == y)
      (fun m -> ALG.varraylist_to_varraylist_lemma #AL.status
        #pred1 #pred2 #pred3 #pred4 #pred5
        (A.split_l md_region md_count_v)
        (US.v idx1)
        (US.v idx2) (US.v idx3) (US.v idx4)
        (US.v idx5) (US.v idx6) (US.v idx7)
        (US.v r.x)
        (US.v idx2) (US.v idx3) (US.v idx4)
        (US.v r.y) (US.v r.z) (US.v r.w)
        m
      );
    return r
  ) else (
    let idxs = update_quarantine2_aux size_class
      slab_region md_bm_region md_region md_count r_idxs
      md_count_v md_region_lv
      idx1 idx2 idx3 idx4 idx5 idx6 idx7 in
    return idxs
  )


#push-options "--fuel 1 --ifuel 1 --z3rlimit 100 --compat_pre_typed_indexed_effects"
let update_quarantine3_aux
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (idxs: tuple4)
  : Steel (G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun md_region_lv' ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv')
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv')
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun _ ->
    US.v idxs.x < US.v md_count_v /\
    Seq.index (G.reveal md_region_lv) (US.v idxs.x) == 4ul
  )
  (ensures fun _ md_region_lv' _ ->
    US.v idxs.x < US.v md_count_v /\
    md_region_lv'
    `Seq.equal`
    Seq.upd (G.reveal md_region_lv) (US.v idxs.x) 0ul
  )
  =
  let idx = idxs.x in
  (**) starseq_unpack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx);
  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx);
  (**) change_equal_slprop
    (f size_class slab_region md_bm_region md_count_v md_region_lv
      (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)))
    (p_quarantine size_class (md_bm_array md_bm_region idx, slab_array slab_region idx));
    p_quarantine_unpack size_class (md_bm_array md_bm_region idx, slab_array slab_region idx);
    Quarantine2.mmap_untrap_quarantine size_class
      (A.split_l
        (snd
          (md_bm_array md_bm_region idx,
          slab_array slab_region idx))
        (u32_to_sz size_class))
      (US.sub slab_size (u32_to_sz size_class));
    sladmit ();
    //rewrite_slprop
    //  (A.varray (A.split_l (slab_array slab_region idx) (u32_to_sz page_size)) `star`
    //  A.varray (A.split_r (slab_array slab_region idx) (u32_to_sz page_size)))
    //  (A.varray (slab_array slab_region idx))
    //  (fun _ -> admit ());
    let md = gget (A.varray (md_bm_array md_bm_region idx)) in
    intro_slab_vprop_empty size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx);
    pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count
      md_count_v
      md_region_lv
      idx 0ul;
    let md_region_lv' = G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx) 0ul) in
    starseq_weakening
      #_
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v
        (Seq.upd (G.reveal md_region_lv) (US.v idx) 0ul))
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv'))
      (f_lemma size_class slab_region md_bm_region md_count_v
        (Seq.upd (G.reveal md_region_lv) (US.v idx) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv'))
      (SeqUtils.init_us_refined (US.v md_count_v))
      (SeqUtils.init_us_refined (US.v md_count_v));
    md_region_lv'

let update_quarantine3
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (idxs: tuple4)
  : Steel (G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun md_region_lv' ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv')
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv')
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun _ ->
    US.v idx7 >= US.v quarantine_queue_length ==> (
      US.v idxs.x < US.v md_count_v /\
      Seq.index (G.reveal md_region_lv) (US.v idxs.x) = 4ul
    )
  )
  (ensures fun _ md_region_lv' _ ->
    (US.v idx7 >= US.v quarantine_queue_length ==> (
      US.v idxs.x < US.v md_count_v /\
      Seq.index (G.reveal md_region_lv) (US.v idxs.x) = 4ul
    )) /\
    md_region_lv'
    `Seq.equal`
    update_quarantine_spec md_count_v idx7 idxs md_region_lv /\
    md_region_lv'
    ==
    update_quarantine_spec md_count_v idx7 idxs md_region_lv
  )
  =
  if (US.lt idx7 quarantine_queue_length) then (
    let md_region_lv' = md_region_lv in
    starseq_weakening
      #_
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f size_class slab_region md_bm_region md_count_v md_region_lv')
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv')
      (SeqUtils.init_us_refined (US.v md_count_v))
      (SeqUtils.init_us_refined (US.v md_count_v));
    return md_region_lv'
  ) else (
    let md_region_lv' = update_quarantine3_aux size_class
      slab_region md_bm_region md_region md_count r_idxs
      md_count_v md_region_lv
      idx1 idx2 idx3 idx4 idx5 idx6 idx7 idxs in
    return md_region_lv'
  )

#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
//inline_for_extraction noextract
//let deallocate_slab_aux_cond
//  (size_class: sc)
//  (md: slab_metadata)
//  (arr: array U8.t{A.length arr = US.v slab_size})
//  : Steel bool
//  (slab_vprop size_class arr md)
//  (fun _ -> slab_vprop size_class arr md)
//  (requires fun _ -> True)
//  (ensures fun h0 r h1 ->
//    let blob0
//      : t_of (slab_vprop size_class arr md)
//      = h0 (slab_vprop size_class arr md) in
//    let blob1
//      : t_of (slab_vprop size_class arr md)
//      = h1 (slab_vprop size_class arr md) in
//    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
//    dfst (fst blob0) == dfst (fst blob1) /\
//    dsnd (fst blob0) == dsnd (fst blob1) /\
//    blob0 == blob1 /\
//    r == is_empty size_class v0
//  )
//  =
//  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
//  let md_as_seq : G.erased (Seq.lseq U64.t 4)
//    = elim_slab_vprop size_class md arr in
//  let r = is_empty_s size_class md in
//  intro_slab_vprop size_class md md_as_seq arr;
//  return r

module FS = FStar.FiniteSet.Base

// Slab moves from full to partial
//inline_for_extraction noextract
//let deallocate_slab_aux_1_partial
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
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
//      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
//      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
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
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
//    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
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
//  //assert (ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3));
//  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
//  (**) lemma_partition_and_pred_implies_mem3 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) gs0 (US.v pos);
//  assert (ALG.mem #AL.status (US.v pos) (US.v idx3) gs0);
//
//  let idx3' = AL.remove3 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    (G.hide (US.v idx1)) (G.hide (US.v idx2)) idx3 (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) pos in
//  AL.insert2 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    idx2 (G.hide (US.v idx1)) (G.hide (US.v idx3')) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) pos 1ul;
//
//  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  A.upd r_idxs 2sz idx3';
//  A.upd r_idxs 1sz pos;
//  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  assert (G.reveal gs_idxs1
//  == Seq.upd (Seq.upd (G.reveal gs_idxs0) 2 idx3') 1 pos);
//
//  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idx1) (US.v pos) (US.v idx3') (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
//  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
//          ALG.ptrs_all #AL.status (US.v idx1) (US.v pos) (US.v idx3') (US.v idx4) (US.v idx5) gs1);
//  //assert (ALG.partition #AL.status gs1 (US.v idx1) (US.v pos) (US.v idx3'));
//
//  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
//    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
//    idx1 pos idx3' idx4 idx5 idx6 idx7

// Slab moves from full to empty
inline_for_extraction noextract
let deallocate_slab_aux_1_empty
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
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
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
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
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
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
  //assert (ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3));
  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
  (**) lemma_partition_and_pred_implies_mem3 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) gs0 (US.v pos);
  assert (ALG.mem #AL.status (US.v pos) (US.v idx3) gs0);

  let idx3' = AL.remove3 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    (G.hide (US.v idx1)) (G.hide (US.v idx2)) idx3 (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) pos in
  AL.insert1 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3')) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) pos 0ul;

  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  A.upd r_idxs 2sz idx3';
  A.upd r_idxs 0sz pos;
  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  assert (G.reveal gs_idxs1
  == Seq.upd (Seq.upd (G.reveal gs_idxs0) 2 idx3') 0 pos);

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v pos) (US.v idx2) (US.v idx3') (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v pos) (US.v idx2) (US.v idx3') (US.v idx4) (US.v idx5) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
    pos idx2 idx3' idx4 idx5 idx6 idx7

#restart-solver

inline_for_extraction noextract
let deallocate_slab_aux_1_fail
  (#opened:_)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos) `star`
    (vptr md_count `star`
    A.varray r_idxs `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
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
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos))
    = h0 (slab_vprop size_class
      (slab_array slab_region pos)
      (md_bm_array md_bm_region pos)) in
    let md : Seq.lseq bool 1 = dfst (fst md_blob) in
    let idxs0 = A.asel r_idxs h0 in
    is_full (Seq.index md 0)  /\
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    Seq.index idxs0 0 == idx1 /\
    Seq.index idxs0 1 == idx2 /\
    Seq.index idxs0 2 == idx3 /\
    Seq.index idxs0 3 == idx4 /\
    Seq.index idxs0 4 == idx5 /\
    Seq.index idxs0 5 == idx6 /\
    Seq.index idxs0 6 == idx7 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
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
  pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5 idx6 idx7

#restart-solver

#push-options "--z3rlimit 150 --compat_pre_typed_indexed_effects --query_stats"
// Slab moves from full to quarantine
//inline_for_extraction noextract
let deallocate_slab_aux_1_quarantine
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
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
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 4ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 4ul))
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
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
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

  // Ensuring the quarantine is not full by dequeuing if needed
  let idxs = update_quarantine2 size_class
    slab_region md_bm_region md_region
    md_count r_idxs md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5 idx6 idx7 in

  assert (pos <> idxs.x);

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y) (US.v idxs.z) (US.v idxs.w)) in

  (**) ALG.lemma_dataify_index #AL.status gs1 (US.v pos);
  (**) lemma_partition_and_pred_implies_mem3 (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y) (US.v idxs.z) (US.v idxs.w) gs1 (US.v pos);
  assert (ALG.mem #AL.status (US.v pos) (US.v idx3) gs1);
  let idx3' = AL.remove3 #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l md_region md_count_v)
    (G.hide (US.v idxs.x)) (G.hide (US.v idx2)) idx3 (G.hide (US.v idx4)) (G.hide (US.v idxs.y)) (G.hide (US.v idxs.z)) (G.hide (US.v idxs.w)) pos in
  let idxs' : ALG.tuple2
    = AL.enqueue #pred1 #pred2 #pred3 #pred4 #pred5
      (A.split_l md_region md_count_v)
      idxs.y idxs.z idxs.w
      (G.hide (US.v idxs.x)) (G.hide (US.v idx2)) (G.hide (US.v idx3')) (G.hide (US.v idx4))
      pos 4ul in

  (**) let gs2 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l md_region md_count_v)
    (US.v idxs.x) (US.v idx2) (US.v idx3') (US.v idx4) (US.v pos) (US.v idxs'.x) (US.v idxs'.y)) in

  assert (ALG.dataify #AL.status gs2 `Seq.equal` Seq.upd (ALG.dataify gs1) (US.v pos) 4ul);
  assert (ALG.dataify #AL.status gs1 `Seq.equal` update_quarantine_spec md_count_v idx7 idxs (ALG.dataify gs0));

  assert (ALG.ptrs_all #AL.status (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y) gs1 `FS.equal`
          ALG.ptrs_all #AL.status (US.v idxs.x) (US.v idx2) (US.v idx3') (US.v idx4) (US.v pos) gs2);

  let md_region_lv' = update_quarantine3 size_class
    slab_region md_bm_region md_region
    md_count r_idxs md_count_v
    (Seq.upd (G.reveal md_region_lv) (US.v pos) 4ul)
    idx1 idx2 idx3 idx4 idx5 idx6 idx7
    idxs in
  update_quarantine_spec_lemma md_count_v idx7 idxs
    md_region_lv pos 4ul;

  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  A.upd r_idxs 0sz idxs.x;
  A.upd r_idxs 2sz idx3';
  A.upd r_idxs 4sz pos;
  A.upd r_idxs 5sz idxs'.x;
  A.upd r_idxs 6sz idxs'.y;
  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
    md_count_v
    md_region_lv'
    idxs.x idx2 idx3' idx4 pos idxs'.x idxs'.y

#restart-solver

open Quarantine2

// Slab initially full
#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
inline_for_extraction noextract
let deallocate_slab_aux_1
  (ptr: array U8.t)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (pos: US.t{US.v pos < US.v md_count_v})
  (pos2: US.t{US.v pos2 < US.v slab_size})
  : Steel bool
  (
    A.varray ptr `star`
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
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let arr' = slab_array slab_region pos in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr') in
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
    same_base_array arr' ptr /\
    0 <= diff /\
    diff < U32.v page_size /\
    (diff % U32.v page_size) % U32.v size_class == 0 /\
    US.v pos2 == diff /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul /\
    A.length ptr == U32.v size_class
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
  //let b = true in
  //rewrite_slprop
  //  (A.varray ptr)
  //  (if b then emp else A.varray ptr)
  //  (fun _ -> admit ());

  let b = deallocate_slot size_class
    (slab_array slab_region pos)
    (md_bm_array md_bm_region pos)
    ptr pos2 in
  if b then (
    if enable_quarantine then (
        upd_and_pack_slab_starseq_quarantine size_class
          slab_region md_bm_region md_region md_count
          md_count_v md_region_lv pos;
        deallocate_slab_aux_1_quarantine size_class
          slab_region md_bm_region md_region md_count r_idxs
          md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos;
        return b
    ) else (
      //admit ();
      pack_slab_starseq size_class
        slab_region md_bm_region md_region md_count
        md_count_v md_region_lv pos 0ul;
      deallocate_slab_aux_1_empty size_class
        slab_region md_bm_region md_region md_count r_idxs
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos;
      return b
    )
 ) else (
    deallocate_slab_aux_1_fail size_class
      slab_region md_bm_region md_region md_count r_idxs
      md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos;
    return b
  )
#pop-options

let _ = ()

//// Slab moves from partial to empty
//inline_for_extraction noextract
//let deallocate_slab_aux_2_empty
//  (size_class: sc_ex)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
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
//      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
//      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
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
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
//    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
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
//  //assert (ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3));
//  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
//  (**) lemma_partition_and_pred_implies_mem2 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) gs0 (US.v pos);
//  assert (ALG.mem #AL.status (US.v pos) (US.v idx2) gs0);
//
//  let idx2' = AL.remove2 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    (G.hide (US.v idx1)) idx2 (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) pos in
//  AL.insert1 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    idx1 (G.hide (US.v idx2')) (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idx5)) (G.hide (US.v idx6)) (G.hide (US.v idx7)) pos 0ul;
//
//  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  A.upd r_idxs 1sz idx2';
//  A.upd r_idxs 0sz pos;
//  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  assert (G.reveal gs_idxs1
//  == Seq.upd (Seq.upd (G.reveal gs_idxs0) 1 idx2') 0 pos);
//
//  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v pos) (US.v idx2') (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
//  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) gs0 `FStar.FiniteSet.Base.equal`
//          ALG.ptrs_all #AL.status (US.v pos) (US.v idx2') (US.v idx3) (US.v idx4) (US.v idx5) gs1);
//
//  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
//    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
//    pos idx2' idx3 idx4 idx5 idx6 idx7
//
//#restart-solver
//
//// Slab moves from partial to partial
//inline_for_extraction noextract
//let deallocate_slab_aux_2_partial
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  (pos: US.t{US.v pos < US.v md_count_v})
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
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
//    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
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
//inline_for_extraction noextract
//let deallocate_slab_aux_2_fail
//  (#opened:_)
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
//  : SteelGhost unit opened
//  (
//    slab_vprop size_class
//      (slab_array slab_region pos)
//      (md_bm_array md_bm_region pos) `star`
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
//      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v pos)) `star`
//    starseq
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v md_region_lv)
//      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos + 1)
//        (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
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
//    let md_blob : t_of (slab_vprop size_class
//      (slab_array slab_region pos)
//      (md_bm_array md_bm_region pos))
//    = h0 (slab_vprop size_class
//      (slab_array slab_region pos)
//      (md_bm_array md_bm_region pos)) in
//    let md : Seq.lseq U64.t 4 = dfst (fst md_blob) in
//    let idxs0 = A.asel r_idxs h0 in
//    is_partial size_class md /\
//    US.v md_count_v <> AL.null /\
//    sel md_count h0 == md_count_v /\
//    Seq.index idxs0 0 == idx1 /\
//    Seq.index idxs0 1 == idx2 /\
//    Seq.index idxs0 2 == idx3 /\
//    Seq.index idxs0 3 == idx4 /\
//    Seq.index idxs0 4 == idx5 /\
//    Seq.index idxs0 5 == idx6 /\
//    Seq.index idxs0 6 == idx7 /\
//    ALG.dataify gs0 `Seq.equal` Ghost.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
//    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
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
//  p_partial_pack size_class
//    (md_bm_array md_bm_region pos, slab_array slab_region pos)
//    (md_bm_array md_bm_region pos, slab_array slab_region pos);
//  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v pos);
//  change_equal_slprop
//    (p_partial size_class (md_bm_array md_bm_region pos, slab_array slab_region pos))
//    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos)));
//  starseq_pack_s
//    #_
//    #(pos:US.t{US.v pos < US.v md_count_v})
//    #(t size_class)
//    (f size_class slab_region md_bm_region md_count_v md_region_lv)
//    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//    (SeqUtils.init_us_refined (US.v md_count_v))
//    (US.v pos);
//  pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
//    md_count_v md_region_lv
//    idx1 idx2 idx3 idx4 idx5 idx6 idx7
//
//#restart-solver
//
//// Slab moves from partial to quarantine
//inline_for_extraction noextract
//let deallocate_slab_aux_2_quarantine
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  (pos: US.t{pos <> AL.null_ptr /\ US.v pos < US.v md_count_v})
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
//      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 4ul))
//      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 4ul))
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
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
//    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
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
//
//  // Ensuring the quarantine is not full by dequeuing if needed
//  let idxs = update_quarantine2 size_class
//    slab_region md_bm_region md_region
//    md_count r_idxs md_count_v md_region_lv
//    idx1 idx2 idx3 idx4 idx5 idx6 idx7 in
//
//  assert (pos <> idxs.x);
//
//  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y) (US.v idxs.z) (US.v idxs.w)) in
//
//  (**) ALG.lemma_dataify_index #AL.status gs1 (US.v pos);
//  (**) lemma_partition_and_pred_implies_mem2 (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y) (US.v idxs.z) (US.v idxs.w) gs1 (US.v pos);
//  assert (ALG.mem #AL.status (US.v pos) (US.v idx2) gs1);
//  let idx2' = AL.remove2 #pred1 #pred2 #pred3 #pred4 #pred5
//    (A.split_l md_region md_count_v)
//    (G.hide (US.v idxs.x)) idx2 (G.hide (US.v idx3)) (G.hide (US.v idx4)) (G.hide (US.v idxs.y)) (G.hide (US.v idxs.z)) (G.hide (US.v idxs.w)) pos in
//  let idxs' : ALG.tuple2
//    = AL.enqueue #pred1 #pred2 #pred3 #pred4 #pred5
//      (A.split_l md_region md_count_v)
//      idxs.y idxs.z idxs.w (G.hide (US.v idxs.x)) (G.hide (US.v idx2')) (G.hide (US.v idx3)) (G.hide (US.v idx4))
//      pos 4ul in
//
//  (**) let gs2 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
//    (A.split_l md_region md_count_v)
//    (US.v idxs.x) (US.v idx2') (US.v idx3) (US.v idx4) (US.v pos) (US.v idxs'.x) (US.v idxs'.y)) in
//
//  assert (ALG.dataify #AL.status gs2 `Seq.equal` Seq.upd (ALG.dataify gs1) (US.v pos) 4ul);
//  assert (ALG.dataify #AL.status gs1 `Seq.equal` update_quarantine_spec md_count_v idx7 idxs (ALG.dataify gs0));
//
//  assert (ALG.ptrs_all #AL.status (US.v idxs.x) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idxs.y) gs1 `FS.equal`
//          ALG.ptrs_all #AL.status (US.v idxs.x) (US.v idx2') (US.v idx3) (US.v idx4) (US.v pos) gs2);
//
//  let md_region_lv' = update_quarantine3 size_class
//    slab_region md_bm_region md_region
//    md_count r_idxs md_count_v
//    (Seq.upd (G.reveal md_region_lv) (US.v pos) 4ul)
//    idx1 idx2 idx3 idx4 idx5 idx6 idx7
//    idxs in
//  update_quarantine_spec_lemma md_count_v idx7 idxs
//    md_region_lv pos 4ul;
//
//  let gs_idxs0 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//  A.upd r_idxs 0sz idxs.x;
//  A.upd r_idxs 1sz idx2';
//  A.upd r_idxs 4sz pos;
//  A.upd r_idxs 5sz idxs'.x;
//  A.upd r_idxs 6sz idxs'.y;
//  let gs_idxs1 : G.erased (Seq.lseq US.t 7)
//    = gget (A.varray r_idxs) in
//
//  (**) pack_3 size_class slab_region md_bm_region md_region md_count r_idxs
//    md_count_v
//    md_region_lv'
//    idxs.x idx2' idx3 idx4 pos idxs'.x idxs'.y
//
//#restart-solver
//
//#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects --query_stats"
//// Slab initially partial
//inline_for_extraction noextract
//let deallocate_slab_aux_2
//  (ptr: array U8.t)
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count: ref US.t)
//  (r_idxs: array US.t{A.length r_idxs = 7})
//  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
//  (pos: US.t{US.v pos < US.v md_count_v})
//  (pos2: US.t{US.v pos2 < U32.v page_size})
//  : Steel bool
//  (
//    A.varray ptr `star`
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
//  (fun b ->
//    (if b then emp else A.varray ptr) `star`
//    vrefinedep
//      (vptr md_count)
//      vrefinedep_prop
//      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
//  )
//  (requires fun h0 ->
//    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
//      (A.split_l md_region md_count_v)
//      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
//    let arr' = slab_array slab_region pos in
//    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr') in
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
//    same_base_array arr' ptr /\
//    0 <= diff /\
//    diff < U32.v page_size /\
//    (diff % U32.v page_size) % U32.v size_class == 0 /\
//    US.v pos2 == diff /\
//    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
//    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
//    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul /\
//    A.length ptr == U32.v size_class
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
//  (**) starseq_unpack_s
//    #_
//    #(pos:US.t{US.v pos < US.v md_count_v})
//    #(t size_class)
//    (f size_class slab_region md_bm_region md_count_v md_region_lv)
//    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//    (SeqUtils.init_us_refined (US.v md_count_v))
//    (US.v pos);
//  (**) SeqUtils.init_us_refined_index (US.v md_count_v) (US.v pos);
//  (**) change_equal_slprop
//    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v pos)))
//    (p_partial size_class (md_bm_array md_bm_region pos, slab_array slab_region pos));
//  (**) p_partial_unpack size_class
//    (md_bm_array md_bm_region pos, slab_array slab_region pos)
//    (md_bm_array md_bm_region pos, slab_array slab_region pos);
//  let b = deallocate_slot size_class
//    (md_bm_array md_bm_region pos)
//    (slab_array slab_region pos)
//    ptr pos2 in
//  if b then (
//    // deallocation success, slab no longer full
//    let cond = deallocate_slab_aux_cond size_class
//      (md_bm_array md_bm_region pos)
//      (slab_array slab_region pos) in
//    if cond then (
//      if enable_quarantine then (
//        upd_and_pack_slab_starseq_quarantine size_class
//          slab_region md_bm_region md_region md_count
//          md_count_v md_region_lv pos;
//        deallocate_slab_aux_2_quarantine size_class
//          slab_region md_bm_region md_region md_count r_idxs
//          md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos;
//        return b
//      ) else (
//        (**) pack_slab_starseq size_class
//          slab_region md_bm_region md_region md_count
//          md_count_v md_region_lv pos 0ul;
//        deallocate_slab_aux_2_empty size_class
//          slab_region md_bm_region md_region md_count r_idxs
//          md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos;
//        return b
//      )
//    ) else (
//      (**) pack_slab_starseq size_class
//        slab_region md_bm_region md_region md_count
//        md_count_v md_region_lv pos 1ul;
//      assert (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul `Seq.equal` md_region_lv);
//    (**) starseq_weakening
//      #_
//      #(pos:US.t{US.v pos < US.v md_count_v})
//      #(t size_class)
//      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
//      (f size_class slab_region md_bm_region md_count_v md_region_lv)
//      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
//      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
//      (SeqUtils.init_us_refined (US.v md_count_v))
//      (SeqUtils.init_us_refined (US.v md_count_v));
//      deallocate_slab_aux_2_partial size_class
//        slab_region md_bm_region md_region md_count r_idxs
//        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos;
//      return b
//    )
//  ) else (
//    deallocate_slab_aux_2_fail size_class
//      slab_region md_bm_region md_region md_count r_idxs
//      md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos;
//    return b
//  )
#pop-options

#restart-solver

inline_for_extraction noextract
let deallocate_slab_fail
  (ptr: array U8.t)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Steel bool
  (
    A.varray ptr `star`
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
  (fun b ->
    (if b then emp else A.varray ptr) `star`
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
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
   )
  (ensures fun _ _ _ -> True)
  =
  let b = false in
  pack_3 size_class
    slab_region md_bm_region md_region
    md_count r_idxs
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4 idx5 idx6 idx7;
  pack_right_and_refactor_vrefine_dep
    size_class slab_region md_bm_region md_region md_count
    r_idxs md_count_v;
  change_equal_slprop
    (A.varray ptr)
    (if b then emp else A.varray ptr);
  return b

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 150"
inline_for_extraction noextract
let deallocate_slab'
  (ptr: array U8.t)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  (diff: US.t)
  : Steel bool
  (
    A.varray ptr `star`
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
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab_region) in
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
    0 <= diff' /\
    (diff' % U32.v page_size) % U32.v size_class == 0 /\
    //UP.v diff < US.v metadata_max * U32.v page_size /\
    US.v diff == diff' /\
    same_base_array ptr slab_region /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) /\
    A.length ptr == U32.v size_class
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
    assume (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (slab_array slab_region pos)) >= 0);
    assert (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (slab_array slab_region pos)) < US.v slab_size);
    // selector equality propagation
    let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) in
    ALG.lemma_dataify_index #AL.status gs0 (US.v pos);
    let status1 = AL.read_in_place
        (A.split_l md_region md_count_v)
        (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) pos in
    if (U32.eq status1 2ul) then (
      let b = deallocate_slab_aux_1 ptr size_class
        slab_region md_bm_region md_region
        md_count r_idxs
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos pos2 in
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r_idxs md_count_v;
      return b
    ) else if (U32.eq status1 1ul) then (
      //failwith
      sladmit ();
      //let b = deallocate_slab_aux_2 ptr size_class
      //  slab_region md_bm_region md_region
      //  md_count r_idxs
      //  md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7 pos pos2 in
      //pack_right_and_refactor_vrefine_dep
      //  size_class slab_region md_bm_region md_region md_count
      //  r_idxs md_count_v;
      return false
    ) else (
      deallocate_slab_fail ptr size_class
        slab_region md_bm_region md_region
        md_count r_idxs
        md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7
    )
  ) else (
    deallocate_slab_fail ptr size_class
      slab_region md_bm_region md_region
      md_count r_idxs
      md_count_v md_region_lv idx1 idx2 idx3 idx4 idx5 idx6 idx7
  )

#restart-solver

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 300"
let deallocate_slab
  (ptr: array U8.t)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (diff_: US.t)
  : Steel bool
  (
    A.varray ptr `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun _ ->
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab_region) in
    0 <= diff' /\
    (diff' % U32.v page_size) % U32.v size_class == 0 /\
    US.v diff_ == diff' /\
    same_base_array ptr slab_region /\
    A.length ptr == U32.v size_class)
  (ensures fun _ _ _ -> True)
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

  let b : bool = deallocate_slab' ptr size_class
    slab_region md_bm_region md_region md_count r_idxs
    md_count_v_ x' idx1_ idx2_ idx3_ idx4_ idx5_ idx6_ idx7_ diff_ in
  return b
