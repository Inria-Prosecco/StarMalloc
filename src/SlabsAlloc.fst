module SlabsAlloc

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

open SlotsAlloc
open SteelStarSeqUtils
open FStar.Mul
open SlabsCommon


#push-options "--z3rlimit 50"
inline_for_extraction noextract
let allocate_slab_aux_cond
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
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    dfst (fst blob0) == dfst (fst blob1) /\
    dsnd (fst blob0) == dsnd (fst blob1) /\
    blob0 == blob1 /\
    r == is_full size_class v0
  )
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  let md_as_seq : G.erased (Seq.lseq U64.t 4)
    = elim_slab_vprop size_class md arr in
  let r = is_full_s size_class md in
  intro_slab_vprop size_class md md_as_seq arr;
  return r
#pop-options

let slab_region_mon_split
  (#opened:_)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
  (A.varray (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))))
  (fun _ ->
    A.varray (slab_array slab_region md_count) `star`
    A.varray (A.split_r slab_region (US.mul (US.add md_count 1sz) (u32_to_sz page_size)))
  )
  (requires fun h0 ->
    zf_u8 (A.asel (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) h0))
  (ensures fun h0 _ h1 ->
    zf_u8 (A.asel (slab_array slab_region md_count) h1) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.add md_count 1sz) (u32_to_sz page_size))) h1)
  )
  =
  let h0 = get () in
  A.ghost_split
    (A.split_r slab_region (US.mul md_count (u32_to_sz page_size)))
    (u32_to_sz page_size);
  zf_u8_slice (A.asel (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) h0) 0 (US.v (u32_to_sz page_size));
  zf_u8_slice (A.asel (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) h0) (US.v (u32_to_sz page_size)) (A.length (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))));
  pack_slab_array slab_region md_count;
  let x1 = A.split_r (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) (u32_to_sz page_size) in
  let x2 = A.split_r slab_region (US.mul (US.add md_count 1sz) (u32_to_sz page_size)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) (u32_to_sz page_size)))
    (A.varray (A.split_r slab_region (US.mul (US.add md_count 1sz) (u32_to_sz page_size))))

let md_bm_region_mon_split
  (#opened:_)
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
  (A.varray (A.split_r md_bm_region (US.mul md_count 4sz)))
  (fun _ ->
    A.varray (md_bm_array md_bm_region md_count) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz))
  )
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul md_count 4sz)) h0))
  (ensures fun h0 _ h1 ->
    zf_u64 (A.asel (md_bm_array md_bm_region md_count) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz)) h1)
  )
  =
  let h0 = get () in
  A.ghost_split
    (A.split_r md_bm_region (US.mul md_count 4sz))
    4sz;
  zf_u64_slice (A.asel (A.split_r md_bm_region (US.mul md_count 4sz)) h0) 0 (US.v 4sz);
  zf_u64_slice (A.asel (A.split_r md_bm_region (US.mul md_count 4sz)) h0) (US.v 4sz) (A.length (A.split_r md_bm_region (US.mul md_count 4sz)));
  pack_md_bm_array md_bm_region md_count;
  let x1 = A.split_r (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz in
  let x2 = A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz))
    (A.varray (A.split_r md_bm_region (US.mul (US.add md_count 1sz) 4sz)))

let md_region_mon_split
  (#opened:_)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhostT unit opened
  (A.varray (A.split_r md_region md_count))
  (fun _ ->
    A.varray (md_array md_region md_count) `star`
    A.varray (A.split_r md_region (US.add md_count 1sz))
  )
  =
  A.ghost_split
    (A.split_r md_region md_count)
    1sz;
  pack_md_array md_region md_count;
  let x1 = A.split_r (A.split_r md_region md_count) 1sz in
  let x2 = A.split_r md_region (US.add md_count 1sz) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r md_region md_count) 1sz))
    (A.varray (A.split_r md_region (US.add md_count 1sz)))

open SteelVRefineDep

#restart-solver

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_slab_aux_1_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1: US.t{US.v idx1 < US.v md_count_v})
  (idx2 idx3 idx4: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4;
  let idx1' = AL.remove1 #pred1 #pred2 #pred3 #pred4
    (A.split_l md_region md_count_v)
    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3)) (G.hide (US.v idx4)) idx1 in
  AL.insert2 #pred1 #pred2 #pred3
    (A.split_l md_region md_count_v)
    idx2 (G.hide (US.v idx1')) (G.hide (US.v idx3)) (G.hide (US.v idx4)) idx1 1ul;
  write r1 idx1';
  write r2 idx1;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1') (US.v idx1) (US.v idx3) (US.v idx4)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1') (US.v idx1) (US.v idx3) (US.v idx4) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
    idx1' idx1 idx3 idx4

inline_for_extraction noextract
let allocate_slab_aux_1_full
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1: US.t{US.v idx1 < US.v md_count_v})
  (idx2 idx3 idx4: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
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
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4;
  let idx1' = AL.remove1 #pred1 #pred2 #pred3 #pred4
    (A.split_l md_region md_count_v)
    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3)) (G.hide (US.v idx4)) idx1 in
  AL.insert3 #pred1 #pred2 #pred3
    (A.split_l md_region md_count_v)
    idx3 (G.hide (US.v idx1')) (G.hide (US.v idx2)) (G.hide (US.v  idx4)) idx1 2ul;
  write r1 idx1';
  write r3 idx1;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1') (US.v idx2) (US.v idx1) (US.v idx4)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1') (US.v idx2) (US.v idx1) (US.v idx4) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
    idx1' idx2 idx1 idx4

inline_for_extraction noextract
let allocate_slab_aux_1
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
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
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun _ r h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    ) in
    md_count_v == dfst blob1 /\
    A.length r == U32.v size_class
  )
  =
  (**) ALG.lemma_head1_in_bounds pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    idx1 (US.v idx2) (US.v idx3) (US.v idx4);
  (**) starseq_unpack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx1);

  (**) ALG.lemma_head1_implies_pred1 pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4;

  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in

  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v idx1);
  (**) SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx1);
  (**) change_equal_slprop
     (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx1)))
     (p_empty size_class (md_bm_array md_bm_region idx1, slab_array slab_region idx1));

  (**) p_empty_unpack size_class
     (md_bm_array md_bm_region idx1, slab_array slab_region idx1)
     (md_bm_array md_bm_region idx1, slab_array slab_region idx1);
  let r = allocate_slot size_class
    (md_bm_array md_bm_region idx1)
    (slab_array slab_region idx1)
  in
  let cond = allocate_slab_aux_cond size_class
    (md_bm_array md_bm_region idx1)
    (slab_array slab_region idx1)
  in
  if cond then (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 2ul;
    allocate_slab_aux_1_full size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 idx2 idx3 idx4;
    return r
  ) else (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 1ul;
    allocate_slab_aux_1_partial size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 idx2 idx3 idx4;
    return r
  )

#restart-solver

inline_for_extraction noextract
let allocate_slab_aux_2_full
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t{US.v idx2 < US.v md_count_v})
  (idx3 idx4: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4;
  let idx2' = AL.remove2 #pred1 #pred2 #pred3 #pred4
    (A.split_l md_region md_count_v)
    (G.hide (US.v idx1)) idx2 (G.hide (US.v idx3)) (G.hide (US.v idx4)) idx2 in
  AL.insert3 #pred1 #pred2 #pred3
    (A.split_l md_region md_count_v)
    idx3 (G.hide (US.v idx1)) (G.hide (US.v idx2')) (G.hide (US.v idx4)) idx2 2ul;
  write r2 idx2';
  write r3 idx2;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2') (US.v idx2) (US.v idx4)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2') (US.v idx2) (US.v idx4) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
    idx1 idx2' idx2 idx4

inline_for_extraction noextract
let allocate_slab_aux_2_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t{US.v idx2 < US.v md_count_v})
  (idx3 idx4: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
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
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    ) in
    md_count_v == dfst blob1)
  =
  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3 r4
    md_count_v md_region_lv
    idx1 idx2 idx3 idx4

inline_for_extraction noextract
let allocate_slab_aux_2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
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
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun _ r h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    ) in
    md_count_v == dfst blob1 /\
    A.length r == U32.v size_class
  )
  =
  (**) ALG.lemma_head2_in_bounds pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) idx2 (US.v idx3) (US.v idx4);
  (**) starseq_unpack_s
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx2);

  (**) ALG.lemma_head2_implies_pred2 pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    idx1 idx2 idx3 idx4;

  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in

  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v idx2);
  (**) SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx2);
  (**) change_equal_slprop
     (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx2)))
     (p_partial size_class (md_bm_array md_bm_region idx2, slab_array slab_region idx2));
  (**) p_partial_unpack size_class
     (md_bm_array md_bm_region idx2, slab_array slab_region idx2)
     (md_bm_array md_bm_region idx2, slab_array slab_region idx2);

  let r = allocate_slot size_class
    (md_bm_array md_bm_region idx2)
    (slab_array slab_region idx2)
  in
  let cond = allocate_slab_aux_cond size_class
    (md_bm_array md_bm_region idx2)
    (slab_array slab_region idx2)
  in
  if cond then (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx2 2ul;
    allocate_slab_aux_2_full size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 idx2 idx3 idx4;
    return r
  ) else (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx2 1ul;
    assert (Seq.upd (G.reveal md_region_lv) (US.v idx2) 1ul `Seq.equal` md_region_lv);
    (**) starseq_weakening
      #_
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 1ul))
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
      (SeqUtils.init_us_refined (US.v md_count_v));
    allocate_slab_aux_2_partial size_class
      slab_region md_bm_region md_region md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 idx2 idx3 idx4;
    return r
  )

#push-options "--fuel 0 --ifuel 0"
let empty_md_is_properly_zeroed
  (size_class: sc)
  : Lemma
  (slab_vprop_aux2 size_class (Seq.create 4 0UL))
  =
  let zero_to_vec_lemma2 (i:nat{i < 64})
    : Lemma
    (FU.nth (FU.zero 64) i = false)
    =
    FU.zero_to_vec_lemma #64 i in
  let s0 = Seq.create 4 0UL in
  let bm = Bitmap4.array_to_bv2 #4 s0 in
  let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
  assert (U64.v (Seq.index s0 0) == FU.zero 64);
  array_to_bv_slice #4 s0 0;
  Classical.forall_intro (zero_to_vec_lemma2);
  Seq.lemma_eq_intro (Seq.slice bm 0 64) (Seq.create 64 false);
  zf_b_slice (Seq.slice bm 0 64) 0 (64 - U32.v bound2)
#pop-options

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
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (v: US.t{US.v v + US.v guard_pages_interval <= US.v metadata_max})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    right_vprop slab_region md_bm_region md_region v
  )) m)
  (ensures SM.interp (hp_of (
    (A.varray (A.split_r slab_region (US.mul v (u32_to_sz page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul v 4sz))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region v)
  )) m /\
  sel_of (
    (A.varray (A.split_r slab_region (US.mul v (u32_to_sz page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul v 4sz))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region v)
  ) m
  ==
  sel_of (right_vprop slab_region md_bm_region md_region v) m
  )
  = ()

let right_vprop_sl_lemma2
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (v: US.t{US.v v <= US.v metadata_max})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    (A.varray (A.split_r slab_region (US.mul v (u32_to_sz page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul v 4sz))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region v)
  )) m)
  (ensures SM.interp (hp_of (
    right_vprop slab_region md_bm_region md_region v
  )) m /\
  sel_of (
    (A.varray (A.split_r slab_region (US.mul v (u32_to_sz page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul v 4sz))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region v)
  ) m
  ==
  sel_of (right_vprop slab_region md_bm_region md_region v) m
  )
  = ()

#restart-solver

#push-options "--print_implicits"

// Extension function, auxiliar
inline_for_extraction noextract
let allocate_slab_aux_3_1_varraylist
  (#opened: _)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (idx1 idx2 idx3 idx4: US.t)
  : SteelGhost unit opened
  (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) `star`
  A.varray (A.split_l (A.split_r md_region md_count_v) guard_pages_interval))
  (fun _ -> AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4))
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    //US.v md_count_v <> AL.null /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4))
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h1 in
    Seq.length gs1 == US.v md_count_v + US.v guard_pages_interval /\
    Seq.slice gs1 0 (US.v md_count_v) == gs0 /\
    ALG.partition #AL.status (Seq.slice gs1 0 (US.v md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) /\
    (forall (j:nat{0 <= j /\ j < US.v guard_pages_interval}).
      ~ (ALG.mem_all #AL.status (US.v md_count_v + j) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs1)
    )
  )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  AL.extend_aux guard_pages_interval
    md_region
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
    md_count_v
    0ul;
  let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (Seq.slice gs1 0 (US.v md_count_v)) `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs0);
  assume (
    forall (j:nat{0 <= j /\ j < US.v guard_pages_interval}).
    ~ (ALG.mem_all #AL.status (US.v md_count_v + j) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs1)
  )

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
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  : SteelGhost unit opened
  (
    A.varray (A.split_r slab_region (US.mul md_count_v (u32_to_sz page_size))) `star`
    A.varray (A.split_r md_bm_region (US.mul md_count_v 4sz)) `star`
    A.varray (A.split_r md_region md_count_v)
  )
  (fun _ ->
    ((A.varray (A.split_r slab_region
      (US.mul (US.add md_count_v guard_pages_interval) (u32_to_sz page_size))) `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region
      (US.mul (US.add md_count_v guard_pages_interval) 4sz)) `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region
      (US.add md_count_v guard_pages_interval))) `star`
    A.varray (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size))) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz)) `star`
    A.varray (A.split_l
      (A.split_r md_region
        md_count_v)
        guard_pages_interval)
  )
  (requires fun h0 ->
    zf_u8 (A.asel
      (A.split_r slab_region (US.mul md_count_v (u32_to_sz page_size)))
      h0
    ) /\
    zf_u64 (A.asel
      (A.split_r md_bm_region (US.mul md_count_v 4sz))
      h0
    )
  )
  (ensures fun _ _ h1 ->
    zf_u64 (A.asel
      (A.split_l
        (A.split_r md_bm_region
          (US.mul md_count_v 4sz))
          (US.mul guard_pages_interval 4sz)) h1)
  )
  =
  let slab_region0 = gget (A.varray (A.split_r slab_region (US.mul md_count_v (u32_to_sz page_size)))) in
  let md_bm_region0 = gget (A.varray (A.split_r md_bm_region (US.mul md_count_v 4sz))) in
  zf_u8_split slab_region0 (US.v guard_pages_interval * U32.v page_size);
  zf_u64_split md_bm_region0 (US.v guard_pages_interval * 4);
  A.ghost_split
    (A.split_r slab_region (US.mul md_count_v (u32_to_sz page_size)))
    (US.mul guard_pages_interval (u32_to_sz page_size));
  A.ghost_split
    (A.split_r md_bm_region (US.mul md_count_v 4sz))
    (US.mul guard_pages_interval 4sz);
  A.ghost_split
    (A.split_r md_region md_count_v)
    guard_pages_interval;
  split_r_r_mul md_count_v guard_pages_interval
    (u32_to_sz page_size) slab_region;
  split_r_r_mul md_count_v guard_pages_interval
    4sz md_bm_region;
  split_r_r
    md_count_v
    guard_pages_interval
    md_region;
  intro_vrefine
    (A.varray (A.split_r slab_region
      (US.mul (US.add md_count_v guard_pages_interval) (u32_to_sz page_size))))
    zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region
      (US.mul (US.add md_count_v guard_pages_interval) 4sz)))
    zf_u64

let allocate_slab_aux_3_1_right
  (#opened: _)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  : SteelGhost unit opened
  (
    right_vprop slab_region md_bm_region md_region md_count_v
  )
  (fun _ ->
    right_vprop slab_region md_bm_region md_region (md_count_v `US.add` guard_pages_interval) `star`
    A.varray (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size))) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz)) `star`
    A.varray (A.split_l
      (A.split_r md_region
        md_count_v)
        guard_pages_interval)
  )
  (requires fun _ -> True)
  (ensures fun _ _ h1 ->
    zf_u64 (A.asel
      (A.split_l
        (A.split_r md_bm_region
          (US.mul md_count_v 4sz))
          (US.mul guard_pages_interval 4sz)) h1)
  )
  =
  change_slprop_rel
    (right_vprop slab_region md_bm_region md_region md_count_v)
    ((A.varray (A.split_r slab_region (US.mul md_count_v (u32_to_sz page_size)))
     `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul md_count_v 4sz))
     `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region md_count_v))
    (fun x y -> x == y)
    (fun m -> right_vprop_sl_lemma1 slab_region md_bm_region md_region md_count_v m);
  elim_vrefine
    (A.varray (A.split_r slab_region (US.mul md_count_v (u32_to_sz page_size))))
    zf_u8;
  elim_vrefine
    (A.varray (A.split_r md_bm_region (US.mul md_count_v 4sz)))
    zf_u64;
  allocate_slab_aux_3_1_right_aux
    slab_region md_bm_region md_region md_count_v;
  change_slprop_rel
    ((A.varray (A.split_r slab_region (US.mul (US.add md_count_v guard_pages_interval) (u32_to_sz page_size)))
     `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul (US.add md_count_v guard_pages_interval) 4sz))
     `vrefine` zf_u64) `star`
   A.varray (A.split_r md_region (US.add md_count_v guard_pages_interval)))
    (right_vprop slab_region md_bm_region md_region (US.add md_count_v guard_pages_interval))
    (fun x y -> x == y)
    (fun m -> right_vprop_sl_lemma2 slab_region md_bm_region md_region (US.add md_count_v guard_pages_interval) m)

// Extension function, should be SteelGhost
inline_for_extraction noextract
let allocate_slab_aux_3_1
  (#opened: _)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (idx1 idx2 idx3 idx4: US.t)
  : SteelGhost unit opened
  (
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4))
  )
  (fun _ ->
    right_vprop slab_region md_bm_region md_region (md_count_v `US.add` guard_pages_interval) `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
    A.varray (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size))) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    //US.v md_count_v <> AL.null /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4))
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h1 in
    Seq.length gs1 == US.v md_count_v + US.v guard_pages_interval /\
    Seq.slice gs1 0 (US.v md_count_v) == gs0 /\
    ALG.partition #AL.status (Seq.slice gs1 0 (US.v md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) /\
    (forall (j:nat{0 <= j /\ j < US.v guard_pages_interval}).
      ~ (ALG.mem_all #AL.status (US.v md_count_v + j) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs1)) /\
    zf_u64 (A.asel
      (A.split_l
        (A.split_r md_bm_region
          (US.mul md_count_v 4sz))
          (US.mul guard_pages_interval 4sz)) h1)
  )
  =
  allocate_slab_aux_3_1_right
    slab_region md_bm_region md_region md_count_v;
  allocate_slab_aux_3_1_varraylist
    md_region md_count_v idx1 idx2 idx3 idx4;
  let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  //TODO: extend_aux should propagate some facts about
  // ptrs_in ... (Seq.slice gs1 0 (US.v md_count_v))
  // ==
  // ptrs_in ... gs1
  assert (forall (j:nat{0 <= j /\ j < US.v guard_pages_interval}).
      ~ (ALG.mem_all #AL.status (US.v md_count_v + j) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs1))

#restart-solver

module FS = FStar.FiniteSet.Base

// Insertion function
inline_for_extraction noextract
let allocate_slab_aux_3_2
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (idx1 idx2 idx3 idx4: US.t)
  : Steel unit
  (
    AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (fun _ ->
    AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v md_count_v + US.v guard_pages_interval - 2)
      (US.v idx2) (US.v idx3)
      (US.v md_count_v + US.v guard_pages_interval - 1)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
  //  //US.v md_count_v <> AL.null /\
    ALG.partition #AL.status (Seq.slice gs0 0 (US.v md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) /\
    (forall (j:nat{0 <= j /\ j < US.v guard_pages_interval}).
      ~ (ALG.mem_all #AL.status (US.v md_count_v + j) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs0))
  )
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v md_count_v + US.v guard_pages_interval - 2)
      (US.v idx2) (US.v idx3)
      (US.v md_count_v + US.v guard_pages_interval - 1)
      h1 in
    ALG.ptrs_in #AL.status
      (US.v md_count_v + US.v guard_pages_interval - 2) gs1
    == FS.union
      (ALG.set (US.v md_count_v) (US.v md_count_v + US.v guard_pages_interval - 1))
      (ALG.ptrs_in #AL.status (US.v idx1) gs0) /\
    ALG.ptrs_in #AL.status (US.v idx2) gs1
    == ALG.ptrs_in #AL.status (US.v idx2) gs0 /\
    ALG.ptrs_in #AL.status (US.v idx3) gs1
    == ALG.ptrs_in #AL.status (US.v idx3) gs0 /\
    ALG.ptrs_in #AL.status
      (US.v md_count_v + US.v guard_pages_interval - 1) gs1
    == FS.insert
      (US.v md_count_v + US.v guard_pages_interval - 1)
      (ALG.ptrs_in #AL.status (US.v idx4) gs0) /\
    ALG.dataify gs1
    == Seq.append
      (Seq.slice (ALG.dataify gs0) 0 (US.v md_count_v))
      (Seq.append
        (Seq.create (US.v guard_pages_interval - 1) 0ul)
        (Seq.create 1 3ul)
      ) /\
    ALG.partition #AL.status gs1
      (US.v md_count_v + US.v guard_pages_interval - 2)
      (US.v idx2) (US.v idx3)
      (US.v md_count_v + US.v guard_pages_interval - 1)
    /\
    True
  )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  assert (~ (ALG.mem_all #AL.status (US.v md_count_v + 0) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs0));
  assert (~ (ALG.mem_all #AL.status (US.v md_count_v) (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) gs0));
  AL.insert1
    (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
    idx1 (US.v idx2) (US.v idx3) (US.v idx4)
    md_count_v
    0ul;
  AL.extend_insert
    guard_pages_interval
    (US.sub guard_pages_interval 2sz)
    md_region
    idx2 idx3 idx4
    md_count_v
    0ul;
  let gs1 = gget (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v md_count_v + US.v (US.sub guard_pages_interval 2sz))
      (US.v idx2) (US.v idx3) (US.v idx4)) in
  assert (forall (j:nat{US.v (US.sub guard_pages_interval 2sz) + 1 <= j /\ j < US.v guard_pages_interval}).
      ~ (ALG.mem_all #AL.status (US.v md_count_v + j)
      (US.v md_count_v + US.v (US.sub guard_pages_interval 2sz))
      (US.v idx2) (US.v idx3) (US.v idx4) gs1));
  assume (~ (ALG.mem_all #AL.status
    (US.v md_count_v + US.v (US.sub guard_pages_interval 2sz) + 1)
    (US.v md_count_v + US.v (US.sub guard_pages_interval 2sz))
    (US.v idx2) (US.v idx3) (US.v idx4) gs0));
  assert (
    US.v (US.sub (US.add md_count_v guard_pages_interval) 1sz)
    ==
    US.v md_count_v + US.v (US.sub guard_pages_interval 2sz) + 1
  );
  assume (~ (ALG.mem_all #AL.status
    (US.v (US.sub (US.add md_count_v guard_pages_interval) 1sz))
    (US.v md_count_v + US.v (US.sub guard_pages_interval 2sz))
    (US.v idx2) (US.v idx3) (US.v idx4)
    gs1
  ));
  AL.insert4
    (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
    idx4
    (US.v md_count_v + US.v (US.sub guard_pages_interval 2sz))
    (US.v idx2) (US.v idx3)
    (US.sub (US.add md_count_v guard_pages_interval) 1sz)
    3ul;
  change_slprop_rel
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v md_count_v + US.v (US.sub guard_pages_interval 2sz))
      (US.v idx2) (US.v idx3)
      (US.v (US.sub (US.add md_count_v guard_pages_interval) 1sz)))
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v md_count_v + US.v guard_pages_interval - 2)
      (US.v idx2) (US.v idx3)
      (US.v md_count_v + US.v guard_pages_interval - 1))
    (fun x y -> x == y)
    (fun _ -> admit ());
  admit ()

let lemma_slab_aux_3_3_1
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : Lemma
    (let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
     let f2 = f size_class slab_region md_bm_region
      (US.add md_count_v guard_pages_interval)
      (Seq.append md_region_lv (Seq.append
        (Seq.create (US.v guard_pages_interval - 1) 0ul)
        (Seq.create 1 3ul))) in
     let s1 = SeqUtils.init_us_refined (US.v md_count_v) in
     let s2 = Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval))) 0 (US.v md_count_v) in
     forall (k:nat{k < Seq.length s1}). f1 (Seq.index s1 k) == f2 (Seq.index s2 k))
  =
  let md_region_lv' = Seq.append
    md_region_lv
    (Seq.append
      (Seq.create (US.v guard_pages_interval - 1) 0ul)
      (Seq.create 1 3ul)) in
  let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
  let f2 = f size_class slab_region md_bm_region (US.add md_count_v guard_pages_interval) md_region_lv' in
  let s1 = SeqUtils.init_us_refined (US.v md_count_v) in
  let s2 = Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval))) 0 (US.v md_count_v) in

  let aux (k:nat{k < Seq.length s1}) : Lemma (f1 (Seq.index s1 k) == f2 (Seq.index s2 k))
    = SeqUtils.init_us_refined_index (US.v md_count_v) k;
      SeqUtils.init_us_refined_index (US.v (US.add md_count_v guard_pages_interval)) k
  in Classical.forall_intro aux

//let lemma_slab_aux_3_3_bis
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
//  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
//  (md_count_v: US.t{US.v md_count_v < US.v metadata_max})
//  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
//  : Lemma
//    (p_empty size_class (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v) ==
//     f size_class slab_region md_bm_region
//      (US.add md_count_v 1sz)
//      (Seq.append md_region_lv (Seq.create 1 0ul))
//      (Seq.index (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz))) (US.v md_count_v)))
//  = SeqUtils.init_us_refined_index (US.v (US.add md_count_v 1sz)) (US.v md_count_v)

#restart-solver

open Helpers



let allocate_slab_aux_3_3_1 (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
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
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval))) 0 (US.v md_count_v))
  )
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  lemma_slab_aux_3_3_1 size_class slab_region md_bm_region md_region md_count_v md_region_lv;

  starseq_weakening_ref
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f size_class slab_region md_bm_region
      (US.add md_count_v guard_pages_interval)
      (Seq.append md_region_lv (Seq.append
        (Seq.create (US.v guard_pages_interval - 1) 0ul)
        (Seq.create 1 3ul))))
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region
      (US.add md_count_v guard_pages_interval)
      (Seq.append md_region_lv (Seq.append
        (Seq.create (US.v guard_pages_interval - 1) 0ul)
        (Seq.create 1 3ul))))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval))) 0 (US.v md_count_v))


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

let allocate_slab_aux_3_3_2_1_aux2 (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (i: US.t{0 < US.v i /\ US.v i < US.v guard_pages_interval})
  : SteelGhost unit opened
  (
    A.varray (A.split_r (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul i (u32_to_sz page_size)))
        (US.mul (US.sub i 1sz) (u32_to_sz page_size))) `star`
    A.varray (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul i 4sz))
        (US.mul (US.sub i 1sz) 4sz))
  )
  (fun _ ->
    f size_class slab_region md_bm_region
      (US.add md_count_v guard_pages_interval)
      (Seq.append md_region_lv (Seq.append
        (Seq.create (US.v guard_pages_interval - 1) 0ul)
        (Seq.create 1 3ul)))
      (Seq.index (SeqUtils.init_us_refined
        (US.v (US.add md_count_v guard_pages_interval)))
        (US.v (US.add md_count_v (US.sub i 1sz))))
  )
  //  starseq
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
  //    (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
  //      (US.v md_count_v + US.v i - 1)
  //      (US.v md_count_v + US.v i)
  //    )
  //)
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul i 4sz))
        (US.mul (US.sub i 1sz) 4sz)) h0)
  )
  (ensures fun _ _ _ -> True)
  =
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_r (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul i (u32_to_sz page_size)))
        (US.mul (US.sub i 1sz) (u32_to_sz page_size))))
    (A.ptr_of (slab_array slab_region (US.add md_count_v (US.sub i 1sz))));
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul i 4sz))
        (US.mul (US.sub i 1sz) 4sz)))
    (A.ptr_of (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz))));
  change_equal_slprop
    (A.varray (A.split_r (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul i (u32_to_sz page_size)))
        (US.mul (US.sub i 1sz) (u32_to_sz page_size))))
    (A.varray (slab_array slab_region (US.add md_count_v (US.sub i 1sz))));
  change_equal_slprop
    (A.varray (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul i 4sz))
        (US.mul (US.sub i 1sz) 4sz)))
    (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz))));

  let md_as_seq = gget (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)))) in
  assert (G.reveal md_as_seq == Seq.create 4 0UL);
  A.ghost_split (slab_array slab_region (US.add md_count_v (US.sub i 1sz))) 0sz;
  slab_to_slots size_class (A.split_r (slab_array slab_region (US.add md_count_v (US.sub i 1sz))) 0sz);
  empty_md_is_properly_zeroed size_class;
  intro_slab_vprop size_class
    (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)))
    (Seq.create 4 0UL)
    (slab_array slab_region (US.add md_count_v (US.sub i 1sz)));
  p_empty_pack size_class
    (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)),
    slab_array slab_region (US.add md_count_v (US.sub i 1sz)))
    (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)),
    slab_array slab_region (US.add md_count_v (US.sub i 1sz)));
  SeqUtils.init_us_refined_index
    (US.v (US.add md_count_v guard_pages_interval))
    (US.v (US.add md_count_v (US.sub i 1sz)));
  change_equal_slprop
    (p_empty size_class
      (md_bm_array md_bm_region (US.add md_count_v (US.sub i 1sz)),
      slab_array slab_region (US.add md_count_v (US.sub i 1sz))))
    (f size_class slab_region md_bm_region
      (US.add md_count_v guard_pages_interval)
      (Seq.append md_region_lv (Seq.append
        (Seq.create (US.v guard_pages_interval - 1) 0ul)
        (Seq.create 1 3ul)))
      (Seq.index (SeqUtils.init_us_refined
        (US.v (US.add md_count_v guard_pages_interval)))
        (US.v (US.add md_count_v (US.sub i 1sz)))))

//TODO: some work left, should be reasonable
let rec allocate_slab_aux_3_3_2_1_aux (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (i: US.t{US.v i < US.v guard_pages_interval})
  : SteelGhost unit opened
  (
    A.varray (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul i (u32_to_sz page_size))) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul i 4sz))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
        (US.v md_count_v)
        (US.v md_count_v + US.v i)
      )
  )
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
      (US.mul i 4sz)) h0)
  )
  (ensures fun _ _ _ -> True)
  (decreases US.v i)
  =
  match US.v i with
  | 0 ->
    //normalization to emp
    sladmit ()
  | _ ->
    A.ghost_split (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul i (u32_to_sz page_size)))
      (US.mul (US.sub i 1sz) (u32_to_sz page_size));
    let s0 = gget (A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul i 4sz))) in
    zf_u64_split s0 (US.v (US.mul (US.sub i 1sz) 4sz));
    A.ghost_split (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul i 4sz))
      (US.mul (US.sub i 1sz) 4sz);
    split_l_l_mul
      (US.sub i 1sz)
      i
      (u32_to_sz page_size)
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)));
    split_l_l_mul
      (US.sub i 1sz)
      i
      4sz
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz));
    allocate_slab_aux_3_3_2_1_aux size_class
      slab_region md_bm_region md_region
      md_count_v md_region_lv
      (US.sub i 1sz);
    //dedicated lemma
    allocate_slab_aux_3_3_2_1_aux2 size_class
      slab_region md_bm_region md_region
      md_count_v md_region_lv
      i;
    //close starseq
    //TODO: starseq_add_singleton_s not working
    sladmit ()

let allocate_slab_aux_3_3_2_1 (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : SteelGhost unit opened
  (
    A.varray (A.split_l (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size)))
      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))) `star`
    A.varray (A.split_l (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
      (US.mul (US.sub guard_pages_interval 1sz) 4sz))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
        (US.v md_count_v)
        (US.v md_count_v + US.v guard_pages_interval - 1)
      )
  )
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_l (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
      (US.mul (US.sub guard_pages_interval 1sz) 4sz)) h0)
  )
  (ensures fun _ _ _ -> True)
  =
  split_l_l_mul
    (US.sub guard_pages_interval 1sz)
    guard_pages_interval
    (u32_to_sz page_size)
    (A.split_r slab_region
      (US.mul md_count_v (u32_to_sz page_size)));
  split_l_l_mul
    (US.sub guard_pages_interval 1sz)
    guard_pages_interval
    4sz
    (A.split_r md_bm_region
      (US.mul md_count_v 4sz));
  allocate_slab_aux_3_3_2_1_aux size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv
    (US.sub guard_pages_interval 1sz);
  change_slprop_rel
    (starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
        (US.v md_count_v)
        (US.v md_count_v + US.v (US.sub guard_pages_interval 1sz))))
    (starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
        (US.v md_count_v)
        (US.v md_count_v + US.v guard_pages_interval - 1)))
    (fun x y -> x == y)
    (fun _ -> assert_norm (
      US.v (US.sub guard_pages_interval 1sz)
      ==
      US.v guard_pages_interval - 1
    ))

open Guards

//TODO: this function is the one that will set the trap
//use slab_to_slots as above + mprotect wrapper
let allocate_slab_aux_3_3_2_2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : Steel unit
  (
    A.varray (A.split_r (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size)))
      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))) `star`
    A.varray (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
      (US.mul (US.sub guard_pages_interval 1sz) 4sz))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
        (US.v md_count_v + US.v guard_pages_interval - 1)
        (US.v md_count_v + US.v guard_pages_interval)
      )
  )
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
      (US.mul (US.sub guard_pages_interval 1sz) 4sz)) h0))
  (ensures fun h0 _ h1 -> True)
  =
  //normalization
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_r (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size)))
      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))))
    (A.ptr_of (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
  change_equal_slprop
    (A.varray(A.split_r (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size)))
      (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz  page_size))))
    (A.varray (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
      (US.mul (US.sub guard_pages_interval 1sz) 4sz)))
    (A.ptr_of (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
  change_equal_slprop
    (A.varray (A.split_r (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
      (US.mul (US.sub guard_pages_interval 1sz) 4sz)))
    (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz))));
  let md_as_seq = gget (A.varray (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)))) in
  assert (G.reveal md_as_seq == Seq.create 4 0UL);
  A.ghost_split (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz))) 0sz;
  slab_to_slots size_class (A.split_r (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz))) 0sz);
  empty_md_is_properly_zeroed size_class;
  intro_slab_vprop size_class
    (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)))
    (Seq.create 4 0UL)
    (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)));
  mmap_trap size_class
    (slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)))
    (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)))
    (u32_to_sz page_size);
  p_guard_pack size_class
    (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)),
    slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)))
    (md_bm_array md_bm_region (US.add md_count_v (US.sub guard_pages_interval 1sz)),
    slab_array slab_region (US.add md_count_v (US.sub guard_pages_interval 1sz)));
  //intro guard pages: set the trap
  sladmit ()

let allocate_slab_aux_3_3_2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : Steel unit
  (
    A.varray (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size))) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
        (US.v md_count_v)
        (US.v md_count_v + US.v guard_pages_interval)
      )
  )
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz)) h0)
  )
  (ensures fun _ _ _ -> True)
  =
  let md_bm_region0 = gget (A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))) in
  zf_u64_split md_bm_region0 ((US.v guard_pages_interval - 1) * 4);
  A.ghost_split
    (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size)))
    (US.mul (US.sub guard_pages_interval 1sz) (u32_to_sz page_size));
  A.ghost_split
    (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz))
    (US.mul (US.sub guard_pages_interval 1sz) 4sz);
  allocate_slab_aux_3_3_2_1 size_class
    slab_region md_bm_region md_region md_count_v md_region_lv;
  allocate_slab_aux_3_3_2_2 size_class
    slab_region md_bm_region md_region md_count_v md_region_lv;
  //TODO: starseq_append_pack
  sladmit ()

let allocate_slab_aux_3_3
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  : Steel unit
  (
    A.varray (A.split_l
      (A.split_r slab_region
        (US.mul md_count_v (u32_to_sz page_size)))
        (US.mul guard_pages_interval (u32_to_sz page_size))) `star`
    A.varray (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
  )
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_l
      (A.split_r md_bm_region
        (US.mul md_count_v 4sz))
        (US.mul guard_pages_interval 4sz)) h0)
  )
  (ensures fun _ _ _ -> True)
  =
  allocate_slab_aux_3_3_1 size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv;
  allocate_slab_aux_3_3_2 size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv;
  rewrite_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval))) 0 (US.v md_count_v)) `star`
     starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (Seq.slice (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval))) (US.v md_count_v) (US.v md_count_v + US.v guard_pages_interval)))
    (starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval))))
    (fun _ -> admit ())
  // TODO: add missing starseq lemma
  // using map_seq_append should work

  //// required for selector equality propagation
  //let md_as_seq = gget (A.varray (md_bm_array md_bm_region md_count_v)) in
  //assert (G.reveal md_as_seq == Seq.create 4 0UL);
  //A.ghost_split (slab_array slab_region md_count_v) 0sz;
  //slab_to_slots size_class (A.split_r (slab_array slab_region md_count_v) 0sz);
  //empty_md_is_properly_zeroed size_class;
  //intro_slab_vprop size_class
  //  (md_bm_array md_bm_region md_count_v)
  //  (Seq.create 4 0UL)
  //  (slab_array slab_region md_count_v);
  //p_empty_pack size_class
  //  (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v)
  //  (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v);

  //SeqUtils.init_us_refined_index (US.v (US.add md_count_v 1sz)) (US.v md_count_v);
  //change_equal_slprop
  //  (p_empty size_class (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v))
  //  (f size_class slab_region md_bm_region
  //    (US.add md_count_v 1sz)
  //    (Seq.append md_region_lv (Seq.create 1 0ul))
  //    (Seq.index (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz))) (US.v md_count_v)));

  //starseq_add_singleton_s
  //  #_
  //  #(pos:US.t{US.v pos < US.v (US.add md_count_v 1sz)})
  //  #(t size_class)
  //  (f size_class slab_region md_bm_region
  //    (US.add md_count_v 1sz)
  //    (Seq.append md_region_lv (Seq.create 1 0ul)))
  //  (f_lemma size_class slab_region md_bm_region
  //    (US.add md_count_v 1sz)
  //    (Seq.append md_region_lv (Seq.create 1 0ul)))
  //  (SeqUtils.init_us_refined (US.v (US.add md_count_v 1sz)))
  //  (US.v md_count_v)

#restart-solver

#push-options "--z3rlimit 100"
inline_for_extraction noextract
let allocate_slab_aux_3
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v + US.v guard_pages_interval <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4: US.t)
  : Steel unit//US.t
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    right_vprop slab_region md_bm_region md_region (US.add md_count_v guard_pages_interval) `star`
    AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v md_count_v + US.v guard_pages_interval - 2)
      (US.v idx2) (US.v idx3)
      (US.v md_count_v + US.v guard_pages_interval - 1) `star`
    starseq
      #(pos:US.t{US.v pos < US.v (US.add md_count_v guard_pages_interval)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (f_lemma size_class slab_region md_bm_region
        (US.add md_count_v guard_pages_interval)
        (Seq.append md_region_lv (Seq.append
          (Seq.create (US.v guard_pages_interval - 1) 0ul)
          (Seq.create 1 3ul))))
      (SeqUtils.init_us_refined (US.v (US.add md_count_v guard_pages_interval)))
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    US.v md_count_v <> AL.null /\
    md_count_v == sel md_count h0 /\
    US.v md_count_v < US.v metadata_max /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1 ) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun h0 _ h1 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    let gs1 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (md_count_v `US.add` guard_pages_interval))
      (US.v md_count_v + US.v guard_pages_interval - 2)
      (US.v idx2) (US.v idx3)
      (US.v md_count_v + US.v guard_pages_interval - 1) h1 in
    //idx1' <> AL.null_ptr /\
    //US.v (sel md_count h1) <> AL.null /\
    sel r1 h1 == US.sub (US.add md_count_v guard_pages_interval) 2sz /\
    sel r2 h1 == sel r2 h0 /\
    sel r3 h1 == sel r3 h0 /\
    sel r4 h1 == US.sub (US.add md_count_v guard_pages_interval)  1sz /\
    sel md_count h0 = md_count_v /\
    sel md_count h1 = US.add md_count_v guard_pages_interval /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.dataify gs1
    == Seq.append
      (G.reveal md_region_lv)
      (Seq.append
        (Seq.create (US.v guard_pages_interval - 1) 0ul)
        (Seq.create 1 3ul)
      ) /\
    ALG.partition #AL.status gs1
      (US.v md_count_v + US.v guard_pages_interval - 2)
      (US.v idx2) (US.v idx3)
      (US.v md_count_v + US.v guard_pages_interval - 1) /\
    True
  )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 pred4
    (A.split_l md_region md_count_v)
    (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) in
  allocate_slab_aux_3_1
    slab_region md_bm_region md_region md_count_v
    idx1 idx2 idx3 idx4;
  allocate_slab_aux_3_2
    md_region md_count_v
    idx1 idx2 idx3 idx4;
  allocate_slab_aux_3_3 size_class
    slab_region md_bm_region md_region md_count_v md_region_lv;

  let v = read md_count in
  write md_count (US.add v guard_pages_interval);
  write r1 (US.sub (US.add v guard_pages_interval) 2sz);
  write r4 (US.sub (US.add v guard_pages_interval) 1sz);
  admit ();

  return ()
#pop-options

module P = Steel.FractionalPermission

#restart-solver

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_slab'
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class (A.split_r slab_region 0sz) md_bm_region md_count_v md_region_lv)
      (f_lemma size_class (A.split_r slab_region 0sz) md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_us_refined (US.v md_count_v)) `star`
    A.varrayp (A.split_l slab_region 0sz) halfp
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    US.v md_count_v <> AL.null /\
    md_count_v == sel md_count h0 /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv
  )
  (ensures fun _ r _ ->
    not (A.is_null r) ==> A.length r == U32.v size_class
  )
  =
  if (idx2 <> AL.null_ptr) then (
    ALG.lemma_head2_in_bounds pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      (US.v idx1) idx2 (US.v idx3) (US.v idx4);
    // Lemma above used to derive
    assert (US.v md_count_v <> AL.null);

    let r = allocate_slab_aux_2 size_class
      (A.split_r slab_region 0sz) md_bm_region md_region
      md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 idx2 idx3 idx4 in
    pack_right_and_refactor_vrefine_dep
      size_class slab_region md_bm_region md_region md_count
      r1 r2 r3 r4 md_count_v;
    A.varrayp_not_null r P.full_perm;
    change_equal_slprop
      (A.varray r)
      (if (A.is_null r) then emp else A.varray r);
    return r
  ) else if (idx1 <> AL.null_ptr) then (
    ALG.lemma_head1_in_bounds pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v)
      idx1 (US.v idx2) (US.v idx3) (US.v idx4);
    // Lemma above used to derive
    assert (US.v md_count_v <> AL.null);

    let r = allocate_slab_aux_1 size_class
      (A.split_r slab_region 0sz) md_bm_region md_region
      md_count r1 r2 r3 r4
      md_count_v md_region_lv idx1 idx2 idx3 idx4 in
    pack_right_and_refactor_vrefine_dep
      size_class slab_region md_bm_region md_region md_count
      r1 r2 r3 r4 md_count_v;
    A.varrayp_not_null r P.full_perm;
    change_equal_slprop
      (A.varray r)
      (if (A.is_null r) then emp else A.varray r);
    return r
  ) else (

    let md_count_v' = read md_count in
    let b = US.lte (US.add md_count_v' guard_pages_interval)  metadata_max in
    if b then (
      allocate_slab_aux_3 size_class
        (A.split_r slab_region 0sz) md_bm_region md_region
        md_count r1 r2 r3 r4
        md_count_v md_region_lv
        idx1 idx2 idx3 idx4;
      sladmit ();
      let r = allocate_slab_aux_1 size_class
        (A.split_r slab_region 0sz) md_bm_region md_region
        md_count r1 r2 r3 r4
        (US.add md_count_v guard_pages_interval)
        (G.hide (Seq.append
          (G.reveal md_region_lv)
          (Seq.append
            (Seq.create (US.v guard_pages_interval - 1) 0ul)
            (Seq.create 1 3ul)
          )))
        (US.sub (US.add md_count_v guard_pages_interval) 2sz)
        idx2 idx3
        (US.sub (US.add md_count_v guard_pages_interval) 1sz) in
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r1 r2 r3 r4 (US.add md_count_v 1sz);
      A.varrayp_not_null r P.full_perm;
      change_equal_slprop
        (A.varray r)
        (if (A.is_null r) then emp else A.varray r);
      return r
    ) else (
      pack_3 size_class
        (A.split_r slab_region 0sz) md_bm_region md_region
        md_count r1 r2 r3 r4
        md_count_v md_region_lv idx1 idx2 idx3 idx4;
      pack_right_and_refactor_vrefine_dep
          size_class slab_region md_bm_region md_region
          md_count
          r1 r2 r3 r4 md_count_v;
      change_equal_slprop
        emp
        (if A.is_null A.null then emp else A.varray A.null);
      return (A.null #U8.t)
    )
  )

#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects"
let allocate_slab
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4: ref US.t)
  : Steel (array U8.t)
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun _ -> True)
  (ensures fun _ r _ ->
    not (A.is_null r) ==> A.length r == U32.v size_class
  )
  =
  let md_count_v
    : G.erased _
    = elim_vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4) in

  let md_count_v_ = read md_count in

  change_equal_slprop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4(G.reveal md_count_v))
    (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region
      r1 r2 r3 r4 md_count_v_ `star`
    right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v_ `star`
    A.varrayp (A.split_l slab_region 0sz) halfp);


  let x
    : G.erased _
    = elim_vdep
    (left_vprop1 md_region r1 r2 r3 r4 md_count_v_)
    (left_vprop_aux size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 r4 md_count_v_) in

  let idxs
    : G.erased _
    = elim_vdep
      (vptr r1 `star` vptr r2 `star` vptr r3 `star` vptr r4)
      (ind_varraylist_aux pred1 pred2 pred3 pred4 (A.split_l md_region md_count_v_))
  in
  let idx1_ = read r1 in
  let idx2_ = read r2 in
  let idx3_ = read r3 in
  let idx4_ = read r4 in

  elim_vrefine
    (ind_varraylist_aux2 pred1 pred2 pred3 pred4 (A.split_l md_region md_count_v_) idxs)
    (ind_varraylist_aux_refinement pred1 pred2 pred3 pred4 (A.split_l md_region md_count_v_) idxs);

  change_slprop_rel
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v_)
      (US.v (fst (fst (fst (G.reveal idxs)))))
      (US.v (snd (fst (fst (G.reveal idxs)))))
      (US.v (snd (fst (G.reveal idxs))))
      (US.v (snd (G.reveal idxs))))
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region md_count_v_)
      (US.v idx1_) (US.v idx2_) (US.v idx3_) (US.v idx4_))
    (fun x y -> x == y)
    (fun _ ->
      assert (fst (fst (fst (G.reveal idxs))) == idx1_);
      assert (snd (fst (fst (G.reveal idxs))) == idx2_);
      assert (snd (fst (G.reveal idxs)) == idx3_);
      assert (snd (G.reveal idxs) = idx4_)
    );

  let x' : Ghost.erased (Seq.lseq AL.status (US.v md_count_v_)) = ALG.dataify (dsnd x) in

  change_equal_slprop
    (left_vprop_aux size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 r4 md_count_v_ x)
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v_})
      #(t size_class)
      (f size_class (A.split_r slab_region 0sz) md_bm_region md_count_v_ x')
      (f_lemma size_class (A.split_r slab_region 0sz) md_bm_region md_count_v_ x')
      (SeqUtils.init_us_refined (US.v md_count_v_)));

  let r = allocate_slab' size_class
    slab_region md_bm_region md_region md_count r1 r2 r3 r4
    md_count_v_ x' idx1_ idx2_ idx3_ idx4_
  in

  return r
