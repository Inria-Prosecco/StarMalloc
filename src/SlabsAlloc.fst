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
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
  (A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))))
  (fun _ ->
    A.varray (slab_array slab_region md_count) `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size)))
  )
  (requires fun h0 ->
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) h0))
  (ensures fun h0 _ h1 ->
    zf_u8 (A.asel (slab_array slab_region md_count) h1) /\
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) h1)
  )
  =
  let h0 = get () in
  A.ghost_split
    (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size)))
    (u32_to_sz page_size);
  zf_u8_slice (A.asel (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) h0) 0 (US.v (u32_to_sz page_size));
  zf_u8_slice (A.asel (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) h0) (US.v (u32_to_sz page_size)) (A.length (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))));
  pack_slab_array slab_region md_count;
  let x1 = A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size) in
  let x2 = A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))))

let md_bm_region_mon_split
  (#opened:_)
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
  (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))))
  (fun _ ->
    A.varray (md_bm_array md_bm_region md_count) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul)))
  )
  (requires fun h0 ->
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) h0))
  (ensures fun h0 _ h1 ->
    zf_u64 (A.asel (md_bm_array md_bm_region md_count) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) h1)
  )
  =
  let h0 = get () in
  A.ghost_split
    (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul)))
    (u32_to_sz 4ul);
  zf_u64_slice (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) h0) 0 (US.v (u32_to_sz 4ul));
  zf_u64_slice (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) h0) (US.v (u32_to_sz 4ul)) (A.length (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))));
  pack_md_bm_array md_bm_region md_count;
  let x1 = A.split_r (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul) in
  let x2 = A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))))

let md_region_mon_split
  (#opened:_)
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhostT unit opened
  (A.varray (A.split_r md_region (u32_to_sz md_count)))
  (fun _ ->
    A.varray (md_array md_region md_count) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
  )
  =
  A.ghost_split
    (A.split_r md_region (u32_to_sz md_count))
    (u32_to_sz 1ul);
  pack_md_array md_region md_count;
  let x1 = A.split_r (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul) in
  let x2 = A.split_r md_region (u32_to_sz (U32.add md_count 1ul)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r md_region (u32_to_sz (md_count))) (u32_to_sz 1ul)))
    (A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul))))

open SteelVRefineDep

#restart-solver

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_slab_aux_1_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t{US.v idx1 < U32.v md_count_v})
  (idx2: US.t)
  (idx3: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0 in
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (US.v idx1) (US.v idx2) (US.v idx3)) in
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 idx2 idx3;
  let idx1' = AL.remove1 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 (Ghost.hide (US.v idx2)) (Ghost.hide (US.v idx3)) idx1 in
  AL.insert2 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx2 (Ghost.hide (US.v idx1')) (Ghost.hide (US.v idx3)) idx1 1ul;
  write r1 idx1';
  write r2 idx1;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (US.v idx1') (US.v idx1) (US.v idx3)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1') (US.v idx1) (US.v idx3) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx1) 1ul))
    idx1' idx1 idx3

inline_for_extraction noextract
let allocate_slab_aux_1_full
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t{US.v idx1 < U32.v md_count_v})
  (idx2: US.t)
  (idx3: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0 in
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 idx2 idx3;
  let idx1' = AL.remove1 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 (Ghost.hide (US.v idx2)) (Ghost.hide (US.v idx3)) idx1 in
  AL.insert3 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx3 (Ghost.hide (US.v idx1')) (Ghost.hide (US.v idx2)) idx1 2ul;
  write r1 idx1';
  write r3 idx1;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (US.v idx1') (US.v idx2) (US.v idx1)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1') (US.v idx2) (US.v idx1) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
    idx1' idx2 idx1

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_slab_aux_1
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun r ->
    A.varray r `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0 in
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob1)
  =
  (**) ALG.lemma_head1_in_bounds pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) idx1 idx2 idx3;
  (**) starseq_unpack_s
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (US.v idx1);

  (**) ALG.lemma_head1_implies_pred1 pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) idx1 idx2 idx3;

  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3
                                (A.split_l md_region (u32_to_sz md_count_v))
                                (US.v idx1) (US.v idx2) (US.v idx3)) in

  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v idx1);
  (**) SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v idx1);
  (**) change_equal_slprop
     (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx1)))
     (p_empty size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx1), slab_array slab_region (US.sizet_to_uint32 idx1)));

  (**) p_empty_unpack size_class
     (md_bm_array md_bm_region (US.sizet_to_uint32 idx1), slab_array slab_region (US.sizet_to_uint32 idx1))
     (md_bm_array md_bm_region (US.sizet_to_uint32 idx1), slab_array slab_region (US.sizet_to_uint32 idx1));
  let r = allocate_slot size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 idx1))
    (slab_array slab_region (US.sizet_to_uint32 idx1))
  in
  let cond = allocate_slab_aux_cond size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 idx1))
    (slab_array slab_region (US.sizet_to_uint32 idx1))
  in
  if cond then (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 2ul;
    allocate_slab_aux_1_full size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3;
    return r
  ) else (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 1ul;
    allocate_slab_aux_1_partial size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3;
    return r
  )
#pop-options

#restart-solver

#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_slab_aux_2_full
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t{US.v idx2 < U32.v md_count_v})
  (idx3: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0 in
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob1)
  =
  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 idx2 idx3;
  let idx2' = AL.remove2 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (Ghost.hide (US.v idx1)) idx2 (Ghost.hide (US.v idx3)) idx2 in
  AL.insert3 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx3 (Ghost.hide (US.v idx1)) (Ghost.hide (US.v idx2')) idx2 2ul;
  write r2 idx2';
  write r3 idx2;

  (**) let gs1 = gget (AL.varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (US.v idx1) (US.v idx2') (US.v idx2)) in
  assert (ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2) (US.v idx3) gs0 `FStar.FiniteSet.Base.equal`
          ALG.ptrs_all #AL.status (US.v idx1) (US.v idx2') (US.v idx2) gs1);

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx2) 2ul))
    idx1 idx2' idx2

inline_for_extraction noextract
let allocate_slab_aux_2_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t{US.v idx2 < U32.v md_count_v})
  (idx3: US.t)
  : Steel unit
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0 in
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob1)
  =
  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v md_region_lv
    idx1 idx2 idx3

inline_for_extraction noextract
let allocate_slab_aux_2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun r ->
    A.varray r `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0 in
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob1)
  =
  (**) ALG.lemma_head2_in_bounds pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) idx1 idx2 idx3;
  (**) starseq_unpack_s
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (US.v idx2);

  (**) ALG.lemma_head2_implies_pred2 pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) idx1 idx2 idx3;

  (**) let gs0 = gget (AL.varraylist pred1 pred2 pred3
                                (A.split_l md_region (u32_to_sz md_count_v))
                                (US.v idx1) (US.v idx2) (US.v idx3)) in

  (**) ALG.lemma_dataify_index #AL.status gs0 (US.v idx2);
  (**) SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v idx2);
  (**) change_equal_slprop
     (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx2)))
     (p_partial size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx2), slab_array slab_region (US.sizet_to_uint32 idx2)));
  (**) p_partial_unpack size_class
     (md_bm_array md_bm_region (US.sizet_to_uint32 idx2), slab_array slab_region (US.sizet_to_uint32 idx2))
     (md_bm_array md_bm_region (US.sizet_to_uint32 idx2), slab_array slab_region (US.sizet_to_uint32 idx2));

  let r = allocate_slot size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 idx2))
    (slab_array slab_region (US.sizet_to_uint32 idx2))
  in
  let cond = allocate_slab_aux_cond size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 idx2))
    (slab_array slab_region (US.sizet_to_uint32 idx2))
  in
  if cond then (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx2 2ul;
    allocate_slab_aux_2_full size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3;
    return r
  ) else (
    (**) pack_slab_starseq size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx2 1ul;
    assert (Seq.upd (G.reveal md_region_lv) (US.v idx2) 1ul `Seq.equal` md_region_lv);
    (**) starseq_weakening
      #_
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 1ul))
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx2) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count_v))
      (SeqUtils.init_u32_refined (U32.v md_count_v));
    allocate_slab_aux_2_partial size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3;
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
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
  (md_count_v0: U32.t{U32.v md_count_v0 < U32.v metadata_max})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v))))
    ) m /\
    G.reveal md_count_v == md_count_v0
  )
  (ensures
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v0 page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v0 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz md_count_v0)))
    ) m /\
    sel_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v))))
      m
    ==
    sel_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v0 page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v0 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz md_count_v0)))
      m
  )
  =
  ()

let alloc_metadata_sl2
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
  (md_count_v0: U32.t{U32.v md_count_v0 < U32.v metadata_max})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (U32.add md_count_v0 1ul))))
    ) m /\
    G.reveal md_count_v == md_count_v0
  )
  (ensures
    SM.interp (hp_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul))))
    ) m /\
    sel_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (U32.add md_count_v0 1ul))))
      m
    ==
    sel_of
      (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul))))
      m
  )
  =
  ()

let right_vprop_sl_lemma1
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v < U32.v metadata_max == true})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    right_vprop slab_region md_bm_region md_region v
  )) m)
  (ensures SM.interp (hp_of (
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz v))
  )) m /\
  sel_of (
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz v))
  ) m
  ==
  sel_of (right_vprop slab_region md_bm_region md_region v) m
  )
  = ()

let right_vprop_sl_lemma2
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v <= U32.v metadata_max == true})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz v))
  )) m)
  (ensures SM.interp (hp_of (
    right_vprop slab_region md_bm_region md_region v
  )) m /\
  sel_of (
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz v))
  ) m
  ==
  sel_of (right_vprop slab_region md_bm_region md_region v) m
  )
  = ()

inline_for_extraction noextract
let allocate_slab_aux_3_1_varraylist
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (idx1 idx2 idx3: US.t)
  : Steel unit
  (AL.varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (US.v idx1) (US.v idx2) (US.v idx3) `star`
  A.varray (md_array md_region md_count_v))
  (fun _ -> AL.varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
    (U32.v md_count_v) (US.v idx2) (US.v idx3))
  (requires fun _ -> U32.v md_count_v <> AL.null)
  (ensures fun h0 _ h1 ->
    ALG.dataify
      (AL.v_arraylist pred1 pred2 pred3
        (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
        (U32.v md_count_v) (US.v idx2) (US.v idx3) h1)
      `Seq.equal`
    Seq.append
      (ALG.dataify
        (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0))
      (Seq.create 1 0ul)
  )
  = unpack_md_array md_region md_count_v;
    ALG.lemma_head1_in_bounds pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) idx1 idx2 idx3;
    A.length_fits md_region;
    AL.extend1 md_region idx1 (Ghost.hide (US.v idx2)) (Ghost.hide (US.v idx3)) (u32_to_sz md_count_v) 0ul;
    change_slprop_rel
      (AL.varraylist pred1 pred2 pred3
        (A.split_l md_region (u32_to_sz md_count_v `US.add` 1sz))
        (US.v (u32_to_sz md_count_v)) (US.v idx2) (US.v idx3))
      (AL.varraylist pred1 pred2 pred3
        (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
        (U32.v md_count_v) (US.v idx2) (US.v idx3))
      (fun x y -> x == y)
      (fun _ -> assert (u32_to_sz (U32.add md_count_v 1ul) == u32_to_sz md_count_v `US.add` 1sz))

inline_for_extraction noextract
let allocate_slab_aux_3_1
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (idx1 idx2 idx3: US.t)
  : Steel unit
  (
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3))
  )
  (fun _ ->
    right_vprop slab_region md_bm_region md_region (U32.add md_count_v 1ul) `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
      (U32.v md_count_v) (US.v idx2) (US.v idx3)) `star`
    A.varray (slab_array slab_region md_count_v) `star`
    A.varray (md_bm_array md_bm_region md_count_v)
  )
  (requires fun h0 -> U32.v md_count_v <> AL.null)
  (ensures fun h0 _ h1 ->
    ALG.dataify
      (AL.v_arraylist pred1 pred2 pred3
        (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
        (U32.v md_count_v) (US.v idx2) (US.v idx3) h1)
      `Seq.equal`
    Seq.append
      (ALG.dataify
        (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0))
      (Seq.create 1 0ul) /\
    zf_u64 (A.asel (md_bm_array md_bm_region md_count_v) h1)
   )
  =
  change_slprop_rel
    (right_vprop slab_region md_bm_region md_region md_count_v)
    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size)))
     `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul)))
     `vrefine` zf_u64) `star`
   A.varray (A.split_r md_region (u32_to_sz md_count_v)))
    (fun x y -> x == y)
    (fun m -> right_vprop_sl_lemma1 slab_region md_bm_region md_region md_count_v m);
  elim_vrefine
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))))
    zf_u8;
  elim_vrefine
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))))
    zf_u64;
  slab_region_mon_split slab_region md_count_v;
  md_bm_region_mon_split md_bm_region md_count_v;
  md_region_mon_split md_region md_count_v;
  intro_vrefine
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count_v 1ul) page_size))))
    zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count_v 1ul) 4ul))))
    zf_u64;
  change_slprop_rel
    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count_v 1ul) page_size)))
     `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count_v 1ul) 4ul)))
     `vrefine` zf_u64) `star`
   A.varray (A.split_r md_region (u32_to_sz (U32.add md_count_v 1ul))))
    (right_vprop slab_region md_bm_region md_region (U32.add md_count_v 1ul))
    (fun x y -> x == y)
    (fun m -> right_vprop_sl_lemma2 slab_region md_bm_region md_region (U32.add md_count_v 1ul) m);
  allocate_slab_aux_3_1_varraylist
    md_region md_count_v idx1 idx2 idx3

let lemma_slab_aux_3_2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  : Lemma
    (let f1 = (f size_class slab_region md_bm_region md_count_v md_region_lv) in
     let f2 = (f size_class slab_region md_bm_region
      (U32.add md_count_v 1ul)
      (Seq.append md_region_lv (Seq.create 1 0ul))) in
     let s1 = (SeqUtils.init_u32_refined (U32.v md_count_v)) in
     let s2 = (Seq.slice (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul))) 0 (U32.v md_count_v)) in

     forall (k:nat{k < Seq.length s1}). f1 (Seq.index s1 k) == f2 (Seq.index s2 k))
  = let md_region_lv' = Seq.append md_region_lv (Seq.create 1 0ul) in
    let f1 = (f size_class slab_region md_bm_region md_count_v md_region_lv) in
    let f2 = (f size_class slab_region md_bm_region
     (U32.add md_count_v 1ul) md_region_lv') in
    let s1 = (SeqUtils.init_u32_refined (U32.v md_count_v)) in
    let s2 = (Seq.slice (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul))) 0 (U32.v md_count_v)) in

    let aux (k:nat{k < Seq.length s1}) : Lemma (f1 (Seq.index s1 k) == f2 (Seq.index s2 k))
      = SeqUtils.init_u32_refined_index (U32.v md_count_v) k;
        SeqUtils.init_u32_refined_index (U32.v (U32.add md_count_v 1ul)) k
    in Classical.forall_intro aux

let lemma_slab_aux_3_2_bis
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  : Lemma
    (p_empty size_class (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v) ==
     f size_class slab_region md_bm_region
      (U32.add md_count_v 1ul)
      (Seq.append md_region_lv (Seq.create 1 0ul))
      (Seq.index (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul))) (U32.v md_count_v)))
  = SeqUtils.init_u32_refined_index (U32.v (U32.add md_count_v 1ul)) (U32.v md_count_v)

#restart-solver

open Helpers
let allocate_slab_aux_3_2 (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  : SteelGhost unit opened
  (
    A.varray (slab_array slab_region md_count_v) `star`
    A.varray (md_bm_array md_bm_region md_count_v) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v (U32.add md_count_v 1ul)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (U32.add md_count_v 1ul)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (U32.add md_count_v 1ul)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul)))
  )
  (requires fun h0 ->
    zf_u64 (A.asel (md_bm_array md_bm_region md_count_v) h0)
  )
  (ensures fun _ _ _ -> True)
  =
  lemma_slab_aux_3_2 size_class slab_region md_bm_region md_region md_count_v md_region_lv;

  starseq_weakening_ref
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(pos:U32.t{U32.v pos < U32.v (U32.add md_count_v 1ul)})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f size_class slab_region md_bm_region
      (U32.add md_count_v 1ul)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region
      (U32.add md_count_v 1ul)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (Seq.slice (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul))) 0 (U32.v md_count_v));

  // required for selector equality propagation
  let md_as_seq = gget (A.varray (md_bm_array md_bm_region md_count_v)) in
  assert (G.reveal md_as_seq == Seq.create 4 0UL);
  A.ghost_split (slab_array slab_region md_count_v) 0sz;
  slab_to_slots size_class (A.split_r (slab_array slab_region md_count_v) 0sz);
  empty_md_is_properly_zeroed size_class;
  intro_slab_vprop size_class
    (md_bm_array md_bm_region md_count_v)
    (Seq.create 4 0UL)
    (slab_array slab_region md_count_v);
  p_empty_pack size_class
    (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v)
    (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v);

  SeqUtils.init_u32_refined_index (U32.v (U32.add md_count_v 1ul)) (U32.v md_count_v);
  change_equal_slprop
    (p_empty size_class (md_bm_array md_bm_region md_count_v, slab_array slab_region md_count_v))
    (f size_class slab_region md_bm_region
      (U32.add md_count_v 1ul)
      (Seq.append md_region_lv (Seq.create 1 0ul))
      (Seq.index (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul))) (U32.v md_count_v)));

  starseq_add_singleton_s
    #_
    #(pos:U32.t{U32.v pos < U32.v (U32.add md_count_v 1ul)})
    #(t size_class)
    (f size_class slab_region md_bm_region
      (U32.add md_count_v 1ul)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (f_lemma size_class slab_region md_bm_region
      (U32.add md_count_v 1ul)
      (Seq.append md_region_lv (Seq.create 1 0ul)))
    (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul)))
    (U32.v md_count_v)

#restart-solver
#push-options "--z3rlimit 100"
inline_for_extraction noextract
let allocate_slab_aux_3
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  : Steel US.t
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    right_vprop slab_region md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun idx1' ->
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    right_vprop slab_region md_bm_region md_region (U32.add md_count_v 1ul) `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
      (US.v idx1') (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v (U32.add md_count_v 1ul)})
      #(t size_class)
      (f size_class slab_region md_bm_region
        (U32.add md_count_v 1ul)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (f_lemma size_class slab_region md_bm_region
        (U32.add md_count_v 1ul)
        (Seq.append md_region_lv (Seq.create 1 0ul)))
      (SeqUtils.init_u32_refined (U32.v (U32.add md_count_v 1ul)))
  )
  (requires fun h0 ->
    U32.v md_count_v <> AL.null /\
    md_count_v == sel md_count h0 /\
    U32.v md_count_v < U32.v metadata_max /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
    )
  (ensures fun h0 idx1' h1 ->
    idx1' <> AL.null_ptr /\
    sel r1 h1 == idx1' /\
    sel r2 h1 == sel r2 h0 /\
    sel r3 h1 == sel r3 h0 /\
    md_count_v == sel md_count h0 /\
    sel md_count h1 = U32.add (sel md_count h0) 1ul /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul))) (US.v idx1') (US.v idx2) (US.v idx3) h1)
      `Seq.equal`
    Seq.append (Ghost.reveal md_region_lv) (Seq.create 1 0ul)
  )
  =
  let gs0 = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in

  allocate_slab_aux_3_1
    slab_region md_bm_region md_region md_count_v
    idx1 idx2 idx3;
  allocate_slab_aux_3_2 size_class
    slab_region md_bm_region md_region md_count_v md_region_lv
    (u32_to_sz md_count_v) idx2 idx3;

  let idx1' = u32_to_sz md_count_v in

  change_slprop_rel
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
      (U32.v md_count_v) (US.v idx2) (US.v idx3))
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz (U32.add md_count_v 1ul)))
      (US.v idx1') (US.v idx2) (US.v idx3))
    (fun x y -> x == y)
    (fun _ -> assert (U32.v md_count_v == US.v idx1'));

  let v = read md_count in
  write md_count (U32.add v 1ul);
  write r1 idx1';

  return idx1'
#pop-options

module P = Steel.FractionalPermission

#restart-solver
#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_slab'
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  : Steel (array U8.t)
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class (A.split_r slab_region 0sz) md_bm_region md_count_v md_region_lv)
      (f_lemma size_class (A.split_r slab_region 0sz) md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count_v)) `star`
    A.varrayp (A.split_l slab_region 0sz) halfp
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0 in
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    U32.v md_count_v <> AL.null /\
    md_count_v == sel md_count h0 /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) /\
    ALG.dataify gs0 `Seq.equal` Ghost.reveal md_region_lv
  )
  (ensures fun _ _ _ -> True)
  =
  if (idx2 <> AL.null_ptr) then (
    ALG.lemma_head2_in_bounds pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      idx1 idx2 idx3;
    // Lemma above used to derive
    assert (U32.v md_count_v <> AL.null);

    let r = allocate_slab_aux_2 size_class
      (A.split_r slab_region 0sz) md_bm_region md_region
      md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3 in
    pack_right_and_refactor_vrefine_dep
      size_class slab_region md_bm_region md_region md_count
      r1 r2 r3 md_count_v;
    A.varrayp_not_null r P.full_perm;
    change_equal_slprop
      (A.varray r)
      (if (A.is_null r) then emp else A.varray r);
    return r
  ) else if (idx1 <> AL.null_ptr) then (
    ALG.lemma_head1_in_bounds pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      idx1 idx2 idx3;
    // Lemma above used to derive
    assert (U32.v md_count_v <> AL.null);

    let r = allocate_slab_aux_1 size_class
      (A.split_r slab_region 0sz) md_bm_region md_region
      md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3 in
    pack_right_and_refactor_vrefine_dep
      size_class slab_region md_bm_region md_region md_count
      r1 r2 r3 md_count_v;
    A.varrayp_not_null r P.full_perm;
    change_equal_slprop
      (A.varray r)
      (if (A.is_null r) then emp else A.varray r);
    return r
  ) else (

    let md_count_v' = read md_count in
    let b = U32.lt md_count_v' metadata_max in
    if b then (
      let idx1' = allocate_slab_aux_3 size_class
        (A.split_r slab_region 0sz) md_bm_region md_region
        md_count r1 r2 r3
        md_count_v md_region_lv
        idx1 idx2 idx3 in
      admit(); // TODO: Need allocate_slab_aux_3 to give partition as a postcondition
      let r = allocate_slab_aux_1 size_class
        (A.split_r slab_region 0sz) md_bm_region md_region
        md_count r1 r2 r3
        (U32.add md_count_v 1ul)
        (G.hide (Seq.append (G.reveal md_region_lv) (Seq.create 1 0ul)))
        idx1' idx2 idx3 in
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r1 r2 r3 (U32.add md_count_v 1ul);
      A.varrayp_not_null r P.full_perm;
      change_equal_slprop
        (A.varray r)
        (if (A.is_null r) then emp else A.varray r);
      return r
    ) else (
      pack_3 size_class
        (A.split_r slab_region 0sz) md_bm_region md_region
        md_count r1 r2 r3
        md_count_v md_region_lv idx1 idx2 idx3;
      pack_right_and_refactor_vrefine_dep
          size_class slab_region md_bm_region md_region
          md_count
          r1 r2 r3 md_count_v;
      change_equal_slprop
        emp
        (if A.is_null A.null then emp else A.varray A.null);
      return (A.null #U8.t)
    )
  )

#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects"
let allocate_slab
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  : SteelT (array U8.t)
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  =
  let md_count_v
    : G.erased _
    = elim_vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3) in

  let md_count_v_ = read md_count in

  change_equal_slprop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 (G.reveal md_count_v))
    (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region
      r1 r2 r3 md_count_v_ `star`
    right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v_ `star`
    A.varrayp (A.split_l slab_region 0sz) halfp);


  let x
    : G.erased _
    = elim_vdep
    (left_vprop1 md_region r1 r2 r3 md_count_v_)
    (left_vprop_aux size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 md_count_v_) in

  let idxs
    : G.erased _
    = elim_vdep
      (vptr r1 `star` vptr r2 `star` vptr r3)
      (ind_varraylist_aux pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v_)))
  in
  let idx1_ = read r1 in
  let idx2_ = read r2 in
  let idx3_ = read r3 in

  elim_vrefine
    (ind_varraylist_aux2 pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v_)) idxs)
    (ind_varraylist_aux_refinement pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v_)) idxs);

  change_slprop_rel
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v_))
      (US.v (fst (fst (G.reveal idxs))))
      (US.v (snd (fst (G.reveal idxs))))
      (US.v (snd (G.reveal idxs))))
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v_))
      (US.v idx1_) (US.v idx2_) (US.v idx3_))
    (fun x y -> x == y)
    (fun _ ->
      assert (fst (fst (G.reveal idxs)) == idx1_);
      assert (snd (fst (G.reveal idxs)) == idx2_);
      assert (snd (G.reveal idxs) = idx3_)
    );

  let x' : Ghost.erased (Seq.lseq AL.status (U32.v md_count_v_)) = ALG.dataify (dsnd x) in

  change_equal_slprop
    (left_vprop_aux size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 md_count_v_ x)
    (starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v_})
      #(t size_class)
      (f size_class (A.split_r slab_region 0sz) md_bm_region md_count_v_ x')
      (f_lemma size_class (A.split_r slab_region 0sz) md_bm_region md_count_v_ x')
      (SeqUtils.init_u32_refined (U32.v md_count_v_)));

  let r = allocate_slab' size_class
    slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v_ x' idx1_ idx2_ idx3_
  in

  return r
