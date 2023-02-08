module Slabs2

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

open Utils2
open Slots
open Slots2
open Slabs

open FStar.Mul
open SteelStarSeqUtils
open SteelVRefineDep
module AL = ArrayList
module ALG = ArrayListGen

unfold
let blob = Slabs.blob

#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
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
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    dfst (fst blob0) == dfst (fst blob1) /\
    dsnd (fst blob0) == dsnd (fst blob1) /\
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

inline_for_extraction noextract
let deallocate_slab_aux_1_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t)
  (idx3: US.t)
  (pos: US.t{US.v pos < U32.v md_count_v})
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
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob1)
  =
  // required for selector equality propagation
  (**) let _ = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in
  // partition improvements required
  admit ();

  let idx3' = AL.remove3 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (G.hide (US.v idx1)) (G.hide (US.v idx2)) idx3 pos in
  AL.insert2 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx2 (G.hide (US.v idx1)) (G.hide (US.v idx3')) pos 1ul;
  write r3 idx3';
  write r2 pos;

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
    idx1 pos idx3'

inline_for_extraction noextract
let deallocate_slab_aux_1_empty
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t)
  (idx3: US.t)
  (pos: US.t{US.v pos < U32.v md_count_v})
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
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob1)
  =
  // required for selector equality propagation
  (**) let _ = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in
  // partition improvements required
  admit ();

  let idx3' = AL.remove3 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (G.hide (US.v idx1)) (G.hide (US.v idx2)) idx3 pos in
  AL.insert1 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 (G.hide (US.v idx2)) (G.hide (US.v idx3')) pos 1ul;
  write r3 idx3';
  write r1 pos;

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
    pos idx2 idx3'

#restart-solver
#push-options "--z3rlimit 100"
let deallocate_slab_aux_1
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  (pos: US.t{US.v pos < U32.v md_count_v})
  : Steel bool
  (
    A.varray ptr `star`
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
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    let arr' = slab_array slab_region (US.sizet_to_uint32 pos) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr') in
    same_base_array arr' ptr /\
    0 <= diff /\
    diff < U32.v  page_size /\
    (U32.v page_size) % (U32.v size_class) = 0 /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 2ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob1)
  =
  (**) starseq_unpack_s
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (US.v pos);
  (**) SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v pos);
  (**) change_equal_slprop
    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v pos)))
    (p_full size_class (md_bm_array md_bm_region (US.sizet_to_uint32 pos), slab_array slab_region (US.sizet_to_uint32 pos)));
  (**) p_full_unpack size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 pos), slab_array slab_region (US.sizet_to_uint32 pos))
    (md_bm_array md_bm_region (US.sizet_to_uint32 pos), slab_array slab_region (US.sizet_to_uint32 pos));
  let b = deallocate_slot size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 pos))
    (slab_array slab_region (US.sizet_to_uint32 pos))
    ptr in
  if b then (
    // deallocation success, slab no longer full
    // TODO: is it empty?
    let cond = deallocate_slab_aux_cond size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 pos))
      (slab_array slab_region (US.sizet_to_uint32 pos)) in
    if cond then (
      admit ();
      allocate_slab_aux_helper size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv pos 0ul;
      deallocate_slab_aux_1_empty size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv idx1 idx2 idx3 pos;
      return b
    ) else (
      admit ();
      allocate_slab_aux_helper size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv pos 1ul;
      deallocate_slab_aux_1_partial size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv idx1 idx2 idx3 pos;
      return b
    )
  ) else (
    sladmit ();
    return b
  )
#pop-options

inline_for_extraction noextract
let deallocate_slab_aux_2_empty
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t)
  (idx3: US.t)
  (pos: US.t{US.v pos < U32.v md_count_v})
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
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob1)
  =
  // required for selector equality propagation
  (**) let _ = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in
  // partition improvements required
  admit ();

  let idx2' = AL.remove2 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (G.hide (US.v idx1)) idx2 (G.hide (US.v idx3)) pos in
  AL.insert1 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 (G.hide (US.v idx2')) (G.hide (US.v idx3)) pos 0ul;
  write r2 idx2';
  write r1 pos;

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v pos) 0ul))
    pos idx2' idx3

inline_for_extraction noextract
let deallocate_slab_aux_2_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1: US.t)
  (idx2: US.t)
  (idx3: US.t)
  (pos: US.t{US.v pos < U32.v md_count_v})
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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob1)
  =
  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v md_region_lv
    idx1 idx2 idx3

#restart-solver
#push-options "--z3rlimit 100"
let deallocate_slab_aux_2
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  (pos: US.t{US.v pos < U32.v md_count_v})
  : Steel bool
  (
    A.varray ptr `star`
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
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    let arr' = slab_array slab_region (US.sizet_to_uint32 pos) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr') in
    same_base_array arr' ptr /\
    0 <= diff /\
    diff < U32.v  page_size /\
    (U32.v page_size) % (U32.v size_class) = 0 /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv /\
    Seq.index (G.reveal md_region_lv) (US.v pos) = 1ul
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob1)
  =
  (**) starseq_unpack_s
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (US.v pos);
  (**) SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v pos);
  (**) change_equal_slprop
    (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v pos)))
    (p_partial size_class (md_bm_array md_bm_region (US.sizet_to_uint32 pos), slab_array slab_region (US.sizet_to_uint32 pos)));
  (**) p_partial_unpack size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 pos), slab_array slab_region (US.sizet_to_uint32 pos))
    (md_bm_array md_bm_region (US.sizet_to_uint32 pos), slab_array slab_region (US.sizet_to_uint32 pos));
  let b = deallocate_slot size_class
    (md_bm_array md_bm_region (US.sizet_to_uint32 pos))
    (slab_array slab_region (US.sizet_to_uint32 pos))
    ptr in
  if b then (
    // deallocation success, slab no longer full
    // TODO: is it empty?
    let cond = deallocate_slab_aux_cond size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 pos))
      (slab_array slab_region (US.sizet_to_uint32 pos)) in
    if cond then (
      admit ();
      (**) allocate_slab_aux_helper size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv pos 0ul;
      deallocate_slab_aux_2_empty size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv idx1 idx2 idx3 pos;
      return b
    ) else (
      admit ();
      (**) allocate_slab_aux_helper size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv pos 1ul;
      assert (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul `Seq.equal` md_region_lv);
    (**) starseq_weakening
      #_
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v pos) 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count_v))
      (SeqUtils.init_u32_refined (U32.v md_count_v));
      deallocate_slab_aux_2_partial size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv idx1 idx2 idx3 pos;
      return b
    )
  ) else (
    sladmit ();
    return b
  )
#pop-options

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let deallocate_slab'
  (ptr: array U8.t)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  (diff: UP.t)
  : Steel bool
  (
    A.varray ptr `star`
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
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of slab_region) in
    0 <= diff' /\
    diff' < U32.v page_size /\
    UP.v diff == diff' /\
    same_base_array ptr slab_region /\
    (U32.v page_size) % (U32.v size_class) = 0 /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    md_count_v == sel md_count h0 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
  )
  (ensures fun _ _ _ -> True)
  =
  let diff_sz = UP.ptrdifft_to_sizet diff in
  assume (US.fits_u32);
  assert_norm (4 < FI.max_int 16);
  let diff_u32 = US.sizet_to_uint32 diff_sz in
  assume (U32.v diff_u32 == UP.v diff);
  let pos = U32.div diff_u32 page_size in
  let pos' = u32_to_sz pos in

  // check diff/page_size < md_count
  if U32.lt pos md_count_v then (
    // selector equality propagation
    let gs0 = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in
    ALG.lemma_dataify_index #AL.status gs0 (U32.v pos);
    let status1 = AL.read_in_place
        (A.split_l md_region (u32_to_sz md_count_v))
        (US.v idx1) (US.v idx2) (US.v idx3) (US.uint_to_t (U32.v pos)) in
    if (U32.eq status1 2ul) then (
      let b = deallocate_slab_aux_1 ptr size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv idx1 idx2 idx3 pos' in
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r1 r2 r3 md_count_v;
      return b
    ) else if (U32.eq status1 1ul) then (
      let b = deallocate_slab_aux_2 ptr size_class
        slab_region md_bm_region md_region md_count r1 r2 r3
        md_count_v md_region_lv idx1 idx2 idx3 pos' in
      pack_right_and_refactor_vrefine_dep
        size_class slab_region md_bm_region md_region md_count
        r1 r2 r3 md_count_v;
      return b
    ) else (
      sladmit ();
      return false
    )
  ) else (
    sladmit ();
    return false
  )

