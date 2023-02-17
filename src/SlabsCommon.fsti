module SlabsCommon

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

// TODO: to be removed/move apart ; use stdlib
// discussion
inline_for_extraction noextract
let u32_to_sz
  (x:U32.t)
  : Tot (y:US.t{US.v y == U32.v x})
  //: Pure US.t
  //(requires True)
  //(ensures fun y -> US.v y == U32.v x)
  =
  US.uint32_to_sizet x

inline_for_extraction noextract
let halfp = Steel.FractionalPermission.half_perm Steel.FractionalPermission.full_perm

#push-options "--print_implicits --print_universes"
#set-options "--ide_id_info_off"

let pred1 (x: U32.t) : prop = U32.eq x 0ul == true
let pred2 (x: U32.t) : prop = U32.eq x 1ul == true
let pred3 (x: U32.t) : prop = U32.eq x 2ul == true

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred2 belongs to the second list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
let lemma_partition_and_pred_implies_mem2
  (hd1 hd2 hd3:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 /\
      ALG.varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3 s /\
      pred2 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd2 s)
  = ALG.lemma_mem_ptrs_in hd1 s idx;
    ALG.lemma_mem_ptrs_in hd2 s idx;
    ALG.lemma_mem_ptrs_in hd3 s idx;
    let open FStar.FiniteSet.Ambient in
    (* Need this assert to trigger the right SMTPats in FiniteSet.Ambiant *)
    assert (FStar.FiniteSet.Base.mem idx (ALG.ptrs_all hd1 hd2 hd3 s));
    Classical.move_requires (ALG.lemma_mem_implies_pred pred1 hd1 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred2 hd2 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred3 hd3 s) idx

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred3 belongs to the third list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
let lemma_partition_and_pred_implies_mem3
  (hd1 hd2 hd3:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 /\
      ALG.varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3 s /\
      pred3 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd3 s)
  = ALG.lemma_mem_ptrs_in hd1 s idx;
    ALG.lemma_mem_ptrs_in hd2 s idx;
    ALG.lemma_mem_ptrs_in hd3 s idx;
    let open FStar.FiniteSet.Ambient in
    (* Need this assert to trigger the right SMTPats in FiniteSet.Ambiant *)
    assert (FStar.FiniteSet.Base.mem idx (ALG.ptrs_all hd1 hd2 hd3 s));
    Classical.move_requires (ALG.lemma_mem_implies_pred pred1 hd1 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred2 hd2 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred3 hd3 s) idx

unfold
let blob
  = slab_metadata &
    (arr:array U8.t{A.length arr = U32.v page_size})

/// Predicates capturing that a slab is empty, partially full, or full respectively
let p_empty (size_class: sc) : blob -> vprop
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_empty size_class s == true)

let p_partial (size_class: sc) : blob -> vprop
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_partial size_class s == true)

let p_full (size_class: sc) : blob -> vprop
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_full size_class s == true)

val p_empty_unpack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  ((p_empty sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    b1 == b2 /\
    is_empty sc v1 /\
    h0 ((p_empty sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )

val p_partial_unpack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  ((p_partial sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    b1 == b2 /\
    is_partial sc v1 /\
    h0 ((p_partial sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )

val p_full_unpack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  ((p_full sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    b1 == b2 /\
    is_full sc v1 /\
    h0 ((p_full sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )

val p_empty_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_empty sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    is_empty sc v0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_empty sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

val p_partial_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_partial sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    is_partial sc v0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_partial sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

val p_full_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_full sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    is_full sc v0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_full sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

/// Retrieving the slab at index [md_count] in the [slab_region]
inline_for_extraction noextract
val slab_array
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array U8.t)
  (requires
    A.length slab_region = U32.v metadata_max * U32.v page_size /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = U32.v page_size /\
    same_base_array r slab_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of slab_region) + U32.v md_count * U32.v page_size
  )

val pack_slab_array (#opened:_)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (fun _ -> A.varray (slab_array slab_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)) h0 ==
      A.asel (slab_array slab_region md_count) h1)

/// Retrieving the metadata bitmap at index [md_count] in array [md_bm_region]
inline_for_extraction noextract
val md_bm_array
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array U64.t)
  (requires
    A.length md_bm_region = U32.v metadata_max * 4 /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = 4 /\
    same_base_array r md_bm_region
  )

val pack_md_bm_array (#opened:_)
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (fun _ -> A.varray (md_bm_array md_bm_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)) h0 ==
      A.asel (md_bm_array md_bm_region md_count) h1)

/// Retrieving the metadata status indicator at index [md_count] in array [md_region]
inline_for_extraction noextract
val md_array
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array AL.cell)
  (requires
    A.length md_region = U32.v metadata_max /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = 1 /\
    same_base_array r md_region /\
    True
  )

val pack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul)))
    (fun _ -> A.varray (md_array md_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul)) h0 ==
      A.asel (md_array md_region md_count) h1)

val unpack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (md_array md_region md_count))
    (fun _ -> A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) 1sz))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region (u32_to_sz md_count)) 1sz) h1 ==
      A.asel (md_array md_region md_count) h0)

(** VProps related to slabs *)

// TODO: Document what the vprops represent

let f
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: Seq.lseq AL.status (U32.v md_count_v))
  (i: U32.t{U32.v i < U32.v md_count_v})
  : vprop
  =
  match Seq.index md_region_lv (U32.v i) with
  | 0ul -> p_empty size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 1ul -> p_partial size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 2ul -> p_full size_class (md_bm_array md_bm_region i, slab_array slab_region i)

val t (size_class: sc) : Type0

val f_lemma
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: Seq.lseq AL.status (U32.v md_count_v))
  (i: U32.t{U32.v i < U32.v md_count_v})
  : Lemma
  (t_of (f size_class slab_region md_bm_region md_count_v md_region_lv i)
  == t size_class)

let ind_varraylist_aux
  (pred1 pred2 pred3: AL.status -> prop) (r: A.array AL.cell)
  (idxs: (US.t & US.t) & US.t)
  = AL.varraylist pred1 pred2 pred3 r
      (US.v (fst (fst idxs)))
      (US.v (snd (fst idxs)))
      (US.v (snd idxs))

let ind_varraylist
  (pred1 pred2 pred3: AL.status -> prop) (r: A.array AL.cell)
  (r1 r2 r3: ref US.t)
  =
  (vptr r1 `star` vptr r2 `star` vptr r3) `vdep`
  ind_varraylist_aux pred1 pred2 pred3 r

let left_vprop1
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  =
  ind_varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    r1 r2 r3

let left_vprop2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (x: Seq.lseq AL.status (U32.v md_count_v))
  =
  starseq
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v x)
    (f_lemma size_class slab_region md_bm_region md_count_v x)
    (SeqUtils.init_u32_refined (U32.v md_count_v))

let left_vprop_aux
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (x: t_of (ind_varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) r1 r2 r3))
  = starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (f_lemma size_class slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (SeqUtils.init_u32_refined (U32.v md_count_v))

let left_vprop
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  =
  left_vprop1 md_region r1 r2 r3 md_count_v
  `vdep`
  left_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 md_count_v

unfold
let vrefinedep_prop (x:U32.t) : prop =
  U32.v x <= U32.v metadata_max /\
  U32.v x <> AL.null

let right_vprop
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v <= U32.v metadata_max})
  : vprop
  =
  (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
    `vrefine` zf_u64) `star`
  A.varray (A.split_r md_region (u32_to_sz v))

let size_class_vprop_aux
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  empty_slabs partial_slabs full_slabs
  (v: U32.t{U32.v v <= U32.v metadata_max == true})
  : vprop
  =
  left_vprop size_class
    (A.split_r slab_region 0sz) md_bm_region md_region
    empty_slabs partial_slabs full_slabs v `star`
  right_vprop
    (A.split_r slab_region 0sz) md_bm_region md_region v `star`
  A.varrayp (A.split_l slab_region 0sz) halfp

open SteelVRefineDep

val pack_3
  (#opened:_)
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
  : SteelGhost unit opened
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
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob1)

val pack_slab_starseq
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx: US.t{US.v idx < U32.v md_count_v})
  (v: AL.status)
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx)) `star`
    (starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_u32_refined (U32.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_u32_refined (U32.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx)))
    = h0 (slab_vprop size_class
      (slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx))) in
    let md : Seq.lseq U64.t 4 = dfst (fst md_blob) in
    (v == 2ul ==> is_full size_class md) /\
    (v == 1ul ==> is_partial size_class md) /\
    (v == 0ul ==> is_empty size_class md) /\
    idx <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)

val pack_right_and_refactor_vrefine_dep
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  : SteelGhost unit opened
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3)
    `star`
    (right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v `star`
    A.varrayp (A.split_l slab_region 0sz) halfp)
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob0)
  (ensures fun h0 _ h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    dfst blob0 == dfst blob1
  )
