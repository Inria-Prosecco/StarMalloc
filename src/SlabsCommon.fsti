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
open Config
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
let pred4 (x: U32.t) : prop = U32.eq x 3ul == true
let pred5 (x: U32.t) : prop = U32.eq x 4ul == true

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred2 belongs to the second list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
let lemma_partition_and_pred_implies_mem2
  (hd1 hd2 hd3 hd4 hd5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 s /\
      pred2 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd2 s)
  = ALG.lemma_mem_ptrs_in hd1 s idx;
    ALG.lemma_mem_ptrs_in hd2 s idx;
    ALG.lemma_mem_ptrs_in hd3 s idx;
    ALG.lemma_mem_ptrs_in hd4 s idx;
    ALG.lemma_mem_ptrs_in hd5 s idx;
    let open FStar.FiniteSet.Ambient in
    (* Need this assert to trigger the right SMTPats in FiniteSet.Ambiant *)
    assert (FStar.FiniteSet.Base.mem idx (ALG.ptrs_all hd1 hd2 hd3 hd4 hd5 s));
    Classical.move_requires (ALG.lemma_mem_implies_pred pred1 hd1 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred2 hd2 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred3 hd3 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred4 hd4 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred5 hd5 s) idx

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred3 belongs to the third list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
let lemma_partition_and_pred_implies_mem3
  (hd1 hd2 hd3 hd4 hd5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 s /\
      pred3 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd3 s)
  = ALG.lemma_mem_ptrs_in hd1 s idx;
    ALG.lemma_mem_ptrs_in hd2 s idx;
    ALG.lemma_mem_ptrs_in hd3 s idx;
    ALG.lemma_mem_ptrs_in hd4 s idx;
    ALG.lemma_mem_ptrs_in hd5 s idx;
    let open FStar.FiniteSet.Ambient in
    (* Need this assert to trigger the right SMTPats in FiniteSet.Ambiant *)
    assert (FStar.FiniteSet.Base.mem idx (ALG.ptrs_all hd1 hd2 hd3 hd4 hd5 s));
    Classical.move_requires (ALG.lemma_mem_implies_pred pred1 hd1 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred2 hd2 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred3 hd3 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred4 hd4 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred5 hd5 s) idx

open Guards
open Quarantine

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
    (fun (|s,_|) -> is_empty size_class s == true)

let p_partial (size_class: sc) : blob -> vprop
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun (|s,_|) -> is_partial size_class s == true)

let p_full (size_class: sc) : blob -> vprop
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun (|s,_|) -> is_full size_class s == true)

let p_guard (size_class) : blob -> vprop
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (is_guard size_class (snd b) (fst b))

let p_quarantine (size_class) : blob -> vprop
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (is_quarantine size_class (snd b) (fst b))

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
    let v1 : Seq.lseq U64.t 4 = dfst blob1 in
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
    let v1 : Seq.lseq U64.t 4 = dfst blob1 in
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
    let v1 : Seq.lseq U64.t 4 = dfst blob1 in
    b1 == b2 /\
    is_full sc v1 /\
    h0 ((p_full sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )

val p_guard_unpack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  ((p_guard sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    b1 == b2 /\
    is_guard sc (snd b1) (fst b1) blob1 /\
    h0 ((p_guard sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )

val p_quarantine_unpack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  ((p_quarantine sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    b1 == b2 /\
    is_quarantine sc (snd b1) (fst b1) blob1 /\
    h0 ((p_quarantine sc) b1)
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
    let v0 : Seq.lseq U64.t 4 = dfst blob0 in
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
    let v0 : Seq.lseq U64.t 4 = dfst blob0 in
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
    let v0 : Seq.lseq U64.t 4 = dfst blob0 in
    is_full sc v0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_full sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

val p_guard_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_guard sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    is_guard sc (snd b1) (fst b1) blob0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_guard sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

val p_quarantine_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_quarantine sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    is_quarantine sc (snd b1) (fst b1) blob0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_quarantine sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

/// Retrieving the slab at index [md_count] in the [slab_region]
inline_for_extraction noextract
val slab_array
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : Pure (array U8.t)
  (requires
    A.length slab_region = US.v metadata_max * U32.v page_size /\
    US.v md_count < US.v metadata_max)
  (ensures fun r ->
    A.length r = U32.v page_size /\
    same_base_array r slab_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of slab_region) + US.v md_count * U32.v page_size
  )

#push-options "--print_implicits"

val pack_slab_array (#opened:_)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) (u32_to_sz page_size)))
    (fun _ -> A.varray (slab_array slab_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) (u32_to_sz page_size)) h0 ==
      A.asel (slab_array slab_region md_count) h1)

/// Retrieving the metadata bitmap at index [md_count] in array [md_bm_region]
inline_for_extraction noextract
val md_bm_array
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : Pure (array U64.t)
  (requires
    A.length md_bm_region = US.v metadata_max * 4 /\
    US.v md_count < US.v metadata_max)
  (ensures fun r ->
    A.length r = 4 /\
    same_base_array r md_bm_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of md_bm_region) + US.v md_count * 4
  )

val pack_md_bm_array (#opened:_)
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz))
    (fun _ -> A.varray (md_bm_array md_bm_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz) h0 ==
      A.asel (md_bm_array md_bm_region md_count) h1)

/// Retrieving the metadata status indicator at index [md_count] in array [md_region]
inline_for_extraction noextract
val md_array
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : Pure (array AL.cell)
  (requires
    A.length md_region = US.v metadata_max /\
    US.v md_count < US.v metadata_max)
  (ensures fun r ->
    A.length r = 1 /\
    same_base_array r md_region /\
    True
  )

val pack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_region md_count) 1sz))
    (fun _ -> A.varray (md_array md_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region md_count) 1sz) h0 ==
      A.asel (md_array md_region md_count) h1)

val unpack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (md_array md_region md_count))
    (fun _ -> A.varray (A.split_l (A.split_r md_region md_count) 1sz))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region md_count) 1sz) h1 ==
      A.asel (md_array md_region md_count) h0)

(** VProps related to slabs *)

// TODO: Document what the vprops represent

let f
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: Seq.lseq AL.status (US.v md_count_v))
  (i: US.t{US.v i < US.v md_count_v})
  : vprop
  =
  match Seq.index md_region_lv (US.v i) with
  | 0ul -> p_empty size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 1ul -> p_partial size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 2ul -> p_full size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 3ul -> p_guard size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 4ul -> p_quarantine size_class (md_bm_array md_bm_region i, slab_array slab_region i)

val t (size_class: sc) : Type0

val f_lemma
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: Seq.lseq AL.status (US.v md_count_v))
  (i: US.t{US.v i < US.v md_count_v})
  : Lemma
  (t_of (f size_class slab_region md_bm_region md_count_v md_region_lv i)
  == t size_class)

let ind_varraylist_aux2
  (r: A.array AL.cell)
  (idxs: (((US.t & US.t) & US.t) & US.t) & US.t)
  =
  AL.varraylist pred1 pred2 pred3 pred4 pred5 r
    (US.v (fst (fst (fst (fst idxs)))))
    (US.v (snd (fst (fst (fst idxs)))))
    (US.v (snd (fst (fst idxs))))
    (US.v (snd (fst idxs)))
    (US.v (snd idxs))

let ind_varraylist_aux_refinement
  (r: A.array AL.cell)
  (idxs: (((US.t & US.t) & US.t) & US.t) & US.t)
  (s: t_of (ind_varraylist_aux2 r idxs))
  : prop
  =
  ALG.partition #AL.status s
    (US.v (fst (fst (fst (fst idxs)))))
    (US.v (snd (fst (fst (fst idxs)))))
    (US.v (snd (fst (fst idxs))))
    (US.v (snd (fst idxs)))
    (US.v (snd idxs))

let ind_varraylist_aux
  (r: A.array AL.cell)
  (idxs: (((US.t & US.t) & US.t) & US.t) & US.t)
  =
  ind_varraylist_aux2 r idxs
  `vrefine`
  ind_varraylist_aux_refinement r idxs

let ind_varraylist
  (r: A.array AL.cell)
  (r1 r2 r3 r4 r5: ref US.t)
  =
  (
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5
  ) `vdep` ind_varraylist_aux r

let left_vprop1
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  =
  ind_varraylist
    (A.split_l md_region md_count_v)
    r1 r2 r3 r4 r5

let left_vprop2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (x: Seq.lseq AL.status (US.v md_count_v))
  =
  starseq
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v x)
    (f_lemma size_class slab_region md_bm_region md_count_v x)
    (SeqUtils.init_us_refined (US.v md_count_v))

let left_vprop_aux
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (x: t_of (ind_varraylist (A.split_l md_region md_count_v) r1 r2 r3 r4 r5))
  = starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (f_lemma size_class slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (SeqUtils.init_us_refined (US.v md_count_v))

let left_vprop
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  =
  left_vprop1 md_region r1 r2 r3 r4 r5 md_count_v
  `vdep`
  left_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 md_count_v

unfold
let vrefinedep_prop (x:US.t) : prop =
  US.v x <= US.v metadata_max /\
  US.v x <> AL.null

let right_vprop
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (v: US.t{US.v v <= US.v metadata_max})
  : vprop
  =
  (A.varray (A.split_r slab_region (US.mul v (u32_to_sz page_size)))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region (US.mul v 4sz))
    `vrefine` zf_u64) `star`
  A.varray (A.split_r md_region v)

let size_class_vprop_aux
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  empty_slabs partial_slabs full_slabs guard_slabs quarantine_slabs
  (v: US.t{US.v v <= US.v metadata_max == true})
  : vprop
  =
  left_vprop size_class
    slab_region md_bm_region md_region
    empty_slabs partial_slabs full_slabs guard_slabs quarantine_slabs v `star`
  right_vprop
    slab_region md_bm_region md_region v

open SteelVRefineDep

val pack_3
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
  : SteelGhost unit opened
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
    ALG.partition #AL.status gs0
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)

val pack_slab_starseq
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  //(r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx: US.t{US.v idx < US.v md_count_v})
  (v: AL.status)
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx) `star`
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx))
    = h0 (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx)) in
    let md : Seq.lseq U64.t 4 = dfst md_blob in
    //(v == 3ul ==> is_guard size_class md) /\
    (v == 4ul ==> is_quarantine  size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx) md_blob) /\
    (v == 3ul ==> is_guard size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx) md_blob) /\
    (v == 2ul ==> is_full size_class md) /\
    (v == 1ul ==> is_partial size_class md) /\
    (v == 0ul ==> is_empty size_class md) /\
    idx <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)

val pack_right_and_refactor_vrefine_dep
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  : SteelGhost unit opened
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    `star`
    right_vprop slab_region md_bm_region md_region md_count_v
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob0)
  (ensures fun h0 _ h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    dfst blob0 == dfst blob1
  )
