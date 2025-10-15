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
open Constants
open Config
open Utils2
open SlotsAlloc

open SteelStarSeqUtils
open FStar.Mul

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
val lemma_partition_and_pred_implies_mem2
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 tl5 sz5 s /\
     pred2 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd2 s)

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred3 belongs to the third list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
val lemma_partition_and_pred_implies_mem3
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 tl5 sz5 s /\
      pred3 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd3 s)

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred2 belongs to the second list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
val lemma_partition_and_pred_implies_mem5
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 tl5 sz5 s /\
     pred5 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd5 s)

open Guards
open Quarantine

val t (size_class: sc_full) : Type0

val empty_md_is_properly_zeroed
  (size_class: sc_full)
  : Lemma
  (slab_vprop_aux2 size_class (Seq.create 4 0UL))

/// A trivial, non-informative selector for quarantined and guard pages
inline_for_extraction noextract
val empty_t (size_class:sc_full) : t size_class

unfold
let blob (size_class: sc_full)
  = slab_metadata &
    (arr:array U8.t{A.length arr = U32.v size_class.slab_size})

/// Predicates capturing that a slab is empty, partially full, or full respectively
let p_empty (size_class: sc_full) : blob size_class -> vprop
  =
  fun b ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_empty size_class s == true)

let p_partial (size_class: sc_full) : blob size_class -> vprop
  =
  fun b ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_partial size_class s == true)

let p_full (size_class: sc_full) : blob size_class -> vprop
  =
  fun b ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_full size_class s == true)

let p_guard (sc:sc_full) : blob sc -> vprop
  =
  fun b ->
    (guard_slab sc (snd b) `star` A.varray (fst b))
    `vrewrite`
    (fun _ -> empty_t sc)
    //(
    //  (guard_slab (snd b) `star` A.varray (fst b))
    //  `VR2.vrefine`
    //  (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL)
    //) `vrewrite` (fun _ -> empty_t sc)

let p_quarantine (sc:sc_full) : blob sc -> vprop
  =
  fun b ->
    (
      (quarantine_slab sc (snd b) `star` A.varray (fst b))
      `VR2.vrefine`
      (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL)
    ) `vrewrite` (fun _ -> empty_t sc)

val p_empty_unpack (#opened:_)
  (sc: sc_full)
  (b1 b2: blob sc)
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
  (sc: sc_full)
  (b1 b2: blob sc)
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
  (sc: sc_full)
  (b1 b2: blob sc)
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
  (sc: sc_full)
  (b1 b2: blob sc)
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
  (sc: sc_full)
  (b1 b2: blob sc)
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
  (sc: sc_full)
  (b1 b2: blob sc)
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

val p_guard_pack (#opened:_)
  (size_class:sc_full)
  (b: blob size_class)
  : SteelGhostT unit opened
  (guard_slab size_class (snd b) `star` A.varray (fst b))
  (fun _ -> p_guard size_class b)

val p_quarantine_pack (#opened:_)
  (size_class:sc_full)
  (b: blob size_class)
  : SteelGhost unit opened
  (quarantine_slab size_class (snd b) `star` A.varray (fst b))
  (fun _ -> p_quarantine size_class b)
  (requires fun h0 ->
    let s : Seq.lseq U64.t 4 = A.asel (fst b) h0 in
    s `Seq.equal` Seq.create 4 0UL
  )
  (ensures fun _ _ _ -> True)

val p_quarantine_unpack (#opened:_)
  (size_class:sc_full)
  (b: blob size_class)
  : SteelGhost unit opened
  (p_quarantine size_class b)
  (fun _ -> quarantine_slab size_class (snd b) `star` A.varray (fst b))
  (requires fun _ -> True)
  (ensures fun _ _ h1 ->
    let s : Seq.lseq U64.t 4 = A.asel (fst b) h1 in
    s `Seq.equal` Seq.create 4 0UL
  )

#pop-options

/// Retrieving the slab at index [md_count] in the [slab_region]
inline_for_extraction noextract
val slab_array
  (sc: sc_full)
  (slab_region: array U8.t)
  (md_count: US.t)
  : Pure (array U8.t)
  (requires
    A.length slab_region = US.v sc.md_max * U32.v sc.slab_size /\
    US.v md_count < US.v sc.md_max)
  (ensures fun r ->
    A.length r = U32.v sc.slab_size /\
    same_base_array r slab_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of slab_region) + US.v md_count * U32.v sc.slab_size
  )

#push-options "--print_implicits"

val pack_slab_array (#opened:_)
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_count: US.t{US.v md_count < US.v sc.md_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz sc.slab_size))) (u32_to_sz sc.slab_size)))
    (fun _ -> A.varray (slab_array sc slab_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz sc.slab_size))) (u32_to_sz sc.slab_size)) h0 ==
      A.asel (slab_array sc slab_region md_count) h1)

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
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (md_region_lv: Seq.lseq AL.status (US.v md_count_v))
  (i: US.t{US.v i < US.v md_count_v})
  : vprop
  =
  match Seq.index md_region_lv (US.v i) with
  | 0ul -> p_empty sc (md_bm_array md_bm_region i, slab_array sc slab_region i)
  | 1ul -> p_partial sc (md_bm_array md_bm_region i, slab_array sc slab_region i)
  | 2ul -> p_full sc (md_bm_array md_bm_region i, slab_array sc slab_region i)
  | 3ul -> p_guard sc (md_bm_array md_bm_region i, slab_array sc slab_region i)
  | 4ul -> p_quarantine sc (md_bm_array md_bm_region i, slab_array sc slab_region i)

val f_lemma
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (md_region_lv: Seq.lseq AL.status (US.v md_count_v))
  (i: US.t{US.v i < US.v md_count_v})
  : Lemma
  (t_of (f sc slab_region md_bm_region md_count_v md_region_lv i)
  == t sc)

let ind_varraylist_aux2
  (r_varraylist: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  : vprop
  =
  AL.varraylist pred1 pred2 pred3 pred4 pred5 r_varraylist
    (US.v (Seq.index idxs 0))
    (US.v (Seq.index idxs 1))
    (US.v (Seq.index idxs 2))
    (US.v (Seq.index idxs 3))
    (US.v (Seq.index idxs 4))
    (US.v (Seq.index idxs 5))
    (US.v (Seq.index idxs 6))

val ind_varraylist_aux2_lemma
  (r_varraylist: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Lemma
  (requires
    idx1 == Seq.index idxs 0 /\
    idx2 == Seq.index idxs 1 /\
    idx3 == Seq.index idxs 2 /\
    idx4 == Seq.index idxs 3 /\
    idx5 == Seq.index idxs 4 /\
    idx6 == Seq.index idxs 5 /\
    idx7 == Seq.index idxs 6
  )
  (ensures (
    let l : list US.t
      = [ idx1; idx2; idx3; idx4; idx5; idx6; idx7 ] in
    let s : Seq.seq US.t = Seq.seq_of_list l in
    List.Tot.length l == 7 /\
    Seq.length s == 7 /\
    s `Seq.equal` idxs /\
    ind_varraylist_aux2 r_varraylist idxs
    ==
    AL.varraylist pred1 pred2 pred3 pred4 pred5 r_varraylist
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idx5) (US.v idx6) (US.v idx7)
  ))

#pop-options

let ind_varraylist_aux_refinement
  (r: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  (s: t_of (ind_varraylist_aux2 r idxs))
  : prop
  =
  ALG.partition #AL.status s
    (US.v (Seq.index idxs 0))
    (US.v (Seq.index idxs 1))
    (US.v (Seq.index idxs 2))
    (US.v (Seq.index idxs 3))
    (US.v (Seq.index idxs 4))

let ind_varraylist_aux
  (r: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  : vprop
  =
  ind_varraylist_aux2 r idxs
  `vrefine`
  ind_varraylist_aux_refinement r idxs

let ind_varraylist
  (r: A.array AL.cell)
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  : vprop
  =
  A.varray r_idxs `vdep` ind_varraylist_aux r

let left_vprop1
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  : vprop
  =
  ind_varraylist
    (A.split_l md_region md_count_v)
    r_idxs

let left_vprop2_aux
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (x: Seq.lseq AL.status (US.v md_count_v))
  : vprop
  =
  starseq
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t sc)
    (f sc slab_region md_bm_region md_count_v x)
    (f_lemma sc slab_region md_bm_region md_count_v x)
    (SeqUtils.init_us_refined (US.v md_count_v))

let left_vprop2
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (x: t_of (ind_varraylist (A.split_l md_region md_count_v) r_idxs))
  : vprop
  = starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (f_lemma sc slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (SeqUtils.init_us_refined (US.v md_count_v))

let left_vprop
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  =
  left_vprop1 md_region r_idxs md_count_v
  `vdep`
  left_vprop2 sc slab_region md_bm_region md_region r_idxs md_count_v

unfold
let vrefinedep_prop (sc: sc_full) (x:US.t): prop =
  US.v x <= US.v sc.md_max /\
  US.v x <> AL.null

let right_vprop
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (v: US.t{US.v v <= US.v sc.md_max})
  : vprop
  =
  (A.varray (A.split_r slab_region (US.mul v (u32_to_sz sc.slab_size)))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region (US.mul v 4sz))
    `vrefine` zf_u64) `star`
  A.varray (A.split_r md_region v)

let size_class_vprop_aux
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r_idxs: array US.t{A.length r_idxs = 7})
  (v: US.t{US.v v <= US.v sc.md_max == true})
  : vprop
  =
  left_vprop sc
    slab_region md_bm_region md_region
    r_idxs v `star`
  right_vprop sc
    slab_region md_bm_region md_region v

open SteelVRefineDep

val pack_3
  (#opened:_)
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : SteelGhost unit opened
  (
    vptr md_count `star`
    A.varray r_idxs `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma sc slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (vrefinedep_prop sc)
      (left_vprop sc slab_region md_bm_region md_region r_idxs)
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
    ALG.partition #AL.status gs0
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (vrefinedep_prop sc)
      (left_vprop sc slab_region md_bm_region md_region r_idxs)
    ) in
    md_count_v == dfst blob1)

val pack_slab_starseq
  (#opened:_)
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  //(r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx: US.t{US.v idx < US.v md_count_v})
  (v: AL.status)
  : SteelGhost unit opened
  (
    slab_vprop sc
      (slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx) `star`
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma sc slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma sc slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (f_lemma sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop sc
      (slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx))
    = h0 (slab_vprop sc
      (slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx)) in
    let md : Seq.lseq U64.t 4 = dfst (fst md_blob) in
    v <> 4ul /\
    v <> 3ul /\
    (v == 2ul ==> is_full sc md) /\
    (v == 1ul ==> is_partial sc md) /\
    (v == 0ul ==> is_empty sc md) /\
    idx <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)

inline_for_extraction noextract
val upd_and_pack_slab_starseq_quarantine
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx: US.t{US.v idx < US.v md_count_v})
  : Steel unit
  (
    slab_vprop sc
      (slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx) `star`
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma sc slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma sc slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) 4ul))
      (f_lemma sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) 4ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop sc
      (slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx))
    = h0 (slab_vprop sc
      (slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx)) in
    let md : Seq.lseq U64.t 4 = dfst (fst md_blob) in
    is_empty sc md
  )
  (ensures fun _ _ _ -> True)

val pack_right_and_refactor_vrefine_dep
  (#opened:_)
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v sc.md_max * U32.v sc.slab_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  : SteelGhost unit opened
  (
    vrefinedep
      (vptr md_count)
      (vrefinedep_prop sc)
      (left_vprop sc slab_region md_bm_region md_region r_idxs)
    `star`
    right_vprop sc slab_region md_bm_region md_region md_count_v
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (vrefinedep_prop sc)
      (size_class_vprop_aux sc slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      (vrefinedep_prop sc)
      (left_vprop sc slab_region md_bm_region md_region r_idxs)
    ) in
    md_count_v == dfst blob0
  )
  (ensures fun h0 _ h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      (vrefinedep_prop sc)
      (left_vprop sc slab_region md_bm_region md_region r_idxs)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (vrefinedep_prop sc)
      (size_class_vprop_aux sc slab_region md_bm_region md_region r_idxs)
    ) in
    dfst blob0 == dfst blob1
  )
