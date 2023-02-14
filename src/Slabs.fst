module Slabs

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
open Slots
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

#push-options "--print_implicits --print_universes"
#set-options "--ide_id_info_off"

let pred1 (x: U32.t) : prop = U32.eq x 0ul == true
let pred2 (x: U32.t) : prop = U32.eq x 1ul == true
let pred3 (x: U32.t) : prop = U32.eq x 2ul == true

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

let p_empty (size_class: sc)
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_empty size_class s == true)

let p_partial (size_class: sc)
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_partial size_class s == true)

let p_full (size_class: sc)
  =
  fun (b:blob) ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_full size_class s == true)

#push-options "--compat_pre_typed_indexed_effects"
#push-options "--z3rlimit 50"
let p_empty_unpack (#opened:_)
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
  =
  change_slprop_rel
    ((p_empty sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_empty sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|), _) -> is_empty sc s == true)

let p_partial_unpack (#opened:_)
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
  =
  change_slprop_rel
    ((p_partial sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_partial sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|), _) -> is_partial sc s == true)

let p_full_unpack (#opened:_)
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
  =
  change_slprop_rel
    ((p_full sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_full sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|), _) -> is_full sc s == true)

let p_full_pack (#opened:_)
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
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|), _) -> is_full sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_full sc s == true))
    ((p_full sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_partial_pack (#opened:_)
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
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|), _) -> is_partial sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_partial sc s == true))
    ((p_partial sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_empty_pack (#opened:_)
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
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|), _) -> is_empty sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_empty sc s == true))
    ((p_empty sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

#pop-options
#pop-options

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
#pop-options

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let slab_array
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array U8.t)
  (requires
    A.length slab_region = U32.v metadata_max * U32.v page_size /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = U32.v page_size /\
    same_base_array r slab_region /\
    True
  )
  =
  let ptr = A.ptr_of slab_region in
  let shift = U32.mul md_count page_size in
  let shift_size_t = u32_to_sz shift in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide (U32.v page_size)|)

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
  change_equal_slprop
    (A.varray (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (slab_array slab_region md_count));
  let x1 = A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size) in
  let x2 = A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))))

inline_for_extraction noextract
let md_bm_array
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array U64.t)
  (requires
    A.length md_bm_region = U32.v metadata_max * 4 /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = 4 /\
    same_base_array r md_bm_region /\
    True
  )
  =
  let ptr = A.ptr_of md_bm_region in
  let shift = U32.mul md_count 4ul in
  let shift_size_t = u32_to_sz shift in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide 4|)

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
  change_equal_slprop
    (A.varray (A.split_l (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (A.varray (md_bm_array md_bm_region md_count));
  let x1 = A.split_r (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul) in
  let x2 = A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))))

inline_for_extraction noextract
let md_array
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
  =
  let ptr = A.ptr_of md_region in
  let shift_size_t = u32_to_sz md_count in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide 1|)

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
  change_equal_slprop
    (A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul)))
    (A.varray (md_array md_region md_count));
  let x1 = A.split_r (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul) in
  let x2 = A.split_r md_region (u32_to_sz (U32.add md_count 1ul)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_equal_slprop
    (A.varray (A.split_r (A.split_r md_region (u32_to_sz (md_count))) (u32_to_sz 1ul)))
    (A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul))))

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

let f_lemma
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: Seq.lseq AL.status (U32.v md_count_v))
  (i: U32.t{U32.v i < U32.v md_count_v})
  : Lemma
  (t_of (f size_class slab_region md_bm_region md_count_v md_region_lv i)
  ==
  dtuple2
    (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
    (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
  & Seq.lseq U8.t 0)
  =
  slab_vprop_lemma size_class
    (slab_array slab_region i)
    (md_bm_array md_bm_region i)

let t
  (size_class: sc)
  : Type0
  =
  dtuple2
    (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
    (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
  & Seq.lseq U8.t 0

let ind_varraylist_aux
  (pred1 pred2 pred3: AL.status -> prop) (r: A.array AL.cell)
  (idxs: (US.t & US.t) & US.t)
  = AL.varraylist pred1 pred2 pred3 r
      (US.v (fst (fst idxs)))
      (US.v (snd (fst idxs)))
      (US.v (snd idxs))

#push-options "--z3rlimit 30"
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

open SteelVRefineDep

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 30"
let pack_3
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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob1)
  =
  intro_vdep
    (vptr r1 `star` vptr r2 `star` vptr r3)
    (ind_varraylist_aux pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) ((idx1, idx2), idx3))
    (ind_varraylist_aux pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)));

  change_equal_slprop
    ((vptr r1 `star` vptr r2 `star` vptr r3) `vdep`
      ind_varraylist_aux pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)))
    (left_vprop1 md_region r1 r2 r3 md_count_v);
  change_equal_slprop
    (starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_u32_refined (U32.v md_count_v)))
    (left_vprop2 size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv));

  intro_vdep
    (left_vprop1 md_region r1 r2 r3 md_count_v)
    (left_vprop2 size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
    (left_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 md_count_v);

  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
    (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 md_count_v)

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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
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
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 idx2 idx3;
  // required for selector equality propagation
  (**) let _ = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in

  let idx1' = AL.remove1 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 (Ghost.hide (US.v idx2)) (Ghost.hide (US.v idx3)) idx1 in
  AL.insert2 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx2 (Ghost.hide (US.v idx1')) (Ghost.hide (US.v idx3)) idx1 1ul;
  write r1 idx1';
  write r2 idx1;

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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
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
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 idx2 idx3;
  // required for selector equality propagation
  (**) let _ = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in

  let idx1' = AL.remove1 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 (Ghost.hide (US.v idx2)) (Ghost.hide (US.v idx3)) idx1 in
  AL.insert3 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx3 (Ghost.hide (US.v idx1')) (Ghost.hide (US.v idx2)) idx1 2ul;
  write r1 idx1';
  write r3 idx1;

  (**) pack_3 size_class slab_region md_bm_region md_region md_count r1 r2 r3
    md_count_v (G.hide (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
    idx1' idx2 idx1


let lemma_slab_aux_starseq
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx:nat{idx < U32.v md_count_v})
  (v:AL.status)
  : Lemma
  (let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
   let f2 = f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
   let s = SeqUtils.init_u32_refined (U32.v md_count_v) in
   forall (k:nat{k <> idx /\ k < Seq.length s}).
     f1 (Seq.index s k) == f2 (Seq.index s k))
  =
  let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
  let f2 = f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
  let md_region_lv' = Seq.upd (G.reveal md_region_lv) idx v in
  let s = SeqUtils.init_u32_refined (U32.v md_count_v) in
  let aux (k:nat{k <> idx /\ k < Seq.length s})
    : Lemma (f1 (Seq.index s k) == f2 (Seq.index s k))
    = let i = Seq.index s k in
      SeqUtils.init_u32_refined_index (U32.v md_count_v) k;
      assert (Seq.index md_region_lv (U32.v i) == Seq.index md_region_lv' (U32.v i))
  in Classical.forall_intro aux

let allocate_slab_aux_helper
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
    starseq
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
      (Seq.slice (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_u32_refined (U32.v md_count_v))))
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
    let md = v_slab_vprop_md size_class
      (slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx)) h0 in
    (v == 2ul ==> is_full size_class md) /\
    (v == 1ul ==> is_partial size_class md) /\
    (v == 0ul ==> is_empty size_class md) /\
    idx <> AL.null_ptr
  )
  (ensures fun h0 _ h1 -> True)
  =
  if U32.eq v 2ul then (
    p_full_pack size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx));
    SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v idx);
    change_equal_slprop
      (p_full size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx), slab_array slab_region (US.sizet_to_uint32 idx)))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx)))
  ) else if U32.eq v 1ul then (
    p_partial_pack size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx));
    SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v idx);
    change_equal_slprop
      (p_partial size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx), slab_array slab_region (US.sizet_to_uint32 idx)))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx)))
  ) else (
     p_empty_pack size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx));
    SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v idx);
    change_equal_slprop
      (p_empty size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx), slab_array slab_region (US.sizet_to_uint32 idx)))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx)))
  );
  lemma_slab_aux_starseq size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv (US.v idx) v;
  starseq_upd_pack
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (US.v idx)

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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
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
    (**) allocate_slab_aux_helper size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 2ul;
    allocate_slab_aux_1_full size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3;
    return r
  ) else (
    (**) allocate_slab_aux_helper size_class
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
  //: Steel (array U8.t)
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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
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
  (**) ALG.lemma_head_not_null_mem pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx1 idx2 idx3;
  // required for selector equality propagation
  (**) let __ = gget (AL.varraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3)) in

  let idx2' = AL.remove2 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (Ghost.hide (US.v idx1)) idx2 (Ghost.hide (US.v idx3)) idx2 in
  AL.insert3 #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx3 (Ghost.hide (US.v idx1)) (Ghost.hide (US.v idx2')) idx2 2ul;
  write r2 idx2';
  write r3 idx2;

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
  //: Steel (array U8.t)
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
    idx2 <> AL.null_ptr /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 v)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx2 <> AL.null_ptr /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv

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
    (**) allocate_slab_aux_helper size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx2 2ul;
    allocate_slab_aux_2_full size_class
      slab_region md_bm_region md_region md_count r1 r2 r3
      md_count_v md_region_lv idx1 idx2 idx3;
    return r
  ) else (
    (**) allocate_slab_aux_helper size_class
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
  = change_equal_slprop
      (A.varray (md_array md_region md_count_v))
      (A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count_v)) 1sz));
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
  assume ((U32.v page_size) % (U32.v size_class) == 0);
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

  // AF: Need to better think about how to model null to handle the case md_count == 0
  assume (U32.v md_count_v <> AL.null);

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
  A.varray (A.split_l slab_region 0sz)

let pack_right_and_refactor_vrefine_dep
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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 v)
    `star`
    (right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v `star`
    A.varray (A.split_l slab_region 0sz))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 v)
    ) in
    md_count_v == dfst blob0)
  (ensures fun h0 _ h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 v)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    dfst blob0 == dfst blob1
  )
  =
  let md_count_v' = elim_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 v) in
  assert (G.reveal md_count_v' == md_count_v);
  change_equal_slprop
    (right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v)
    (right_vprop (A.split_r slab_region 0sz) md_bm_region md_region (G.reveal md_count_v'));
  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
    (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 (G.reveal md_count_v') `star`
    right_vprop (A.split_r slab_region 0sz) md_bm_region md_region (G.reveal md_count_v') `star`
    A.varray (A.split_l slab_region 0sz))

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
    A.varray (A.split_l slab_region 0sz)
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    md_count_v == sel md_count h0 /\
    ALG.dataify (AL.v_arraylist pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v)) (US.v idx1) (US.v idx2) (US.v idx3) h0) `Seq.equal` Ghost.reveal md_region_lv
  )
  (ensures fun _ _ _ -> True)
  =
  if (idx2 <> AL.null_ptr) then (
    ALG.lemma_head2_in_bounds pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      idx1 idx2 idx3;
    // Lemma above used to derive
    assert (0 < U32.v md_count_v);

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
    assert (0 < U32.v md_count_v);

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
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  =
  let md_count_v
    : G.erased _
    = elim_vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3) in

  let md_count_v_ = read md_count in

  change_equal_slprop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 (G.reveal md_count_v))
    (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region
      r1 r2 r3 md_count_v_ `star`
    right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v_ `star`
    A.varray (A.split_l slab_region 0sz));


  let x
    : G.erased _
    = elim_vdep
    (left_vprop1 md_region r1 r2 r3 md_count_v_)
    (left_vprop_aux size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 md_count_v_) in

  change_equal_slprop
    (left_vprop1 md_region r1 r2 r3 md_count_v_)
    (ind_varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v_))
       r1 r2 r3);

  let idxs
    : G.erased _
    = elim_vdep
      (vptr r1 `star` vptr r2 `star` vptr r3)
      (ind_varraylist_aux pred1 pred2 pred3 (A.split_l md_region (u32_to_sz md_count_v_)))
  in
  let idx1_ = read r1 in
  let idx2_ = read r2 in
  let idx3_ = read r3 in

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
