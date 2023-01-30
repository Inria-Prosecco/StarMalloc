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

module SL = BlobList

module VR2 = SteelVRefine2
//module Temp = TempLock

open Utils2
open Slots

//let slab_region_len : U32.t = normalize_term (U32.mul page_size slab_max_number)
//unfold let slab_region
//  = r:array U8.t{A.length r = U32.v slab_region_len}
//
//let slab_md_region_len : U32.t = normalize_term (U32.mul 40ul slab_max_number)
//unfold let slab_md_region
//  = r:array U8.t{A.length r = U32.v slab_md_region_len}

//// C binding, no top-level Steel initialization
//val get_slab_region (_:unit)
//  : slab_region
//
//// C binding, no top-level Steel initialization
//val get_slab_md_region (_:unit)
//  : slab_md_region

////TODO
//noextract
//let slab_md_bitmap_length = nb_slots (U32.uint_to_t min_sc)

#push-options "--print_implicits --print_universes"

#set-options "--ide_id_info_off"

unfold
let blob
  = slab_metadata &
    (arr:array U8.t{A.length arr = U32.v page_size})



//[@@__steel_reduce__]
//unfold
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
  (b1: SL.blob)
  (b2: SL.blob)
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
  (b1: SL.blob)
  (b2: SL.blob)
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
  (b1: SL.blob)
  (b2: SL.blob)
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
  (b1: SL.blob)
  (b2: SL.blob)
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
  (b1: SL.blob)
  (b2: SL.blob)
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

module AL = ArrayList


// TODO: to be removed/move apart ; use stdlib
// discussion
let u32_to_sz
  (x:U32.t)
  : Tot (y:US.t{US.v y == U32.v x})
  //: Pure US.t
  //(requires True)
  //(ensures fun y -> US.v y == U32.v x)
  =
  assume (US.fits_u32);
  US.uint32_to_sizet x

open FStar.Mul

#push-options "--z3rlimit 30"
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
  change_slprop_rel
    (A.varray (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (slab_array slab_region md_count))
    (fun x y -> x == y)
    (fun _ -> ());
  let x1 = A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size) in
  let x2 = A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_slprop_rel
    (A.varray (A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))))
    (fun x y -> x == y)
    (fun _ -> ())

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
  change_slprop_rel
    (A.varray (A.split_l (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (A.varray (md_bm_array md_bm_region md_count))
    (fun x y -> x == y)
    (fun _ -> ());
  let x1 = A.split_r (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul) in
  let x2 = A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  change_slprop_rel
    (A.varray (A.split_r (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))))
    (fun x y -> x == y)
    (fun _ -> ())

let md_array
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array SL.cell)
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
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
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
  change_slprop_rel
    (A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul)))
    (A.varray (md_array md_region md_count))
    (fun x y -> x == y)
    (fun _ -> ());
  let x1 = A.split_r (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul) in
  let x2 = A.split_r md_region (u32_to_sz (U32.add md_count 1ul)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  rewrite_slprop
    (A.varray (A.split_r (A.split_r md_region (u32_to_sz (md_count))) (u32_to_sz 1ul)))
    (A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul))))
    (fun _ -> ())



let pred1 (x: U32.t) : prop = U32.eq x 0ul == true
let pred2 (x: U32.t) : prop = U32.eq x 1ul == true
let pred3 (x: U32.t) : prop = U32.eq x 2ul == true


open SteelStarSeqUtils

let status = v:U32.t{U32.v v < 3}

let f
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  (md_region_lv: Seq.lseq status (U32.v md_count))
  (i: U32.t{U32.v i < U32.v md_count})
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
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  (md_region_lv: Seq.lseq status (U32.v md_count))
  (i: U32.t{U32.v i < U32.v md_count})
  : Lemma
  (t_of (f size_class slab_region md_bm_region md_count md_region_lv i)
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

let dataify
  (s: Seq.seq (AL.cell status))
  : Seq.lseq status (Seq.length s)
  =
  let f = fun (c: AL.cell status) -> c.data in
  Seq.map_seq_len f s;
  Seq.map_seq f s

#push-options "--z3rlimit 30"
let ind_varraylist (#a: Type)
  (pred1 pred2 pred3: a -> prop) (r: A.array (AL.cell a))
  (r1 r2 r3: ref US.t)
  //(hd1 hd2 hd3: nat)
  =
  (vptr r1 `star` vptr r2 `star` vptr r3) `vdep`
  (fun (idxs: (US.t & US.t) & US.t) ->
    AL.varraylist pred1 pred2 pred3 r
    (US.v (fst (fst idxs)))
    (US.v (snd (fst idxs)))
    (US.v (snd idxs))
  )

let s_vprop
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{0 < U32.v md_count /\ U32.v md_count < U32.v metadata_max})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (idx1 idx2 idx3: nat)
  =
  AL.varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count))
    idx1 idx2 idx3
  `vdep`
  (fun (x: Seq.lseq (AL.cell status) (U32.v md_count)) ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count (dataify x))
      (f_lemma size_class slab_region md_bm_region md_count (dataify x))
      (SeqUtils.init_u32_refined (U32.v md_count)))

let s_vprop'
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{0 < U32.v md_count /\ U32.v md_count < U32.v metadata_max})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (r1 r2 r3: ref US.t)
  =
  ind_varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count))
    r1 r2 r3
  `vdep`
  (fun x ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count (dataify (dsnd x)))
      (f_lemma size_class slab_region md_bm_region md_count (dataify (dsnd x)))
      (SeqUtils.init_u32_refined (U32.v md_count)))

#push-options "--z3rlimit 75"
assume val allocate_slab_aux_1_full
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: U32.t{0 < U32.v md_count /\ U32.v md_count < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count)))
  (idx1: US.t{US.v idx1 < U32.v md_count})
  (idx2 idx3: US.t)
  (r1 r2 r3: ref US.t)
  //: Steel (array U8.t)
  : SteelT unit
  (
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (f_lemma size_class slab_region md_bm_region md_count (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (SeqUtils.init_u32_refined (U32.v md_count))
  )
  (fun idxs ->
    s_vprop' size_class slab_region md_bm_region md_count md_region r1 r2 r3
  )
  //=
  //let idx1' = AL.remove1
  //  (A.split_l md_region (u32_to_sz md_count))
  //  (US.v idx1) (US.v idx2) (US.v idx3) idx1 in
  //let idx2' = AL.insert3
  //  (A.split_l md_region (u32_to_sz md_count))
  //  (US.v idx1') (US.v idx2) (US.v idx3) idx1 in
  //write_in_place



let a = 42

//#push-options "--compat_pre_typed_indexed_effects"
//#push-options "--z3rlimit 30"
//let allocate_slab_aux_1_partial
//  (size_class: sc)
//  (partial_slabs_ptr empty_slabs_ptr: ref SL.t)
//  (partial_slabs empty_slabs: SL.t)
//  (cell_ptr: SL.t)
//  (cell_content: SL.cell)
//  (b: SL.blob)
//  : Steel unit
//  (
//    slab_vprop size_class (snd b) (fst b) `star`
//    (SAR.vptr cell_ptr `star`
//    vptr empty_slabs_ptr `star`
//    SL.llist (p_empty size_class) (SL.get_next cell_content) `star`
//    vptr partial_slabs_ptr `star`
//    SL.llist (p_partial size_class) partial_slabs)
//  )
//  (fun r ->
//    SL.ind_llist (p_empty size_class) empty_slabs_ptr `star`
//    SL.ind_llist (p_partial size_class) partial_slabs_ptr
//  )
//  (requires fun h0 ->
//    let slab_vprop_data
//      : t_of (slab_vprop size_class (snd b) (fst b))
//      = h0 (slab_vprop size_class (snd b) (fst b)) in
//    let md_seq : Seq.lseq U64.t 4 = dfst (fst slab_vprop_data) in
//    sel partial_slabs_ptr h0 == partial_slabs /\
//    SAR.sel cell_ptr h0 == cell_content /\
//    is_partial size_class md_seq /\
//    SL.get_data cell_content == b)
//  (ensures fun h0 _ h1 ->
//    True
//  )
//  =
//  p_partial_pack size_class b (SL.get_data cell_content);
//  let n_partial = SL.mk_cell partial_slabs (SL.get_data cell_content) in
//  SAR.write cell_ptr n_partial;
//  SL.pack_list (p_partial size_class)
//    cell_ptr
//    partial_slabs
//    (SL.get_data cell_content);
//  write partial_slabs_ptr cell_ptr;
//  SL.pack_ind (p_partial size_class) partial_slabs_ptr cell_ptr;
//  write empty_slabs_ptr (SL.get_next cell_content);
//  SL.pack_ind (p_empty size_class)
//    empty_slabs_ptr
//    (SL.get_next cell_content)
//
//let allocate_slab_aux_1_full
//  (size_class: sc)
//  (full_slabs_ptr empty_slabs_ptr: ref SL.t)
//  (full_slabs empty_slabs: SL.t)
//  (cell_ptr: SL.t)
//  (cell_content: SL.cell)
//  (b: SL.blob)
//  : Steel unit
//  (
//    slab_vprop size_class (snd b) (fst b) `star`
//    (SAR.vptr cell_ptr `star`
//    vptr empty_slabs_ptr `star`
//    SL.llist (p_empty size_class) (SL.get_next cell_content) `star`
//    vptr full_slabs_ptr `star`
//    SL.llist (p_full size_class) full_slabs)
//  )
//  (fun r ->
//    SL.ind_llist (p_empty size_class) empty_slabs_ptr `star`
//    SL.ind_llist (p_full size_class) full_slabs_ptr
//  )
//  (requires fun h0 ->
//    let slab_vprop_data
//      : t_of (slab_vprop size_class (snd b) (fst b))
//      = h0 (slab_vprop size_class (snd b) (fst b)) in
//    let md_seq : Seq.lseq U64.t 4 = dfst (fst slab_vprop_data) in
//    sel full_slabs_ptr h0 == full_slabs /\
//    SAR.sel cell_ptr h0 == cell_content /\
//    is_full size_class md_seq /\
//    SL.get_data cell_content == b)
//  (ensures fun h0 _ h1 ->
//    True
//  )
//  =
//  p_full_pack size_class b (SL.get_data cell_content);
//  let n_full = SL.mk_cell full_slabs (SL.get_data cell_content) in
//  SAR.write cell_ptr n_full;
//  SL.pack_list (p_full size_class)
//    cell_ptr
//    full_slabs
//    (SL.get_data cell_content);
//  write full_slabs_ptr cell_ptr;
//  SL.pack_ind (p_full size_class) full_slabs_ptr cell_ptr;
//  write empty_slabs_ptr (SL.get_next cell_content);
//  SL.pack_ind (p_empty size_class)
//    empty_slabs_ptr
//    (SL.get_next cell_content)

//#push-options "--z3rlimit 50"
//let allocate_slab_aux_1
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
//  (md_count: U32.t{0 < U32.v md_count /\ U32.v md_count < U32.v metadata_max})
//  (idx1 idx2 idx3: US.t)
//  (r1 r2 r3: ref US.t)
//  //: Steel (array U8.t)
//  : Steel unit
//  (
//    vptr r1 `star`
//    vptr r2 `star`
//    vptr r3 `star`
//    s_vprop size_class slab_region md_bm_region md_count md_region (US.v idx1) (US.v idx2) (US.v idx3)
//  )
//  (fun r ->
//    //A.varray r `star`
//    vptr r1 `star`
//    vptr r2 `star`
//    vptr r3 `star`
//    s_vprop size_class slab_region md_bm_region md_count md_region (US.v idx1) (US.v idx2) (US.v idx3)
//  )
//  (requires fun h0 ->
//    sel r1 h0 == idx1 /\
//    sel r2 h0 == idx2 /\
//    sel r3 h0 == idx3 /\
//    idx1 <> AL.null_ptr
//  )
//  (ensures fun _ _ _ -> True)
//  =
//  let s = elim_vdep
//    (AL.varraylist pred1 pred2 pred3
//      (A.split_l md_region (u32_to_sz md_count))
//      (US.v idx1) (US.v idx2) (US.v idx3))
//    (fun (x: Seq.lseq (AL.cell status) (U32.v md_count)) ->
//      starseq
//        #(pos:U32.t{U32.v pos < U32.v md_count})
//        #(t size_class)
//        (f size_class slab_region md_bm_region md_count x)
//        (f_lemma size_class slab_region md_bm_region md_count x)
//       (SeqUtils.init_u32_refined (U32.v md_count)))
//  in
//  let idx1 = read r1 in
//  //let v1 = AL.read_in_place



#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
let allocate_slab_aux_1
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: U32.t{0 < U32.v md_count /\ U32.v md_count < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count)))
  (idx1 idx2 idx3: US.t)
  (r1 r2 r3: ref US.t)
  : Steel (array U8.t)
  (
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count))
      (US.v idx1) (US.v idx2) (US.v idx3)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count md_region_lv)
      (SeqUtils.init_u32_refined (U32.v md_count))
  )
  (fun r ->
    A.varray r `star`
    s_vprop' size_class slab_region md_bm_region md_count md_region r1 r2 r3
  )
  (requires fun h0 ->
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)
  =
  let idx1 = read r1 in
  assume (US.v idx1 < U32.v md_count);
  starseq_unpack_s
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count md_region_lv)
    (SeqUtils.init_u32_refined (U32.v md_count))
    (US.v idx1);
  assume (Seq.index md_region_lv (US.v idx1) == 0ul);
  SeqUtils.init_u32_refined_index (U32.v md_count) (US.v idx1);
  change_slprop_rel
     (f size_class slab_region md_bm_region md_count md_region_lv (Seq.index (SeqUtils.init_u32_refined (U32.v md_count)) (US.v idx1)))
     (p_empty size_class (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1)), slab_array slab_region (U32.uint_to_t (US.v idx1))))
     (fun x y -> x == y)
     (fun _ -> admit ());
  p_empty_unpack size_class 
     (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1)), slab_array slab_region (U32.uint_to_t (US.v idx1)))
     (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1)), slab_array slab_region (U32.uint_to_t (US.v idx1)));
  let r = allocate_slot size_class
    (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1)))
    (slab_array slab_region (U32.uint_to_t (US.v idx1)))
  in
  let cond = allocate_slab_aux_cond size_class
    (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1)))
    (slab_array slab_region (U32.uint_to_t (US.v idx1)))
  in
  if cond then (
   change_slprop_rel
      (slab_vprop size_class
        (slab_array slab_region (U32.uint_to_t (US.v idx1)))
        (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1))))
      (f size_class slab_region md_bm_region md_count (Seq.upd md_region_lv (US.v idx1) 2ul) (Seq.index (SeqUtils.init_u32_refined (U32.v md_count)) (US.v idx1)))
      (fun x y -> x == y)
      (fun _ -> admit ());
    admit ();
    starseq_upd_pack
      #_
      #(pos:U32.t{U32.v pos < U32.v md_count})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count (G.reveal md_region_lv))
      (f size_class slab_region md_bm_region md_count (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (f_lemma size_class slab_region md_bm_region md_count (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (SeqUtils.init_u32_refined (U32.v md_count))
      (SeqUtils.init_u32_refined (U32.v md_count))
      (US.v idx1);
    sladmit ();
    allocate_slab_aux_1_full
      size_class
      slab_region
      md_bm_region
      md_region
      md_count
      md_region_lv
      idx1 idx2 idx3
      r1 r2 r3;
    return r
  ) else (
    sladmit ();
    return r
  )

(*)
  change_equal_slprop
     (f size_class slab_region md_bm_region md_count s (U32.uint_to_t (US.v idx1)))
     (f size_class slab_region md_bm_region md_count s (Seq.index (SeqUtils.init_u32_refined (U32.v md_count)) (US.v idx1)));
  starseq_pack_s
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count s)
    (f_lemma size_class slab_region md_bm_region md_count s)
    (SeqUtils.init_u32_refined (U32.v md_count))
    (US.v idx1)

  //if cond then (
  //  sladmit ()
  //) else (
  //  sladmit ()
  //)





let x = 42
(*)
#push-options "--z3rlimit 75"
inline_for_extraction noextract
let allocate_slab_aux_1
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr full_slabs_ptr: ref SL.t)
  (partial_slabs empty_slabs full_slabs: SL.t)
  : Steel (array U8.t)
  (
  vptr empty_slabs_ptr `star`
  SL.llist (p_empty sc) empty_slabs `star`
  vptr partial_slabs_ptr `star`
  SL.llist (p_partial sc) partial_slabs `star`
  vptr full_slabs_ptr `star`
  SL.llist (p_full sc) full_slabs)
  (fun r ->
  A.varray r `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
  SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_full sc) full_slabs_ptr)
  (requires fun h0 ->
    sel partial_slabs_ptr h0 == partial_slabs /\
    sel empty_slabs_ptr h0 == empty_slabs /\
    sel full_slabs_ptr h0 == full_slabs /\
    not (SL.is_null_t empty_slabs))
  (ensures fun _ _ _ -> True)
  =
  let n_empty = SL.unpack_list (p_empty sc) empty_slabs in
  let b = SL.get_data n_empty in
  p_empty_unpack sc
    (SL.get_data n_empty)
    b;
  let r = allocate_slot sc (fst b) (snd b) in
  let cond = allocate_slab_aux_cond sc (fst b) (snd b) in
  if cond then (
    allocate_slab_aux_1_full
      sc
      full_slabs_ptr
      empty_slabs_ptr
      full_slabs
      (SL.get_next n_empty)
      empty_slabs
      n_empty
      b;
    SL.pack_ind (p_partial sc) partial_slabs_ptr partial_slabs;
    return r
  ) else (
    allocate_slab_aux_1_partial
      sc
      partial_slabs_ptr
      empty_slabs_ptr
      partial_slabs
      (SL.get_next n_empty)
      empty_slabs
      n_empty
      b;
    SL.pack_ind (p_full sc) full_slabs_ptr full_slabs;
    return r
  )
#pop-options

inline_for_extraction noextract
let allocate_slab_aux_2
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref SL.t)
  (partial_slabs empty_slabs: SL.t)
  : Steel (array U8.t)
  (
  vptr empty_slabs_ptr `star`
  SL.llist (p_empty sc) empty_slabs `star`
  vptr partial_slabs_ptr `star`
  SL.llist (p_partial sc) partial_slabs)
  (fun r ->
  A.varray r `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
  SL.ind_llist (p_partial sc) partial_slabs_ptr)
  (requires fun h0 ->
    sel partial_slabs_ptr h0 == partial_slabs /\
    sel empty_slabs_ptr h0 == empty_slabs /\
    not (SL.is_null_t partial_slabs))
  (ensures fun _ _ _ -> True)
  =
  let n_partial = SL.unpack_list (p_partial sc) partial_slabs in
  let b = SL.get_data n_partial in
  p_partial_unpack sc
    (SL.get_data n_partial)
    b;
  let r = allocate_slot sc (fst b) (snd b) in
  let blob0
    : G.erased (t_of (slab_vprop sc (snd b) (fst b)))
    = gget (slab_vprop sc (snd b) (fst b)) in
  let v0 : G.erased (Seq.lseq U64.t 4) = dfst (fst blob0) in
  // TODO: false, but ok for now as nb_slots size_class > 1
  assume (is_partial sc v0);
  p_partial_pack sc
    b
    (SL.get_data n_partial);
  SL.pack_list (p_partial sc)
    partial_slabs
    (SL.get_next n_partial)
    (SL.get_data n_partial);
  SL.pack_ind (p_partial sc) partial_slabs_ptr partial_slabs;
  SL.pack_ind (p_empty sc) empty_slabs_ptr empty_slabs;
  return r
#pop-options

#push-options "--z3rlimit 30"
let alloc_metadata_aux
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  //: Steel (SL.t blob)
  : Steel SL.blob
  (
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz md_count))
  )
  //TODO: add a refinement over a md_count ref, discussion with Aymeric
  ////`star` vptr md_count)
  (fun r ->
    //TODO: these 2 varrays will be packed into slab_vprop, then into the p_empty part of SL.llist
    //A.varray (snd r) `star`
    A.varray (A.split_l (snd r) 0sz) `star`
    slab_vprop_aux size_class (A.split_r (snd r) 0sz) (Seq.create 4 0UL) `star`
    A.varray (fst r) `star`
    //TODO: this varray will be somehow casted into the ref that corresponds to the SL.t type
    A.varray (md_array md_region md_count) `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
  )
  (requires fun h0 ->
    (U32.v page_size) % (U32.v size_class) == 0 /\
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) h0)
  )
  (ensures fun h0 r h1 ->
    A.asel (fst r) h1 == Seq.create 4 0UL /\
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) h1)
  )
  =
  slab_region_mon_split slab_region md_count;
  md_bm_region_mon_split md_bm_region md_count;
  md_region_mon_split md_region md_count;
  let md_bm = md_bm_array md_bm_region md_count in
  let v = gget (A.varray (md_bm_array md_bm_region md_count)) in
  let slab = slab_array slab_region md_count in
  let b = (md_bm, slab) in
  change_slprop_rel
    (A.varray (slab_array slab_region md_count) `star`
    A.varray (md_bm_array md_bm_region md_count))
    (A.varray (snd b) `star` A.varray (fst b))
    (fun x y -> x == y)
    (fun _ -> ());
  A.ghost_split (snd b) 0sz;
  Helpers.slab_to_slots size_class (A.split_r (snd b) 0sz);
  return b
#pop-options

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

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
let alloc_metadata_aux2
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  : Steel (SL.t & (G.erased U32.t))
  (
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz md_count))
  )
  (fun r ->
    SL.llist (p_empty size_class) (fst r) `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
  )
  (requires fun h0 ->
    (U32.v page_size) % (U32.v size_class) == 0 /\
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) h0))
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) (fst r) h1) = 1 /\
    G.reveal (snd r) = U32.add md_count 1ul /\
    U32.v (G.reveal (snd r)) <= U32.v metadata_max /\
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) h1)
  )
  =
  let b : SL.blob = alloc_metadata_aux md_count size_class slab_region md_bm_region md_region in
  empty_md_is_properly_zeroed size_class;
  intro_slab_vprop size_class (fst b) (Seq.create 4 0UL) (snd b);
  zeroes_impl_empty size_class (Seq.create 4 0UL);
  p_empty_pack size_class b b;
  SAR.intro_vptr (md_array md_region md_count);
  SL.intro_singleton_llist_no_alloc (p_empty size_class) (md_array md_region md_count) b;
  return (md_array md_region md_count, G.hide (U32.add md_count 1ul))
#pop-options

let alloc_metadata_sl1
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
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
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
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

#push-options "--z3rlimit 100"
let alloc_metadata
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
  : Steel (SL.t & G.erased U32.t)
  (
    vptr md_count `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v)))
  )
  (fun r ->
    vptr md_count `star`
    SL.llist (p_empty size_class) (fst r) `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul)))
  )
  (requires fun h0 ->
    (U32.v page_size) % (U32.v size_class) == 0 /\
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) h0) /\
    sel md_count h0 = G.reveal md_count_v
  )
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) (fst r) h1) = 1 /\
    sel md_count h0 = G.reveal md_count_v /\
    sel md_count h1 = U32.add (sel md_count h0) 1ul /\
    sel md_count h1 = G.reveal (snd r) /\
    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) h1)
  )
  =
  let md_count_v0 = read md_count in
  assert (md_count_v0 == G.reveal md_count_v);
  change_equal_slprop
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v))))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v0 page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v0 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz md_count_v0)));
  let r = alloc_metadata_aux2 md_count_v0 size_class slab_region md_bm_region md_region in
  assert (U32.add md_count_v0 1ul == U32.add (G.reveal md_count_v) 1ul);
  change_equal_slprop
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count_v0 1ul))))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul))));
  write md_count (U32.add md_count_v0 1ul);
  let md_count_v1 = read md_count in
  assert (md_count_v1 == G.reveal (snd r));
  //assert (U32.v md_count_v1 <= U32.v metadata_max);
  return r
#pop-options

//TODO: move it inside SL lib
let unpack_list_singleton
  (p: SL.blob -> vprop)
  (ptr: SL.t)
  : Steel SL.cell
  (SL.llist p ptr)
  (fun n -> SAR.vptr ptr `star` p (SL.get_data n))
  (requires fun h0 ->
    L.length (SL.v_llist p ptr h0) = 1)
  (ensures fun h0 n h1 ->
    SL.v_llist p ptr h0 ==
      (SL.get_data (SAR.sel ptr h1)) :: [] /\
    SAR.sel ptr h1 == n)
  =
  SL.cons_is_not_null p ptr;
  let n = SL.unpack_list p ptr in
  //TODO: FIXME (add AVL-like helper)
  drop (SL.llist p (SL.get_next n));
  return n

#push-options "--z3rlimit 100"
let alloc_metadata'
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
  : Steel SL.t
  (
    vptr md_count `star`
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v)))
  )
  (fun r ->
    vptr md_count `star`
    SL.llist (p_empty size_class) r `star`
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul)))
  )
  (requires fun h0 ->
    sel md_count h0 = G.reveal md_count_v /\
    (U32.v page_size) % (U32.v size_class) == 0
  )
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) r h1) = 1 /\
    sel md_count h0 = G.reveal md_count_v /\
    sel md_count h1 = U32.add (sel md_count h0) 1ul /\
    U32.v (U32.add (sel md_count h0) 1ul) <= U32.v metadata_max
    //sel md_count h1 = G.reveal (snd r)
  )
  =
  elim_vrefine
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))))
    zf_u8;
  elim_vrefine
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))))
    zf_u64;
  let r = alloc_metadata size_class slab_region md_bm_region md_region md_count md_count_v in
  intro_vrefine
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))))
    zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))))
    zf_u64;
  return (fst r)
#pop-options

open SteelVRefineDep

let vp_aux
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v <= U32.v metadata_max == true})
  : vprop
  =
  (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
    `vrefine` zf_u64) `star`
  A.varray (A.split_r md_region (u32_to_sz v))

let vp_aux_lt
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v < U32.v metadata_max == true})
  : vprop
  =
  (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
    `vrefine` zf_u64) `star`
  A.varray (A.split_r md_region (u32_to_sz v))

let vp_aux_lt_equal_lemma
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v < U32.v metadata_max == true})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    vp_aux_lt slab_region md_bm_region md_region v
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
  sel_of (vp_aux_lt slab_region md_bm_region md_region v) m
  )
  = ()

let vp_aux_equal_lemma
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
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
    vp_aux slab_region md_bm_region md_region v
  )) m /\
  sel_of (
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz v))
  ) m
  ==
  sel_of (vp_aux slab_region md_bm_region md_region v) m
  )
  = ()

(*)
#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let alloc_metadata2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel SL.t
  (
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (fun r ->
    SL.llist (p_empty size_class) r `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (requires fun h0 ->
    let x = h0 (
      vrefinedep
        (vptr md_count)
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v -> vp_aux slab_region md_bm_region md_region v)
      ) in
    U32.v (dfst x) < U32.v metadata_max /\
    (U32.v page_size) % (U32.v size_class) == 0)
  (ensures fun h0 r h1 ->
    FStar.List.Tot.length (SL.v_llist (p_empty size_class) r h1) = 1
  )
  =
  let x
    = elim_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> vp_aux slab_region md_bm_region md_region v)
  in
  let x'
    : G.erased (x:U32.t{U32.v x < U32.v metadata_max})
    = G.hide (G.reveal x <: x:U32.t{U32.v x < U32.v metadata_max}) in
  //TODO: hideous coercion that leads to 2 change_slprop_rel
  change_equal_slprop
    (vp_aux slab_region md_bm_region md_region (G.reveal x))
    (vp_aux_lt slab_region md_bm_region md_region (G.reveal x'));
  change_slprop_rel
    (vp_aux_lt slab_region md_bm_region md_region (G.reveal x'))
    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x') page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x') 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal x'))))
    (fun x y -> x == y)
    (fun m -> vp_aux_lt_equal_lemma slab_region md_bm_region md_region (G.reveal x') m);
  let r = alloc_metadata' size_class slab_region md_bm_region md_region md_count x' in
  //TODO: hideous coercion that leads to 2 change_slprop_rel
  change_slprop_rel
    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x') 1ul))))
    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x') 1ul))
    (fun x y -> x == y)
    (fun m -> vp_aux_equal_lemma slab_region md_bm_region md_region (U32.add (G.reveal x') 1ul) m);
  change_equal_slprop
    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x') 1ul))
    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x) 1ul));
  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> vp_aux slab_region md_bm_region md_region v)
    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x) 1ul));
  return r
#pop-options

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
inline_for_extraction noextract
let allocate_slab_aux_3
  (size_class: sc)
  (empty_slabs_ptr: ref SL.t)
  (empty_slabs: SL.t)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel SL.t
  (
    vptr empty_slabs_ptr `star`
    SL.llist (p_empty size_class) empty_slabs `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (fun r ->
    vptr empty_slabs_ptr `star`
    SL.llist (p_empty size_class) r `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (requires fun h0 ->
    let x = h0 (
      vrefinedep
        (vptr md_count)
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v -> vp_aux slab_region md_bm_region md_region v)
      ) in
    U32.v (dfst x) < U32.v metadata_max /\
    (U32.v page_size) % (U32.v size_class) == 0)
  (ensures fun h0 r h1 ->
    sel empty_slabs_ptr h1 == r /\
    //sel partial_slabs_ptr h1 == sel partial_slabs_ptr h0 /\
    not (SL.is_null_t r))
  =
  let r = alloc_metadata2 size_class slab_region md_bm_region md_region md_count in
  let n_empty = unpack_list_singleton (p_empty size_class) r in
  let n_empty_2 = SL.mk_cell empty_slabs (SL.get_data n_empty) in
  SAR.write r n_empty_2;
  SL.pack_list (p_empty size_class)
    r
    empty_slabs
    (SL.get_data n_empty);
  SL.cons_is_not_null (p_empty size_class) r;
  write empty_slabs_ptr r;
  return r
#pop-options

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let allocate_slab_check_md_count
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel bool
  (
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
    ) in
    blob0 == blob1 /\
    r == (U32.v (dfst blob0) < U32.v metadata_max)
  )
  =
  let x0 = gget (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  ) in
  let x
    = elim_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> vp_aux slab_region md_bm_region md_region v)
  in
  let r = read md_count in
  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> vp_aux slab_region md_bm_region md_region v)
    (vp_aux slab_region md_bm_region md_region (G.reveal x));
  let x1 = gget (vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  ) in
  assert (dfst x0 == dfst x1);
  assert (dsnd x0 == dsnd x1);
  return (U32.lt r metadata_max)


#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let allocate_slab
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr full_slabs_ptr: ref SL.t)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel (array U8.t & G.erased bool)
  (
    SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
    SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
    SL.ind_llist (p_full sc) full_slabs_ptr `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (fun r ->
    (if (G.reveal (snd r)) then A.varray (fst r) else emp) `star`
    SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
    SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
    SL.ind_llist (p_full sc) full_slabs_ptr `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> vp_aux slab_region md_bm_region md_region v)
  )
  (requires fun h0 ->
    (U32.v page_size) % (U32.v sc) == 0)
  (ensures fun _ _ _ -> True)
  =
  let partial_slabs
    = SL.unpack_ind (p_partial sc) partial_slabs_ptr in
  let empty_slabs
    = SL.unpack_ind (p_empty sc) empty_slabs_ptr in
  let full_slabs
    = SL.unpack_ind (p_full sc) full_slabs_ptr in
  if (not (SL.is_null_t partial_slabs)) then (
    let r = allocate_slab_aux_2 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    SL.pack_ind (p_full sc) full_slabs_ptr full_slabs;
    return (r, G.hide true)
  ) else if (not (SL.is_null_t empty_slabs)) then (
    let r = allocate_slab_aux_1 sc
      partial_slabs_ptr empty_slabs_ptr full_slabs_ptr
      partial_slabs empty_slabs full_slabs in
    return (r, G.hide true)
  ) else (
    let b = allocate_slab_check_md_count slab_region md_bm_region md_region md_count in
    if b then (
      let n_empty_slabs = allocate_slab_aux_3 sc
        empty_slabs_ptr empty_slabs
        slab_region md_bm_region md_region md_count in
      let r = allocate_slab_aux_1 sc
        partial_slabs_ptr empty_slabs_ptr full_slabs_ptr
        partial_slabs n_empty_slabs full_slabs in
      change_equal_slprop
        (A.varray r)
        (if b then A.varray r else emp);
      return (r, G.hide b)
    ) else (
      SL.pack_ind (p_empty sc) empty_slabs_ptr empty_slabs;
      SL.pack_ind (p_partial sc) partial_slabs_ptr partial_slabs;
      SL.pack_ind (p_full sc) full_slabs_ptr full_slabs;
      let r = A.null #U8.t in
      change_equal_slprop
        emp
        (if b then A.varray r else emp);
      return (r, G.hide b)
    )
  )
#pop-options
