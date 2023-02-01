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

open Utils2
open Slots
open SteelStarSeqUtils
open FStar.Mul

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

#push-options "--print_implicits --print_universes"
#set-options "--ide_id_info_off"

let status = v:U32.t{U32.v v < 3}

let pred1 (x: U32.t) : prop = U32.eq x 0ul == true
let pred2 (x: U32.t) : prop = U32.eq x 1ul == true
let pred3 (x: U32.t) : prop = U32.eq x 2ul == true

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
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array (AL.cell status))
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
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
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

let f
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count <= U32.v metadata_max})
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
  (md_count: U32.t{U32.v md_count <= U32.v metadata_max})
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

let left_vprop_deprecated
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count <= U32.v metadata_max})
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

let left_vprop1
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count <= U32.v metadata_max})
  (r1 r2 r3: ref US.t)
  =
  ind_varraylist pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz md_count))
    r1 r2 r3

let left_vprop2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count <= U32.v metadata_max})
  (x: Seq.lseq status (U32.v md_count))
  =
  starseq
    #(pos:U32.t{U32.v pos < U32.v md_count})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count x)
    (f_lemma size_class slab_region md_bm_region md_count x)
    (SeqUtils.init_u32_refined (U32.v md_count))

let left_vprop
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count <= U32.v metadata_max})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (r1 r2 r3: ref US.t)
  =
  left_vprop1 md_region md_count r1 r2 r3 `vdep`
  (fun x ->
    left_vprop2 size_class slab_region md_bm_region md_count (dataify (dsnd x))
  )

open SteelVRefineDep

#push-options "--z3rlimit 75"
assume val allocate_slab_aux_1_partial
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count_v)))
  (idx1: US.t{US.v idx1 < U32.v md_count_v})
  (idx2 idx3: US.t)
  //: Steel (array U8.t)
  : SteelT unit
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
      (fun v -> left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3)
  )

#push-options "--compat_pre_typed_indexed_effects"
let allocate_slab_aux_1_full
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count_v)))
  (idx1: US.t{US.v idx1 < U32.v md_count_v})
  (idx2 idx3: US.t)
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
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)
  =
  //assume (t_of (
  //  AL.varraylist pred1 pred2 pred3
  //    (A.split_l md_region (u32_to_sz md_count))
  //    (US.v idx1) (US.v idx2) (US.v idx3))
  //  ==
  //  v:Seq.seq (AL.cell status){AL.varraylist_refine pred1 pred2 pred3 (US.v idx1) (US.v idx2) (US.v idx3) v});
  //let l
  //  = gget (
  //  AL.varraylist pred1 pred2 pred3
  //    (A.split_l md_region (u32_to_sz md_count))
  //    (US.v idx1) (US.v idx2) (US.v idx3)
  //) in
  //assume (AL.mem (US.v idx1) (US.v idx1) (G.reveal l));
  admit ();
  let idx1' = AL.remove1 #_ #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    (US.v idx1) (US.v idx2) (US.v idx3) idx1 in
  AL.insert3 #_ #pred1 #pred2 #pred3
    (A.split_l md_region (u32_to_sz md_count_v))
    idx3 idx1' (US.v idx2) idx1 2ul;
  write r1 (US.uint_to_t idx1');
  write r2 idx1;
  intro_vdep
    (vptr r1 `star` vptr r2 `star` vptr r3)
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      idx1' (US.v idx2) (US.v idx1))
    (fun (idxs: (US.t & US.t) & US.t) ->
      AL.varraylist pred1 pred2 pred3
        (A.split_l md_region (u32_to_sz md_count_v))

      (US.v (fst (fst idxs)))
      (US.v (snd (fst idxs)))
      (US.v (snd idxs))
    );
  slassert (left_vprop1 md_region md_count_v r1 r2 r3);
  slassert (left_vprop2 size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul));
  intro_vdep
    (left_vprop1 md_region md_count_v r1 r2 r3)
    (left_vprop2 size_class slab_region md_bm_region md_count_v
      (Seq.upd (G.reveal md_region_lv) (US.v idx1) 2ul))
    (fun x -> left_vprop2 size_class slab_region md_bm_region md_count_v (dataify (dsnd x)));
  slassert (left_vprop size_class slab_region md_bm_region md_count_v md_region r1 r2 r3);
  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3)
    (left_vprop size_class slab_region md_bm_region md_count_v md_region r1 r2 r3)

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

let _ = 42

#push-options "--print_implicits"

#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
let allocate_slab_aux_1
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count_v)))
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
      (fun v -> left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx1 <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)
  =
  let idx1' : US.t = read r1 in
  change_equal_slprop
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3))
    (AL.varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1') (US.v idx2) (US.v idx3));
  assume (US.v idx1' < U32.v md_count_v);
  starseq_unpack_s
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (US.v idx1');
  assume (Seq.index md_region_lv (US.v idx1') == 0ul);
  SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v idx1');
  change_slprop_rel
     (f size_class slab_region md_bm_region md_count_v md_region_lv (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx1')))
     (p_empty size_class (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1')), slab_array slab_region (U32.uint_to_t (US.v idx1'))))
     (fun x y -> x == y)
     (fun _ -> admit ());
  p_empty_unpack size_class 
     (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1')), slab_array slab_region (U32.uint_to_t (US.v idx1')))
     (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1')), slab_array slab_region (U32.uint_to_t (US.v idx1')));
  let r = allocate_slot size_class
    (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1')))
    (slab_array slab_region (U32.uint_to_t (US.v idx1')))
  in
  let cond = allocate_slab_aux_cond size_class
    (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1')))
    (slab_array slab_region (U32.uint_to_t (US.v idx1')))
  in
  if cond then (
   change_slprop_rel
      (slab_vprop size_class
        (slab_array slab_region (U32.uint_to_t (US.v idx1')))
        (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1'))))
      (f size_class slab_region md_bm_region md_count_v
        (Seq.upd md_region_lv (US.v idx1') 2ul)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx1')))
      (fun x y -> x == y)
      (fun _ -> admit ());
    admit ();
    starseq_upd_pack
      #_
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1') 2ul))
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1') 2ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
      (US.v idx1');
    allocate_slab_aux_1_full
      size_class
      slab_region
      md_bm_region
      md_region
      md_count
      r1 r2 r3
      md_count_v
      md_region_lv
      idx1' idx2 idx3;
    return r
  ) else (
    change_slprop_rel
      (slab_vprop size_class
        (slab_array slab_region (U32.uint_to_t (US.v idx1')))
        (md_bm_array md_bm_region (U32.uint_to_t (US.v idx1'))))
      (f size_class slab_region md_bm_region md_count_v
        (Seq.upd md_region_lv (US.v idx1') 1ul)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx1')))
      (fun x y -> x == y)
      (fun _ -> admit ());
    admit ();
    starseq_upd_pack
      #_
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1') 1ul))
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx1') 1ul))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
      (US.v idx1');
    allocate_slab_aux_1_partial
      size_class
      slab_region
      md_bm_region
      md_region
      md_count
      r1 r2 r3
      md_count_v
      md_region_lv
      idx1' idx2 idx3;
    return r
  )

assume val allocate_slab_aux_2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count_v)))
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
      (fun v -> left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3)
  )
  (requires fun h0 ->
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    idx2 <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)

//#push-options "--z3rlimit 30"
//let alloc_metadata_aux
//  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
//  //: Steel (SL.t blob)
//  : Steel SL.blob
//  (
//    A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz md_count))
//  )
//  //TODO: add a refinement over a md_count ref, discussion with Aymeric
//  ////`star` vptr md_count)
//  (fun r ->
//    //TODO: these 2 varrays will be packed into slab_vprop, then into the p_empty part of SL.llist
//    //A.varray (snd r) `star`
//    A.varray (A.split_l (snd r) 0sz) `star`
//    slab_vprop_aux size_class (A.split_r (snd r) 0sz) (Seq.create 4 0UL) `star`
//    A.varray (fst r) `star`
//    //TODO: this varray will be somehow casted into the ref that corresponds to the SL.t type
//    A.varray (md_array md_region md_count) `star`
//    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
//  )
//  (requires fun h0 ->
//    (U32.v page_size) % (U32.v size_class) == 0 /\
//    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) h0) /\
//    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) h0)
//  )
//  (ensures fun h0 r h1 ->
//    A.asel (fst r) h1 == Seq.create 4 0UL /\
//    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) h1) /\
//    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) h1)
//  )
//  =
//  slab_region_mon_split slab_region md_count;
//  md_bm_region_mon_split md_bm_region md_count;
//  md_region_mon_split md_region md_count;
//  let md_bm = md_bm_array md_bm_region md_count in
//  let v = gget (A.varray (md_bm_array md_bm_region md_count)) in
//  let slab = slab_array slab_region md_count in
//  let b = (md_bm, slab) in
//  change_slprop_rel
//    (A.varray (slab_array slab_region md_count) `star`
//    A.varray (md_bm_array md_bm_region md_count))
//    (A.varray (snd b) `star` A.varray (fst b))
//    (fun x y -> x == y)
//    (fun _ -> ());
//  A.ghost_split (snd b) 0sz;
//  Helpers.slab_to_slots size_class (A.split_r (snd b) 0sz);
//  return b
//#pop-options

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

//TODO: remove
//#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
//let alloc_metadata_aux2
//  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
//  : Steel (SL.t & (G.erased U32.t))
//  (
//    A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz md_count))
//  )
//  (fun r ->
//    SL.llist (p_empty size_class) (fst r) `star`
//    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
//  )
//  (requires fun h0 ->
//    (U32.v page_size) % (U32.v size_class) == 0 /\
//    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) h0) /\
//    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) h0))
//  (ensures fun h0 r h1 ->
//    L.length (SL.v_llist (p_empty size_class) (fst r) h1) = 1 /\
//    G.reveal (snd r) = U32.add md_count 1ul /\
//    U32.v (G.reveal (snd r)) <= U32.v metadata_max /\
//    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) h1) /\
//    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) h1)
//  )
//  =
//  let b : SL.blob = alloc_metadata_aux md_count size_class slab_region md_bm_region md_region in
//  empty_md_is_properly_zeroed size_class;
//  intro_slab_vprop size_class (fst b) (Seq.create 4 0UL) (snd b);
//  zeroes_impl_empty size_class (Seq.create 4 0UL);
//  p_empty_pack size_class b b;
//  SAR.intro_vptr (md_array md_region md_count);
//  SL.intro_singleton_llist_no_alloc (p_empty size_class) (md_array md_region md_count) b;
//  return (md_array md_region md_count, G.hide (U32.add md_count 1ul))
//#pop-options

let alloc_metadata_sl1
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
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
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
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

////TODO: remove
//#push-options "--z3rlimit 100"
//let alloc_metadata
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
//  (md_count: ref U32.t)
//  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
//  : Steel (SL.t & G.erased U32.t)
//  (
//    vptr md_count `star`
//    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v)))
//  )
//  (fun r ->
//    vptr md_count `star`
//    SL.llist (p_empty size_class) (fst r) `star`
//    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul)))
//  )
//  (requires fun h0 ->
//    (U32.v page_size) % (U32.v size_class) == 0 /\
//    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) h0) /\
//    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) h0) /\
//    sel md_count h0 = G.reveal md_count_v
//  )
//  (ensures fun h0 r h1 ->
//    L.length (SL.v_llist (p_empty size_class) (fst r) h1) = 1 /\
//    sel md_count h0 = G.reveal md_count_v /\
//    sel md_count h1 = U32.add (sel md_count h0) 1ul /\
//    sel md_count h1 = G.reveal (snd r) /\
//    zf_u8 (A.asel (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) h1) /\
//    zf_u64 (A.asel (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) h1)
//  )
//  =
//  let md_count_v0 = read md_count in
//  assert (md_count_v0 == G.reveal md_count_v);
//  change_equal_slprop
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v))))
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v0 page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v0 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz md_count_v0)));
//  let r = alloc_metadata_aux2 md_count_v0 size_class slab_region md_bm_region md_region in
//  assert (U32.add md_count_v0 1ul == U32.add (G.reveal md_count_v) 1ul);
//  change_equal_slprop
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count_v0 1ul) 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count_v0 1ul))))
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) `star`
//    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) `star`
//    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul))));
//  write md_count (U32.add md_count_v0 1ul);
//  let md_count_v1 = read md_count in
//  assert (md_count_v1 == G.reveal (snd r));
//  //assert (U32.v md_count_v1 <= U32.v metadata_max);
//  return r
//#pop-options

////TODO: move it inside SL lib
//let unpack_list_singleton
//  (p: SL.blob -> vprop)
//  (ptr: SL.t)
//  : Steel SL.cell
//  (SL.llist p ptr)
//  (fun n -> SAR.vptr ptr `star` p (SL.get_data n))
//  (requires fun h0 ->
//    L.length (SL.v_llist p ptr h0) = 1)
//  (ensures fun h0 n h1 ->
//    SL.v_llist p ptr h0 ==
//      (SL.get_data (SAR.sel ptr h1)) :: [] /\
//    SAR.sel ptr h1 == n)
//  =
//  SL.cons_is_not_null p ptr;
//  let n = SL.unpack_list p ptr in
//  //TODO: FIXME (add AVL-like helper)
//  drop (SL.llist p (SL.get_next n));
//  return n

//TODO: remove
//#push-options "--z3rlimit 100"
//let alloc_metadata'
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
//  (md_count: ref U32.t)
//  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
//  : Steel SL.t
//  (
//    vptr md_count `star`
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size)))
//      `vrefine` zf_u8) `star`
//    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul)))
//      `vrefine` zf_u64) `star`
//    A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v)))
//  )
//  (fun r ->
//    vptr md_count `star`
//    SL.llist (p_empty size_class) r `star`
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size)))
//      `vrefine` zf_u8) `star`
//    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul)))
//      `vrefine` zf_u64) `star`
//    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul)))
//  )
//  (requires fun h0 ->
//    sel md_count h0 = G.reveal md_count_v /\
//    (U32.v page_size) % (U32.v size_class) == 0
//  )
//  (ensures fun h0 r h1 ->
//    L.length (SL.v_llist (p_empty size_class) r h1) = 1 /\
//    sel md_count h0 = G.reveal md_count_v /\
//    sel md_count h1 = U32.add (sel md_count h0) 1ul /\
//    U32.v (U32.add (sel md_count h0) 1ul) <= U32.v metadata_max
//    //sel md_count h1 = G.reveal (snd r)
//  )
//  =
//  elim_vrefine
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))))
//    zf_u8;
//  elim_vrefine
//    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))))
//    zf_u64;
//  let r = alloc_metadata size_class slab_region md_bm_region md_region md_count md_count_v in
//  intro_vrefine
//    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))))
//    zf_u8;
//  intro_vrefine
//    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))))
//    zf_u64;
//  return (fst r)
//#pop-options

open SteelVRefineDep

let right_vprop
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v <= U32.v metadata_max == true})
  : vprop
  =
  (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
    `vrefine` zf_u64) `star`
  A.varray (A.split_r md_region (u32_to_sz v))

let right_vprop_lt
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v < U32.v metadata_max == true})
  : vprop
  =
  (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
    `vrefine` zf_u64) `star`
  A.varray (A.split_r md_region (u32_to_sz v))

let right_vprop_lt_equal_lemma
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (v: U32.t{U32.v v < U32.v metadata_max == true})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    right_vprop_lt slab_region md_bm_region md_region v
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
  sel_of (right_vprop_lt slab_region md_bm_region md_region v) m
  )
  = ()

let right_vprop_equal_lemma
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
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

////TODO: remove
//#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
//let alloc_metadata2
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
//  (md_count: ref U32.t)
//  : Steel SL.t
//  (
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  )
//  (fun r ->
//    SL.llist (p_empty size_class) r `star`
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  )
//  (requires fun h0 ->
//    let x = h0 (
//      vrefinedep
//        (vptr md_count)
//        (fun x -> U32.v x <= U32.v metadata_max == true)
//        (fun v -> vp_aux slab_region md_bm_region md_region v)
//      ) in
//    U32.v (dfst x) < U32.v metadata_max /\
//    (U32.v page_size) % (U32.v size_class) == 0)
//  (ensures fun h0 r h1 ->
//    FStar.List.Tot.length (SL.v_llist (p_empty size_class) r h1) = 1
//  )
//  =
//  let x
//    = elim_vrefinedep
//    (vptr md_count)
//    (fun x -> U32.v x <= U32.v metadata_max == true)
//    (fun v -> vp_aux slab_region md_bm_region md_region v)
//  in
//  let x'
//    : G.erased (x:U32.t{U32.v x < U32.v metadata_max})
//    = G.hide (G.reveal x <: x:U32.t{U32.v x < U32.v metadata_max}) in
//  //TODO: hideous coercion that leads to 2 change_slprop_rel
//  change_equal_slprop
//    (vp_aux slab_region md_bm_region md_region (G.reveal x))
//    (vp_aux_lt slab_region md_bm_region md_region (G.reveal x'));
//  change_slprop_rel
//    (vp_aux_lt slab_region md_bm_region md_region (G.reveal x'))
//    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x') page_size)))
//      `vrefine` zf_u8) `star`
//    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x') 4ul)))
//      `vrefine` zf_u64) `star`
//    A.varray (A.split_r md_region (u32_to_sz (G.reveal x'))))
//    (fun x y -> x == y)
//    (fun m -> vp_aux_lt_equal_lemma slab_region md_bm_region md_region (G.reveal x') m);
//  let r = alloc_metadata' size_class slab_region md_bm_region md_region md_count x' in
//  //TODO: hideous coercion that leads to 2 change_slprop_rel
//  change_slprop_rel
//    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) page_size)))
//      `vrefine` zf_u8) `star`
//    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) 4ul)))
//      `vrefine` zf_u64) `star`
//    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x') 1ul))))
//    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x') 1ul))
//    (fun x y -> x == y)
//    (fun m -> vp_aux_equal_lemma slab_region md_bm_region md_region (U32.add (G.reveal x') 1ul) m);
//  change_equal_slprop
//    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x') 1ul))
//    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x) 1ul));
//  intro_vrefinedep
//    (vptr md_count)
//    (fun x -> U32.v x <= U32.v metadata_max == true)
//    (fun v -> vp_aux slab_region md_bm_region md_region v)
//    (vp_aux slab_region md_bm_region md_region (U32.add (G.reveal x) 1ul));
//  return r
//#pop-options

assume val allocate_slab_aux_3
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count_v)))
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
    U32.v md_count_v < U32.v metadata_max)
  (ensures fun h0 idx1' h1 ->
    idx1' <> AL.null_ptr /\
    sel r1 h1 == idx1' /\
    sel r2 h1 == sel r2 h0 /\
    sel r3 h1 == sel r3 h0 /\
    md_count_v == sel md_count h0 /\
    sel md_count h1 = U32.add (sel md_count h0) 1ul
  )


//#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
//inline_for_extraction noextract
//let allocate_slab_aux_3
//  (size_class: sc)
//  (empty_slabs_ptr: ref SL.t)
//  (empty_slabs: SL.t)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
//  (md_count: ref U32.t)
//  : Steel SL.t
//  (
//    vptr empty_slabs_ptr `star`
//    SL.llist (p_empty size_class) empty_slabs `star`
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  )
//  (fun r ->
//    vptr empty_slabs_ptr `star`
//    SL.llist (p_empty size_class) r `star`
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  )
//  (requires fun h0 ->
//    let x = h0 (
//      vrefinedep
//        (vptr md_count)
//        (fun x -> U32.v x <= U32.v metadata_max == true)
//        (fun v -> vp_aux slab_region md_bm_region md_region v)
//      ) in
//    U32.v (dfst x) < U32.v metadata_max /\
//    (U32.v page_size) % (U32.v size_class) == 0)
//  (ensures fun h0 r h1 ->
//    sel empty_slabs_ptr h1 == r /\
//    //sel partial_slabs_ptr h1 == sel partial_slabs_ptr h0 /\
//    not (SL.is_null_t r))
//  =
//  let r = alloc_metadata2 size_class slab_region md_bm_region md_region md_count in
//  let n_empty = unpack_list_singleton (p_empty size_class) r in
//  let n_empty_2 = SL.mk_cell empty_slabs (SL.get_data n_empty) in
//  SAR.write r n_empty_2;
//  SL.pack_list (p_empty size_class)
//    r
//    empty_slabs
//    (SL.get_data n_empty);
//  SL.cons_is_not_null (p_empty size_class) r;
//  write empty_slabs_ptr r;
//  return r
//#pop-options

//#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
//let allocate_slab_check_md_count
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array SL.cell{A.length md_region = U32.v metadata_max})
//  (md_count: ref U32.t)
//  : Steel bool
//  (
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  )
//  (fun _ ->
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  )
//  (requires fun _ -> True)
//  (ensures fun h0 r h1 ->
//    let blob0
//      = h0 (vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//    ) in
//    let blob1
//      = h1 (vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//    ) in
//    blob0 == blob1 /\
//    r == (U32.v (dfst blob0) < U32.v metadata_max)
//  )
//  =
//  let x0 = gget (vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  ) in
//  let x
//    = elim_vrefinedep
//    (vptr md_count)
//    (fun x -> U32.v x <= U32.v metadata_max == true)
//    (fun v -> vp_aux slab_region md_bm_region md_region v)
//  in
//  let r = read md_count in
//  intro_vrefinedep
//    (vptr md_count)
//    (fun x -> U32.v x <= U32.v metadata_max == true)
//    (fun v -> vp_aux slab_region md_bm_region md_region v)
//    (vp_aux slab_region md_bm_region md_region (G.reveal x));
//  let x1 = gget (vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v -> vp_aux slab_region md_bm_region md_region v)
//  ) in
//  assert (dfst x0 == dfst x1);
//  assert (dsnd x0 == dsnd x1);
//  return (U32.lt r metadata_max)

assume val pack_right_and_refactor_vrefine_dep
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  : SteelGhostT unit opened
  (
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v -> left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3)
    `star`
    right_vprop slab_region md_bm_region md_region md_count_v
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3 `star`
         right_vprop slab_region md_bm_region md_region v)
  )

module P = Steel.FractionalPermission

#push-options "--z3rlimit 30"
let allocate_slab'
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq status (U32.v md_count_v)))
  (idx1 idx2 idx3: US.t)
  : Steel (array U8.t)
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
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3 `star`
         right_vprop slab_region md_bm_region md_region v)
  )
  (requires fun h0 ->
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    md_count_v == sel md_count h0
  )
  (ensures fun _ _ _ -> True)
  =
  if (idx2 <> AL.null_ptr) then (
    assume (0 < U32.v md_count_v);
    let r = allocate_slab_aux_2 size_class
      slab_region md_bm_region md_region
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
    assume (0 < U32.v md_count_v);
    let r = allocate_slab_aux_1 size_class
      slab_region md_bm_region md_region
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
        slab_region md_bm_region md_region
        md_count r1 r2 r3
        md_count_v md_region_lv
        idx1 idx2 idx3 in
      let r = allocate_slab_aux_1 size_class
        slab_region md_bm_region md_region
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
      sladmit ();
      return (A.null #U8.t)
    )
  )

#push-options "--z3rlimit 30"
assume val allocate_slab
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (AL.cell status){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  : SteelT (array U8.t)
  (
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         // left part
         left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3 `star`
         // right part
         right_vprop slab_region md_bm_region md_region v)
  )
  (fun r ->
    (if not (A.is_null r) then A.varray r else emp) `star`
    vrefinedep
      (vptr md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         // left part
         left_vprop size_class slab_region md_bm_region v md_region r1 r2 r3 `star`
         // right part
         right_vprop slab_region md_bm_region md_region v)
  )
