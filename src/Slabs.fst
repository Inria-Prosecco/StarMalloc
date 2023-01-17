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

module SL = Selectors.LList3

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
  fun (b: blob) ->
    slab_vprop size_class (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_empty size_class s == true)

let p_partial (size_class: sc)
  =
  fun (b: blob) ->
    slab_vprop size_class (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_partial size_class s == true)

let p_full (size_class: sc)
  =
  fun (b: blob) ->
    slab_vprop size_class (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_full size_class s == true)

#push-options "--compat_pre_typed_indexed_effects"
#push-options "--z3rlimit 30"
let p_empty_unpack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
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
  =
  change_slprop_rel
    ((p_empty sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `vrefine`
    (fun (|s,_|) -> is_empty sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun (|s,_|) -> is_empty sc s == true)

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
    let v1 : Seq.lseq U64.t 4 = dfst blob1 in
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
    `vrefine`
    (fun (|s,_|) -> is_partial sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun (|s,_|) -> is_partial sc s == true)

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
    let v1 : Seq.lseq U64.t 4 = dfst blob1 in
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
    `vrefine`
    (fun (|s,_|) -> is_full sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun (|s,_|) -> is_full sc s == true)

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
  =
  intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun (|s,_|) -> is_full sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `vrefine`
    (fun (|s,_|) -> is_full sc s == true))
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
  =
  intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun (|s,_|) -> is_partial sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `vrefine`
    (fun (|s,_|) -> is_partial sc s == true))
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
  =
  intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun (|s,_|) -> is_empty sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `vrefine`
    (fun (|s,_|) -> is_empty sc s == true))
    ((p_empty sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

#pop-options
#pop-options

module SAR = Steel.ArrayRef

#push-options "--compat_pre_typed_indexed_effects"
#push-options "--z3rlimit 30"
let allocate_slab_aux_1_partial
  (size_class: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  (partial_slabs empty_slabs: SL.t blob)
  (cell_ptr: SL.t blob)
  (cell_content: SL.cell blob)
  (b: blob)
  : Steel unit
  (
    slab_vprop size_class (snd b) (fst b) `star`
    (SAR.vptr cell_ptr `star`
    vptr empty_slabs_ptr `star`
    SL.llist (p_empty size_class) (SL.get_next cell_content) `star`
    vptr partial_slabs_ptr `star`
    SL.llist (p_partial size_class) partial_slabs)
  )
  (fun r ->
    SL.ind_llist (p_empty size_class) empty_slabs_ptr `star`
    SL.ind_llist (p_partial size_class) partial_slabs_ptr
  )
  (requires fun h0 ->
    let slab_vprop_data
      : t_of (slab_vprop size_class (snd b) (fst b))
      = h0 (slab_vprop size_class (snd b) (fst b)) in
    let md_seq : Seq.lseq U64.t 4 = dfst slab_vprop_data in
    sel partial_slabs_ptr h0 == partial_slabs /\
    SAR.sel cell_ptr h0 == cell_content /\
    is_partial size_class md_seq /\
    SL.get_data cell_content == b)
  (ensures fun h0 _ h1 ->
    True
  )
  =
  p_partial_pack size_class b (SL.get_data cell_content);
  let n_partial = SL.mk_cell partial_slabs (SL.get_data cell_content) in
  SAR.write cell_ptr n_partial;
  SL.pack_list (p_partial size_class)
    cell_ptr
    partial_slabs
    (SL.get_data cell_content);
  write partial_slabs_ptr cell_ptr;
  SL.pack_ind (p_partial size_class) partial_slabs_ptr cell_ptr;
  write empty_slabs_ptr (SL.get_next cell_content);
  SL.pack_ind (p_empty size_class)
    empty_slabs_ptr
    (SL.get_next cell_content)

let allocate_slab_aux_1_full
  (size_class: sc)
  (full_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  (full_slabs empty_slabs: SL.t blob)
  (cell_ptr: SL.t blob)
  (cell_content: SL.cell blob)
  (b: blob)
  : Steel unit
  (
    slab_vprop size_class (snd b) (fst b) `star`
    (SAR.vptr cell_ptr `star`
    vptr empty_slabs_ptr `star`
    SL.llist (p_empty size_class) (SL.get_next cell_content) `star`
    vptr full_slabs_ptr `star`
    SL.llist (p_full size_class) full_slabs)
  )
  (fun r ->
    SL.ind_llist (p_empty size_class) empty_slabs_ptr `star`
    SL.ind_llist (p_full size_class) full_slabs_ptr
  )
  (requires fun h0 ->
    let slab_vprop_data
      : t_of (slab_vprop size_class (snd b) (fst b))
      = h0 (slab_vprop size_class (snd b) (fst b)) in
    let md_seq : Seq.lseq U64.t 4 = dfst slab_vprop_data in
    sel full_slabs_ptr h0 == full_slabs /\
    SAR.sel cell_ptr h0 == cell_content /\
    is_full size_class md_seq /\
    SL.get_data cell_content == b)
  (ensures fun h0 _ h1 ->
    True
  )
  =
  p_full_pack size_class b (SL.get_data cell_content);
  let n_full = SL.mk_cell full_slabs (SL.get_data cell_content) in
  SAR.write cell_ptr n_full;
  SL.pack_list (p_full size_class)
    cell_ptr
    full_slabs
    (SL.get_data cell_content);
  write full_slabs_ptr cell_ptr;
  SL.pack_ind (p_full size_class) full_slabs_ptr cell_ptr;
  write empty_slabs_ptr (SL.get_next cell_content);
  SL.pack_ind (p_empty size_class)
    empty_slabs_ptr
    (SL.get_next cell_content)

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
    let v0 : Seq.lseq U64.t 4 = dfst blob0 in
    blob0 == blob1 /\
    r == is_full size_class v0
  )
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  let md_as_seq = elim_vdep
    (A.varray md)
    (fun (x: Seq.lseq U64.t 4) ->
      slab_vprop_aux size_class arr x)
  in
  let md_as_seq2 = G.hide ((G.reveal md_as_seq) <: Seq.lseq U64.t 4) in
  change_slprop_rel
    (slab_vprop_aux size_class arr (G.reveal md_as_seq))
    (slab_vprop_aux size_class arr (G.reveal md_as_seq2))
    (fun x y -> x == y)
    (fun _ -> ());
  let r = is_full_s size_class md in
  intro_vdep
    (A.varray md)
    (slab_vprop_aux size_class arr (G.reveal md_as_seq2))
    (fun (x: Seq.lseq U64.t 4) ->
      slab_vprop_aux size_class arr x);
  return r
#pop-options
#pop-options
#pop-options

#push-options "--z3rlimit 75"
inline_for_extraction noextract
let allocate_slab_aux_1
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr full_slabs_ptr: ref (SL.t blob))
  (partial_slabs empty_slabs full_slabs: SL.t blob)
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
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  (partial_slabs empty_slabs: SL.t blob)
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
  let v0 : G.erased (Seq.lseq U64.t 4) = dfst blob0 in
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
  : SteelGhostT unit opened
  (A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))))
  (fun _ ->
    A.varray (slab_array slab_region md_count) `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size)))
  )
  =
  A.ghost_split
    (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size)))
    (u32_to_sz page_size);
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
  : SteelGhostT unit opened
  (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))))
  (fun _ ->
    A.varray (md_bm_array md_bm_region md_count) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul)))
  )
  =
  A.ghost_split
    (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul)))
    (u32_to_sz 4ul);
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
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array (SL.cell blob))
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
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
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

#push-options "--z3rlimit 30"
let alloc_metadata_aux
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  //: Steel (SL.t blob)
  : Steel blob
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
    slab_vprop_aux size_class (snd r) (Seq.create 4 0UL) `star`
    A.varray (fst r) `star`
    //TODO: this varray will be somehow casted into the ref that corresponds to the SL.t type
    A.varray (md_array md_region md_count) `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
  )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    A.asel (fst r) h1 == Seq.create 4 0UL
  )
  =
  slab_region_mon_split slab_region md_count;
  md_bm_region_mon_split md_bm_region md_count;
  md_region_mon_split md_region md_count;
  let md_bm = md_bm_array md_bm_region md_count in
  let slab = slab_array slab_region md_count in
  let b : blob = (md_bm, slab) in
  change_slprop_rel
    (A.varray (slab_array slab_region md_count) `star`
    A.varray (md_bm_array md_bm_region md_count))
    (A.varray (snd b) `star` A.varray (fst b))
    (fun x y -> x == y)
    (fun _ -> ());
  // prove never-used slab bitmap metadata is empty
  admit ();
  Helpers.slab_to_slots size_class (snd b);
  return b
#pop-options

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
let alloc_metadata_aux2
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  : Steel (SL.t blob & (G.erased U32.t))
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
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) (fst r) h1) = 1 /\
    G.reveal (snd r) = U32.add md_count 1ul /\
    U32.v (G.reveal (snd r)) <= U32.v metadata_max
  )
  =
  let b : blob = alloc_metadata_aux md_count size_class slab_region md_bm_region md_region in
  let v0 : G.erased (Seq.lseq U64.t 4) = gget (A.varray (fst b)) in
  assert (G.reveal v0 == Seq.create 4 0UL);
  intro_vdep
    (A.varray (fst b))
    (slab_vprop_aux size_class (snd b) (Seq.create 4 0UL))
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (snd b) md_as_seq);
  let blob1
      : G.erased (t_of (slab_vprop size_class (snd b) (fst b)))
      = gget (slab_vprop size_class (snd b) (fst b)) in
  let v1 : G.erased (Seq.lseq U64.t 4) = dfst blob1 in
  // fix it...
  assume (G.reveal v1 == G.reveal v0);
  zeroes_impl_empty size_class (G.reveal v1);
  p_empty_pack size_class b b;
  SAR.intro_vptr (md_array md_region md_count);
  SL.intro_singleton_llist_no_alloc (p_empty size_class) (md_array md_region md_count) b;
  return (md_array md_region md_count, G.hide (U32.add md_count 1ul))
#pop-options

let alloc_metadata_sl1
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
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
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
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
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
  : Steel (SL.t blob & G.erased U32.t)
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
    sel md_count h0 = G.reveal md_count_v
  )
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) (fst r) h1) = 1 /\
    sel md_count h0 = G.reveal md_count_v /\
    sel md_count h1 = U32.add (sel md_count h0) 1ul /\
    sel md_count h1 = G.reveal (snd r)
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

let unpack_list_singleton (#a: Type0)
  (p: a -> vprop)
  (ptr: SL.t a)
  : Steel (SL.cell a)
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
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (md_count_v: G.erased (v:U32.t{U32.v v < U32.v metadata_max}))
  : Steel (SL.t blob)
  (
    vptr md_count `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal md_count_v) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal md_count_v) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal md_count_v)))
  )
  (fun r ->
    vptr md_count `star`
    SL.llist (p_empty size_class) r `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal md_count_v) 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal md_count_v) 1ul)))
  )
  (requires fun h0 ->
    sel md_count h0 = G.reveal md_count_v
  )
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) r h1) = 1 /\
    sel md_count h0 = G.reveal md_count_v /\
    sel md_count h1 = U32.add (sel md_count h0) 1ul /\
    U32.v (U32.add (sel md_count h0) 1ul) <= U32.v metadata_max
    //sel md_count h1 = G.reveal (snd r)
  )
  =
  let r = alloc_metadata size_class slab_region md_bm_region md_region md_count md_count_v in
  return (fst r)
#pop-options

open SteelVRefineDep

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let alloc_metadata2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel (SL.t blob)
  //: Steel unit
  (
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (fun r ->
    SL.llist (p_empty size_class) r `star`
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (requires fun h0 ->
    let x = h0 (
      vrefinedep
        (vptr md_count)
        //TODO: hideous coercion
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
          A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
          A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
          A.varray (A.split_r md_region (u32_to_sz v)))
      ) in
    U32.v (dfst x) < U32.v metadata_max)


  (ensures fun h0 r h1 ->
    //TODO FIXME: fails with this postcondition
    FStar.List.Tot.length (SL.v_llist (p_empty size_class) r h1) = 1
    ///\ sel md_count h1 = U32.add (sel md_count h0) 1ul
  )
  =
  let x
    //: G.erased (x:U32.t{U32.v x < U32.v metadata_max == true})
    = elim_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz v)))
  in
 let x'
    : G.erased (x:U32.t{U32.v x < U32.v metadata_max})
    = G.hide (G.reveal x <: x:U32.t{U32.v x < U32.v metadata_max}) in
  //TODO: hideous coercion that leads to 2 change_slprop_rel
  change_equal_slprop
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal x))))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x') page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x') 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal x'))));
  let r = alloc_metadata' size_class slab_region md_bm_region md_region md_count x' in
  //TODO: hideous coercion that leads to 2 change_slprop_rel
  change_equal_slprop
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x') 1ul))))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x) 1ul))));
  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz v)))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x) 1ul))));
  return r
#pop-options

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
inline_for_extraction noextract
let allocate_slab_aux_3
  (size_class: sc)
  (empty_slabs_ptr: ref (SL.t blob))
  (empty_slabs: SL.t blob)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel (SL.t blob)
  (
    vptr empty_slabs_ptr `star`
    SL.llist (p_empty size_class) empty_slabs `star`
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (fun r ->
    vptr empty_slabs_ptr `star`
    SL.llist (p_empty size_class) r `star`
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (requires fun h0 ->
    let x = h0 (
      vrefinedep
        (vptr md_count)
        //TODO: hideous coercion
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
          A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
          A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
          A.varray (A.split_r md_region (u32_to_sz v)))
      ) in
    U32.v (dfst x) < U32.v metadata_max)
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
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel bool
  (
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))) in
    blob0 == blob1 /\
    r == (U32.v (dfst blob0) < U32.v metadata_max)
  )
  =
  let x0 = gget (vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))) in
  let x
    = elim_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz v)))
  in
  let r = read md_count in
  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz v)))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (G.reveal x))));
  let x1 = gget (vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))) in
  assert (dfst x0 == dfst x1);
  assert (dsnd x0 == dsnd x1);
  return (U32.lt r metadata_max)


#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let allocate_slab
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr full_slabs_ptr: ref (SL.t blob))
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel (array U8.t & G.erased bool)
  (
    SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
    SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
    SL.ind_llist (p_full sc) full_slabs_ptr `star`
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (fun r ->
    (if (G.reveal (snd r)) then A.varray (fst r) else emp) `star`
    SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
    SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
    SL.ind_llist (p_full sc) full_slabs_ptr `star`
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (requires fun h0 -> True)
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
