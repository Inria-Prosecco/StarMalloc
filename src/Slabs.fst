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

module SL = Selectors.LList

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

let allocate_slot_refined
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : Steel (array U8.t)
  (slab_vprop size_class arr md)
  (fun r -> A.varray r `star` slab_vprop size_class arr md)
  (requires fun h0 ->
    let blob0 : (t_of (slab_vprop size_class arr md))
      = h0 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq U64.t 4 = dfst blob0 in
    has_free_slot size_class v0)
  (ensures fun h0 _ h1 ->
    let blob1 : (t_of (slab_vprop size_class arr md))
      = h1 (slab_vprop size_class arr md) in
    let v1 : Seq.lseq U64.t 4 = dfst blob1 in
    is_partial size_class v1)
  =
  admit ();
  allocate_slot size_class md arr

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
    (fun (|s,_|) -> is_empty size_class s)

let p_partial (size_class: sc)
  =
  fun (b: blob) ->
    slab_vprop size_class (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_partial size_class s)

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
    (fun (|s,_|) -> is_empty sc s))
    (fun x y -> x == y)
    (fun _ -> ());
  elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun (|s,_|) -> is_empty sc s)

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
    (fun (|s,_|) -> is_partial sc s))
    (fun x y -> x == y)
    (fun _ -> ());
  elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun (|s,_|) -> is_partial sc s)

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
    (fun (|s,_|) -> is_partial sc s);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `vrefine`
    (fun (|s,_|) -> is_partial sc s))
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
    (fun (|s,_|) -> is_empty sc s);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `vrefine`
    (fun (|s,_|) -> is_empty sc s))
    ((p_empty sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

#pop-options
#pop-options

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let allocate_slab_aux_1
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
    not (SL.is_null_t empty_slabs))
  (ensures fun _ _ _ -> True)
  =
  let n_empty = SL.unpack_list (p_empty sc) empty_slabs in
  let b = SL.get_data n_empty in
  p_empty_unpack sc
    (SL.get_data n_empty)
    b;
  let r = allocate_slot_refined sc (fst b) (snd b) in
  p_partial_pack sc
    b
    (SL.get_data n_empty);
  let n_partial = SL.mk_cell partial_slabs (SL.get_data n_empty) in
  write empty_slabs n_partial;
  SL.pack_list (p_partial sc)
    empty_slabs
    partial_slabs
    (SL.get_data n_empty);
  write partial_slabs_ptr empty_slabs;
  SL.pack_ind (p_partial sc) partial_slabs_ptr empty_slabs;
  write empty_slabs_ptr (SL.get_next n_empty);
  SL.pack_ind (p_empty sc) empty_slabs_ptr (SL.get_next n_empty);
  return r

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
  let r = allocate_slot_refined sc (fst b) (snd b) in
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

//TODO:
//to be improved
//val alloc_metadata_v2
//  (size_class: sc)
//  : Steel (SL.t blob)
//  emp
//  (fun r ->
//    vptr r `vdep` (fun n -> p_empty size_class (SL.get_data n)))
//  (requires fun h0 -> True)
//  (ensures fun _ r h1 ->
//    not (SL.is_null_t r) /\
//    SL.is_null_t (SL.get_next (sel r h1)))

//#push-options "--z3rlimit 30"
//let slab_array
//  (slab_region: array U8.t)
//  (md_count: U32.t)
//  : Pure (array U8.t)
//  (requires
//    U32.v md_count < U32.v metadata_max /\
//    A.length slab_region = U32.v page_size * U32.v metadata_max)
//  (ensures fun r ->
//    A.length r = U32.v page_size /\
//    same_base_array r slab_region /\
//    True)
//  =
//  let ptr = A.ptr_of slab_region in
//  let shift = U32.mul md_count page_size in
//  //assert (U32.v shift <= U32.v page_size);
//  //assert_norm (U32.v shift <= FI.max_int U16.n);
//  //assert (U32.v shift <= FI.max_int U16.n);
//  let shift_size_t = STU.small_uint32_to_sizet shift in
//  assert (US.v shift_size_t < A.length arr);
//  let ptr_shifted = A.ptr_shift ptr shift_size_t in
//  (| ptr_shifted, G.hide (U32.v size_class) |)
//#pop-options

assume val alloc_metadata
  (size_class: sc)
  (slab_region: array U8.t)
  (md_bm_region: array U64.t)
  (md_region: array (SL.cell blob))
  (md_count: ref U32.t)
  : Steel (SL.t blob)
  (A.varray slab_region `star`
  A.varray md_bm_region `star`
  A.varray md_region `star`
  vptr md_count)
  (fun r ->
    SL.llist (p_empty size_class) r `star`
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region `star`
    vptr md_count)
  (requires fun h0 ->
    U32.v (sel md_count h0) < U32.v metadata_max)
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) r h1) = 1 /\
    U32.v (sel md_count h1) = U32.v (sel md_count h0) + 1)

let unpack_list_singleton (#a: Type0)
  (p: a -> vprop)
  (ptr: SL.t a)
  : Steel (SL.cell a)
  (SL.llist p ptr)
  (fun n -> vptr ptr `star` p (SL.get_data n))
  (requires fun h0 ->
    L.length (SL.v_llist p ptr h0) = 1)
  (ensures fun h0 n h1 ->
    SL.v_llist p ptr h0 ==
      (SL.get_data (sel ptr h1)) :: [] /\
    sel ptr h1 == n)
  =
  SL.cons_is_not_null p ptr;
  let n = SL.unpack_list p ptr in
  //TODO: FIXME (add AVL-like helper)
  drop (SL.llist p (SL.get_next n));
  return n

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let allocate_slab_aux_3
  (sc: sc)
  (empty_slabs_ptr: ref (SL.t blob))
  (empty_slabs: SL.t blob)
  (slab_region: array U8.t)
  (md_bm_region: array U64.t)
  (md_region: array (SL.cell blob))
  (md_count: ref U32.t)
  : Steel (SL.t blob)
  (vptr empty_slabs_ptr `star`
  SL.llist (p_empty sc) empty_slabs `star`
  A.varray slab_region `star`
  A.varray md_bm_region `star`
  A.varray md_region `star`
  vptr md_count)
  //`star`
  //vptr partial_slabs_ptr `star`
  //SL.llist (p_partial sc) partial_slabs)
  (fun r ->
  vptr empty_slabs_ptr `star`
  SL.llist (p_empty sc) r `star`
  A.varray slab_region `star`
  A.varray md_bm_region `star`
  A.varray md_region `star`
  vptr md_count)
  //`star`
  //vptr partial_slabs_ptr `star`
  //SL.llist (p_partial sc) partial_slabs)
  (requires fun h0 ->
    U32.v (sel md_count h0) < U32.v metadata_max)
  (ensures fun h0 r h1 ->
    sel empty_slabs_ptr h1 == r /\
    //sel partial_slabs_ptr h1 == sel partial_slabs_ptr h0 /\
    not (SL.is_null_t r))
  =
  let r = alloc_metadata sc slab_region md_bm_region md_region md_count in
  let n_empty = unpack_list_singleton (p_empty sc) r in
  let n_empty_2 = SL.mk_cell empty_slabs (SL.get_data n_empty) in
  write r n_empty_2;
  SL.pack_list (p_empty sc)
    r
    empty_slabs
    (SL.get_data n_empty);
  SL.cons_is_not_null (p_empty sc) r;
  write empty_slabs_ptr r;
  return r
#pop-options

#push-options "--z3rlimit 50"
let allocate_slab
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  (slab_region: array U8.t)
  (md_bm_region: array U64.t)
  (md_region: array (SL.cell blob))
  (md_count: ref U32.t)
  : Steel (array U8.t)
  (SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
  A.varray slab_region `star`
  A.varray md_bm_region `star`
  A.varray md_region `star`
  vptr md_count)
  (fun r ->
  A.varray r `star`
  SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr `star`
  A.varray slab_region `star`
  A.varray md_bm_region `star`
  A.varray md_region `star`
  vptr md_count)
  (requires fun h0 ->
    Cons? (SL.v_ind_llist (p_partial sc) partial_slabs_ptr h0) \/
    Cons? (SL.v_ind_llist (p_empty sc) empty_slabs_ptr h0) \/
    U32.v (sel md_count h0) < U32.v metadata_max)
  (ensures fun _ _ _ -> True)
  =
  let partial_slabs
    = SL.unpack_ind (p_partial sc) partial_slabs_ptr in
  let empty_slabs
    = SL.unpack_ind (p_empty sc) empty_slabs_ptr in
  //let h1 = get () in
  //assert (sel partial_slabs_ptr h1 == partial_slabs);
  //assert (sel empty_slabs_ptr h1 == empty_slabs);
  SL.cons_imp_not_null (p_partial sc) partial_slabs;
  SL.cons_imp_not_null (p_empty sc) empty_slabs;
  let h0 = get () in
  assert (
    not (SL.is_null_t partial_slabs) \/
    not (SL.is_null_t empty_slabs) \/
    U32.v (sel md_count h0) < U32.v metadata_max);
  if (not (SL.is_null_t partial_slabs)) then (
    let r = allocate_slab_aux_2 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  ) else if (not (SL.is_null_t empty_slabs)) then (
    let r = allocate_slab_aux_1 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  ) else (
    // h_malloc alloc_metadata equivalent
    let n_empty_slabs = allocate_slab_aux_3 sc
      empty_slabs_ptr empty_slabs
      slab_region md_bm_region md_region md_count in
    let r = allocate_slab_aux_1 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs n_empty_slabs in
    return r
  )
#pop-options
