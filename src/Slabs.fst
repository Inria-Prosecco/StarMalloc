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
open FStar.Mul

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
  rewrite_slprop
    (A.varray (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (slab_array slab_region md_count))
    (fun _ -> ());
  let x1 = A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size) in
  let x2 = A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size)) in
  A.ptr_base_offset_inj (A.ptr_of x1) (A.ptr_of x2);
  assert (A.length x1 = A.length x2);
  assert (x1 == x2);
  rewrite_slprop
    (A.varray (A.split_r (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))))
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
  sladmit ()

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
  sladmit ()

let intro_slab_vprop
  (#opened: _)
  (size_class: sc)
  (b: blob)
  : SteelGhostT unit opened
  (A.varray (snd b) `star` A.varray (fst b))
  (fun _ -> slab_vprop size_class (snd b) (fst b))
  =
  sladmit ()

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
    A.varray (snd r) `star`
    A.varray (fst r) `star`
    //TODO: this varray will be somehow casted into the ref that corresponds to the SL.t type
    A.varray (md_array md_region md_count) `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
  )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
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
  return b
#pop-options

assume val singleton_array_to_ref
  (#a: Type0)
  (arr: array a)
  : Steel (ref a)
  (A.varray arr)
  (fun r -> vptr r)
  (requires fun _ -> A.length arr = 1)
  (ensures fun h0 r h1 ->
    Seq.length (A.asel arr h0) = 1 /\
    Seq.index (A.asel arr h0) 0 == sel r h1
  )

assume val intro_singleton_llist_no_alloc
  (#a: Type)
  (p: a -> vprop)
  (r: SL.t a)
  (v: a)
  : Steel (SL.t a)
  (vptr r `star` p v)
  (fun r' -> SL.llist p r')
  (requires fun h0 -> True)
  (ensures fun h0 r' h1 ->
    SL.v_llist p r' h1 == [SL.get_data (sel r h0)]
  )

#push-options "--z3rlimit 30"
let alloc_metadata_aux2
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  : Steel (SL.t blob)
  (
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz md_count))
  )
  //TODO: add a refinement over a md_count ref, discussion with Aymeric
  ////`star` vptr md_count)
  (fun r ->
    SL.llist (p_empty size_class) r `star`
    A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add md_count 1ul)))
  )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    L.length (SL.v_llist (p_empty size_class) r h1) = 1
  )
  =
  let b : blob = alloc_metadata_aux md_count size_class slab_region md_bm_region md_region in
  //let h = get () in
  //assume (is_empty size_class (A.asel (fst b) h));
  intro_slab_vprop size_class b;
  change_slprop_rel
    (slab_vprop size_class (snd b) (fst b))
    (p_empty size_class b)
    (fun x y -> x == y)
    (fun _ -> admit ());
  //p_empty_pack size_class b b;
  let r = singleton_array_to_ref (md_array md_region md_count) in
  let b_cell = SL.mk_cell null b in
  write r b_cell;
  let r = intro_singleton_llist_no_alloc (p_empty size_class) r b in
  return r
#pop-options

#push-options "--z3rlimit 50"
let alloc_metadata
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref (x:U32.t{U32.v x <= U32.v metadata_max}))
  //(md_count: ref U32.t)
  : SteelT unit
  //: Steel (SL.t blob)
  (
    vptr md_count `vdep` (fun (md_count_v:U32.t{U32.v md_count_v <= U32.v metadata_max}) ->
    //vptr md_count `vdep` (fun (md_count_v: U32.t{U32.v md_count_v < U32.v metadata_max}) ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz md_count_v))
    )
  )
  //TODO: add a refinement over a md_count ref, discussion with Aymeric
  ////`star` vptr md_count)
  (fun r ->
    //SL.llist (p_empty size_class) r `star`
    //emp
    //vptr md_count `vdep` (fun md_count_v ->
    vptr md_count `vdep` (fun (md_count_v:U32.t{U32.v md_count_v <= U32.v metadata_max}) ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz md_count_v))
    )
  )
  //(requires fun h0 ->
  //  let md_count_v
  //    : U32.t
  //    = dfst (h0
  //    (vptr md_count `vdep`
  //    (fun (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max}) ->
  //      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
  //      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
  //      A.varray (A.split_r md_region (u32_to_sz md_count_v))
  //    )))
  //  in
  //  U32.v md_count_v < U32.v metadata_max
  //)
  //(ensures fun h0 r h1 ->
  //  let md_count_v
  //    : U32.t
  //    = dfst (h1
  //    (vptr md_count `vdep`
  //    (fun (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max}) ->
  //      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
  //      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
  //      A.varray (A.split_r md_region (u32_to_sz md_count_v))
  //    )))
  //  in
  //  U32.v md_count_v <= U32.v metadata_max)


  //  let md_count_v0
  //    : U32.t
  //    = dfst (h0
  //    (vptr md_count `vdep`
  //    (fun md_count_v ->
  //      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
  //      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
  //      A.varray (A.split_r md_region (u32_to_sz md_count_v))
  //    ))) in
  //  let md_count_v1
  //    : U32.t
  //    = dfst (h1
  //    (vptr md_count `vdep`
  //    (fun md_count_v ->
  //      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
  //      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
  //      A.varray (A.split_r md_region (u32_to_sz md_count_v))
  //    ))) in
  //  md_count_v0 = md_count_v1



  ////  //sel md_count h1 = sel md_count h0
  ////  //L.length (SL.v_llist (p_empty size_class) r h1) = 1
  //)
  =
  let md_count_v = elim_vdep
    (vptr md_count)
    //(fun md_count_v ->
    (fun (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max}) ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz md_count_v))) in

  let h0 = get () in
  assume (U32.v (sel md_count h0) < U32.v metadata_max);
  let md_count_v2 = read md_count in
  assert (U32.v md_count_v2 = U32.v (sel md_count h0));
  assert (U32.v md_count_v2 < U32.v metadata_max);
  //assume (U32.v md_count_v2 < U32.v metadata_max);
  //sladmit ();
  //let r : SL.t blob = alloc_metadata_aux2 md_count_v size_class slab_region md_bm_region md_region in
  write md_count (U32.add md_count_v2 1ul);
  let h = get () in
  assume (U32.v (sel md_count h) <= U32.v metadata_max);
  let md_count_v2 : v:U32.t{U32.v v <= U32.v metadata_max} = read md_count in
  intro_vdep
    (vptr md_count)
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v2 page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v2 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz md_count_v2)))
    //(A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add md_count_v2 1ul) page_size))) `star`
    //  A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add md_count_v2 1ul) 4ul))) `star`
    //  A.varray (A.split_r md_region (u32_to_sz (U32.add md_count_v2 1ul))))
    //(fun md_count_v ->
    (fun (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max}) ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul md_count_v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul md_count_v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz md_count_v)));
  //return r
  return ()
#pop-options





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
  let md_count_v = read md_count in
  let r = alloc_metadata md_count_v sc slab_region md_bm_region md_region in
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
