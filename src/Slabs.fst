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
//assume val get_slab_region (_:unit)
//  : slab_region
//
//// C binding, no top-level Steel initialization
//assume val get_slab_md_region (_:unit)
//  : slab_md_region

////TODO
//noextract
//let slab_md_bitmap_length = nb_slots (U32.uint_to_t min_sc)

#push-options "--print_implicits --print_universes"

#set-options "--ide_id_info_off"

assume val allocate_slot_refined
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

//#push-options "--compat_pre_typed_indexed_effects"
//let allocate_slab_bug
//  (sc: sc)
//  (b: blob)
//  : Steel unit
//  ((slab_vprop sc (snd b) (fst b)
//    `vrefine`
//    (fun (|s,_|) -> is_empty sc s)))
//  (fun _ -> (slab_vprop sc (snd b) (fst b)
//    `vrefine`
//    (fun (|s,_|) -> is_empty sc s)))
//  (requires fun h0 -> True)
//  (ensures fun _ _ _ -> True)
//  =
//  elim_vrefine
//    (slab_vprop sc (snd b) (fst b))
//    (fun (|s,_|) -> is_empty sc s);
//  intro_vrefine
//    (slab_vprop sc (snd b) (fst b))
//    (fun (|s,_|) -> is_empty sc s);
//  return ()
//#pop-options

// Given a size class, return a free slot and update metadata
// TODO: refine spec
// TODO: remove assume with pure predicates inside p
//   this will yield two different versions of p

#push-options "--z3rlimit 30"
#push-options "--compat_pre_typed_indexed_effects"
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
  change_slprop_rel
    ((p_empty sc) (SL.get_data n_empty))
    (slab_vprop sc (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_empty sc s))
    (fun x y -> x == y)
    (fun _ -> admit ());
  elim_vrefine
    (slab_vprop sc (snd b) (fst b))
    (fun (|s,_|) -> is_empty sc s);
  let r = allocate_slot_refined sc (fst b) (snd b) in
  intro_vrefine
    (slab_vprop sc (snd b) (fst b))
    (fun (|s,_|) -> is_partial sc s);
  change_slprop_rel
    (slab_vprop sc (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_partial sc s))
    ((p_partial sc) (SL.get_data n_empty))
    (fun x y -> x == y)
    (fun _ -> admit ());
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
#pop-options

#push-options "--compat_pre_typed_indexed_effects"
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
  change_slprop_rel
    ((p_partial sc) (SL.get_data n_partial))
    (slab_vprop sc (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_partial sc s))
    (fun x y -> x == y)
    (fun _ -> admit ());
  elim_vrefine
    (slab_vprop sc (snd b) (fst b))
    (fun (|s,_|) -> is_partial sc s);
  let r = allocate_slot_refined sc (fst b) (snd b) in
  intro_vrefine
    (slab_vprop sc (snd b) (fst b))
    (fun (|s,_|) -> is_partial sc s);
  change_slprop_rel
    (slab_vprop sc (snd b) (fst b)
    `vrefine`
    (fun (|s,_|) -> is_partial sc s))
    ((p_partial sc) (SL.get_data n_partial))
    (fun x y -> x == y)
    (fun _ -> admit ());
  SL.pack_list (p_partial sc)
    partial_slabs
    (SL.get_next n_partial)
    (SL.get_data n_partial);
  SL.pack_ind (p_partial sc) partial_slabs_ptr partial_slabs;
  SL.pack_ind (p_empty sc) empty_slabs_ptr empty_slabs;
  return r
#pop-options
#pop-options

let allocate_slab
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  (partial_slabs empty_slabs: SL.t blob)
  : Steel (array U8.t)
  (vptr partial_slabs_ptr `star`
  SL.llist (p_partial sc) partial_slabs `star`
  vptr empty_slabs_ptr `star`
  SL.llist (p_empty sc) empty_slabs)
  (fun r ->
  A.varray r `star`
  SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr)
  (requires fun h0 ->
    sel partial_slabs_ptr h0 == partial_slabs /\
    sel empty_slabs_ptr h0 == empty_slabs /\
    (not (SL.is_null_t partial_slabs) \/
    not (SL.is_null_t empty_slabs)))
  (ensures fun _ _ _ -> True)
  =
  if (SL.is_null_t partial_slabs) then (
    let r = allocate_slab_aux_1 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  ) else (
    let r = allocate_slab_aux_2 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  )

(*)
// Given a size, return a size_class
// TODO: improve max_sc bound
// (requires an improved Steel while loop)
let select_size_class (size: U32.t)
  : Steel sc
  emp (fun _ -> emp)
  (requires fun _ -> U32.v size <= max_sc)
  (ensures fun _ size_class _ -> U32.lte size size_class)
  =
  if U32.lte size 16ul then (
    return 16ul
  ) else if U32.lte size 32ul then (
    return 32ul
  ) else (
    return 64ul
  )

let select_size_class2 (size: U32.t)
  (sc16 sc32 sc64: ref size_class_struct)
  : Steel (ref size_class_struct & G.erased U32.t)
  (size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (fun _ -> size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (requires fun h0 ->
    (v_sc_full sc16 h0).scs_v.size == 16ul /\
    (v_sc_full sc32 h0).scs_v.size == 32ul /\
    (v_sc_full sc64 h0).scs_v.size == 64ul /\
    U32.v size <= max_sc)
  (ensures fun h0 r h1 ->
    U32.lte size (snd r))
  =

  if U32.lte size 16ul then (
    let sc_size = G.hide 16ul in
    return (sc16, sc_size)
  ) else if U32.lte size 32ul then (
    let sc_size = G.hide 32ul in
    return (sc32, sc_size)
  ) else (
    let sc_size = G.hide 64ul in
    return (sc64, sc_size)
  )

let size_classes : list sc = [16ul ; 32ul ; 64ul]

let scl_to_vprop (scl: list (ref size_class_struct))
  : vprop
  = starl (L.map (fun sc -> size_class_full sc) scl)

let f ()
  =
  assert (L.memP 16ul size_classes);
  assert_norm (L.memP 32ul size_classes);
  assert_norm (L.memP 64ul size_classes)


(*)
let rec select_size_class3
  (scl: list (ref size_class_struct))
  (size: U32.t)
  : Steel (ref size_class_struct)
  (scl_to_vprop scl)
  (fun r ->
    size_class_full r `star`
    scl_to_vprop (L.filter (fun r2 -> r2 =!= r) scl)
  )
  (requires fun h0 -> Cons? scl)
  (ensures fun h0 r h1 ->
    not (is_null r)
  )
  =
  let r = L.hd scl in




  admit ();
  return null

let a = 42
(*)

  (fun r ->
    size_class_full r `star`
    SL.ind_llist (fun sc -> size_class_full sc) size_classes)
  (requires fun h0 ->
    Cons? (SL.v_ind_llist (fun sc -> size_class_full sc) size_classes h0))
  (ensures fun h0 r h1 ->

  )



  (size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (fun _ -> size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (requires fun h0 ->
    (v_sc_full sc16 h0).scs_v.size == 16ul /\
    (v_sc_full sc32 h0).scs_v.size == 32ul /\
    (v_sc_full sc64 h0).scs_v.size == 64ul /\
    U32.v size <= max_sc)
  (ensures fun h0 r h1 ->
    U32.lte size (snd r))
  =

  if U32.lte size 16ul then (
    let sc_size = G.hide 16ul in
    return (sc16, sc_size)
  ) else if U32.lte size 32ul then (
    let sc_size = G.hide 32ul in
    return (sc32, sc_size)
  ) else (
    let sc_size = G.hide 64ul in
    return (sc64, sc_size)
  )



(*)
//noextract
//let size_classes : list nzn = [
//  //(* 0 *) 0;
//  (* 16 *) 16; 32; 48; 64; 80; 96; 112; 128;
//  (* 32 *) 160; 192; 224; 256;
//  (* 64 *) 320; 384; 448; 512;
//]
//
//
//noextract
//let size_class_slots : list nzn =
//  L.map nb_of_slots size_classes
//
//let f (_:unit) =
//  let v = L.nth size_class_slots 0 in
//  assert(Some?.v v == 256);
//  ()

let page_size = 4096ul

let nzn = x:U32.t{U32.v x > 0 /\ U32.v x <= U32.v page_size}
let slab = slab:array U8.t{A.length slab == U32.v page_size}

let nb_slots (x: nzn) : nzn = U32.div page_size x

let slab_metadata (size_class: nzn)
  = Seq.lseq bool (U32.v (nb_slots size_class))
