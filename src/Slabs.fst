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


//assume val cons_imp_not_null (#opened:SM.inames) (#a:Type0) (p: a -> vprop) (ptr:SL.t a)
//  : SteelGhost unit opened
//  (SL.llist p ptr) (fun _ -> SL.llist p ptr)
//  (requires fun h -> True)
//  (ensures fun h0 _ h1 ->
//    SL.v_llist p ptr h0 == SL.v_llist p ptr h1 /\
//    Cons? (SL.v_llist p ptr h0) <==> ptr =!= SL.null_t)

//let impl_lemma (p1 p2: bool) (q1 q2: prop)
//  : Lemma
//  (requires
//    (p1 \/ p2) /\
//    (p1 ==> q1) /\
//    (p2 ==> q2)
//  )
//  (ensures
//    q1 \/ q2
//  )
//  = ()

#push-options "--compat_pre_typed_indexed_effects"
assume val alloc_metadata
  (size_class: sc)
  : Steel (slab_metadata & (arr:array U8.t{A.length arr = U32.v page_size}))
  emp
  (fun r ->
    slab_vprop size_class (snd r) (fst r))
    //`vrefine`
    //(fun (|s,_|) -> is_empty size_class s))
  (requires fun h0 -> True)
  (ensures fun h0 r h1->
    let blob1
      : t_of (slab_vprop size_class (snd r) (fst r))
      = h1 (slab_vprop size_class (snd r) (fst r)) in
    let v1 : Seq.lseq U64.t 4 = dfst blob1 in
    is_empty size_class v1 /\
    has_free_slot size_class v1)
#pop-options

#push-options "--z3rlimit 50"
#push-options "--compat_pre_typed_indexed_effects"
inline_for_extraction noextract
let allocate_slab_aux_3
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  (partial_slabs empty_slabs: SL.t blob)
  : Steel (SL.t blob)
  (vptr empty_slabs_ptr `star`
  SL.llist (p_empty sc) empty_slabs `star`
  vptr partial_slabs_ptr `star`
  SL.llist (p_partial sc) partial_slabs)
  (fun r ->
  vptr empty_slabs_ptr `star`
  SL.llist (p_empty sc) r `star`
  vptr partial_slabs_ptr `star`
  SL.llist (p_partial sc) partial_slabs)
  (requires fun h0 -> True)
  (ensures fun _ r h1 ->
    sel empty_slabs_ptr h1 == r)
  =
  let r = alloc_metadata sc in
  intro_vrefine
    (slab_vprop sc (snd r) (fst r))
    (fun (|s,_|) -> is_empty sc s);
  change_slprop_rel
    (slab_vprop sc (snd r) (fst r)
    `vrefine`
    (fun (|s,_|) -> is_empty sc s))
    ((p_empty sc) r)
    (fun x y -> x == y)
    (fun _ -> admit ());
  let n_empty = SL.mk_cell empty_slabs r in
  //// will yield to reentrance thus segfault
  let n_empty_slabs = malloc n_empty in
  SL.pack_list (p_empty sc)
    n_empty_slabs
    empty_slabs
    r;
  write empty_slabs_ptr n_empty_slabs;
  return n_empty_slabs
#pop-options
#pop-options



#push-options "--z3rlimit 50"
let allocate_slab
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t blob))
  : Steel (array U8.t)
  (SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr)
  (fun r ->
  A.varray r `star`
  SL.ind_llist (p_partial sc) partial_slabs_ptr `star`
  SL.ind_llist (p_empty sc) empty_slabs_ptr)
  (requires fun h0 ->
    //not (SL.is_null_t (sel empty_slabs_ptr h0)) \/
    //not (SL.is_null_t (sel partial_slabs_ptr h0)) \/
    Cons? (SL.v_ind_llist (p_partial sc) partial_slabs_ptr h0) \/
    Cons? (SL.v_ind_llist (p_empty sc) empty_slabs_ptr h0) \/
    // third case
    True
  )
  (ensures fun _ _ _ -> True)
  =
  //let h0 = get () in
  let partial_slabs
    = SL.unpack_ind (p_partial sc) partial_slabs_ptr in
  let empty_slabs
    = SL.unpack_ind (p_empty sc) empty_slabs_ptr in
  //let h1 = get () in
  //assert (SL.v_ind_llist (p_partial sc) partial_slabs_ptr h0
  //  == SL.v_llist (p_partial sc) partial_slabs h1);
  //assert (SL.v_ind_llist (p_empty sc) empty_slabs_ptr h0
  //  == SL.v_llist (p_empty sc) empty_slabs h1);
  //assert (
  //  Cons? (SL.v_llist (p_partial sc) partial_slabs h1) \/
  //  Cons? (SL.v_llist (p_empty sc) empty_slabs h1));
  //cons_imp_not_null (p_empty sc) empty_slabs;
  //cons_imp_not_null (p_partial sc) partial_slabs;
  //impl_lemma
  //  (Cons? (SL.v_llist (p_partial sc) partial_slabs h1))
  //  (Cons? (SL.v_llist (p_empty sc) empty_slabs h1))
  //  (~ (SL.is_null_t partial_slabs) /\ True)
  //  (~ (SL.is_null_t empty_slabs) /\ True);
  assume (
    not (SL.is_null_t partial_slabs) \/
    not (SL.is_null_t empty_slabs));
  if (not (SL.is_null_t partial_slabs)) then (
    let r = allocate_slab_aux_2 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  ) else if (not (SL.is_null_t empty_slabs)) then (
  //) else (
    let r = allocate_slab_aux_1 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  ) else (
    // h_malloc alloc_metadata equivalent
    let n_empty_slabs = allocate_slab_aux_3 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    let r = allocate_slab_aux_1 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs n_empty_slabs in
    return r
  )
#pop-options
