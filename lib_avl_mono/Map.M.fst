module Map.M

open Steel.Effect.Atomic
open Steel.Effect

open Constants

module US = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I64 = FStar.Int64

open Impl.Core
open Impl.Common
open Impl.Trees.Types

#set-options "--ide_id_info_off"
//let unpack_tree = Impl.Trees.M.unpack_tree

let spec_convert (#a: Type) (compare: Impl.Common.cmp a)
  : GTot (Spec.cmp a)
  //= Impl.Common.convert (convert compare)
  = Impl.Common.convert compare

//inline_for_extraction noextract
//let insert
//  (r: bool) (ptr: t)
//  (new_data: data)
//  : Steel t
//  (linked_tree ptr)
//  (fun ptr' -> linked_tree ptr')
//  (requires fun h0 ->
//    Spec.size_of_tree (v_linked_tree ptr h0) < c /\
//    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
//  (ensures fun h0 ptr' h1 ->
//    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0) /\
//    v_linked_tree ptr' h1
//    == Spec.insert_avl r
//      (spec_convert cmp)
//      (v_linked_tree ptr h0) new_data)
//  =
//  let h0 = get () in
//  Spec.height_lte_size (v_linked_tree ptr h0);
//  Impl.Mono.insert_avl trees_malloc2 trees_free2 r ptr new_data
//
//inline_for_extraction noextract
//let delete
//  (ptr: t)
//  (data_to_rm: data)
//  : Steel t
//  (linked_tree ptr)
//  (fun ptr' -> linked_tree ptr')
//  (requires fun h0 ->
//    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
//  (ensures fun h0 ptr' h1 ->
//    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0) /\
//    v_linked_tree ptr' h1
//    == Spec.delete_avl (spec_convert cmp)
//      (v_linked_tree ptr h0)
//      data_to_rm)
//  =
//  Impl.Mono.delete_avl trees_malloc2 trees_free2 ptr data_to_rm

inline_for_extraction noextract
let cardinal
  (ptr: t)
  : Steel (U64.t)
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun _ -> True)
  (ensures fun h0 s h1 ->
    v_linked_tree p ptr h0 == v_linked_tree p ptr h1 /\
    U64.v s == Spec.sot_wds (v_linked_tree p ptr h0) /\
    U64.v s == Spec.size_of_tree (v_linked_tree p ptr h0))
  =
  Impl.Mono.sot_wds ptr

inline_for_extraction noextract
let mem
  (ptr: t)
  (v: data)
  : Steel bool
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun h0 ->
    Spec.is_bst (spec_convert cmp) (v_linked_tree p ptr h0))
  (ensures fun h0 b h1 ->
    v_linked_tree p ptr h0 == v_linked_tree p ptr h1 /\
    Spec.is_bst (convert cmp) (v_linked_tree p ptr h0) /\
    (Spec.mem (convert cmp) (v_linked_tree p ptr h0) v <==> b) /\
    (Spec.memopt (convert cmp) (v_linked_tree p ptr h0) v <==> b)
  )
  =
  Impl.Mono.member ptr v

module A = Steel.Array

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

#restart-solver

open Config

let rec find
  (ptr: t)
  (v: data)
  : Steel (option US.t)
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree p ptr h0) /\
    Spec.forall_keys
      (v_linked_tree p ptr h0)
      (fun x -> US.v (snd x) <> 0)
  )
  (ensures fun h0 r h1 ->
    v_linked_tree p ptr h1 == v_linked_tree p ptr h0 /\
    //h1 (linked_tree p ptr)
    //==
    //h0 (linked_tree p ptr) /\
    Spec.is_avl (spec_convert cmp) (v_linked_tree p ptr h0) /\
    (Some? r == Spec.mem (spec_convert cmp) (v_linked_tree p ptr h0) v) /\
    (Some? r == Spec.memopt (spec_convert cmp) (v_linked_tree p ptr h0) v) /\
    (Some? r ==> (
      let size = Some?.v r in
      A.length (fst v) == US.v size /\
      US.v size > U32.v max_slab_size /\
      A.is_full_array (fst v) /\
      Spec.mem (spec_convert cmp) (v_linked_tree p ptr h0)
        (fst v, Some?.v r)
    ))
  )
  =
  let h = get () in
  Spec.equivmem (spec_convert cmp) (v_linked_tree p ptr h) v;
  if is_null_t ptr then (
    null_is_leaf p ptr;
    return None
  ) else (
    let h0 = get () in
    let node = unpack_tree p ptr in
    let h1 = get () in
    let delta = cmp v (get_data node) in
    if I64.eq delta szero then (
      pack_tree p ptr
        (get_left node) (get_right node)
        (get_size node) (get_height node);
      let d : data = get_data node in
      let r = snd (get_data node) in
      assert (r <> 0sz);
      return (Some r)
    ) else (
      if I64.lt delta szero then (
        let r = find (get_left node) v in
        pack_tree p ptr
          (get_left node) (get_right node)
          (get_size node) (get_height node);
        return r
      ) else (
        let r = find (get_right node) v in
        pack_tree p ptr
          (get_left node) (get_right node)
          (get_size node) (get_height node);
        return r
      )
    )
  )
