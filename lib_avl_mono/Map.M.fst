module Map.M

open Steel.Effect.Atomic
open Steel.Effect

module US = FStar.SizeT
module U64 = FStar.UInt64
module I64 = FStar.Int64

open Impl.Core
open Impl.Common
open Impl.Trees.Types

#set-options "--ide_id_info_off"
//let unpack_tree = Impl.Trees.M.unpack_tree

let spec_convert (#a: Type) (compare: cmp a)
  : GTot (Spec.cmp a)
  //= Impl.Common.convert (convert compare)
  = Impl.Common.convert compare

let insert
  (r: bool) (cmp: cmp data) (ptr: t)
  (new_data: data)
  : Steel t
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.size_of_tree (v_linked_tree ptr h0) < c /\
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0) /\
    v_linked_tree ptr' h1
    == Spec.insert_avl r
      (spec_convert cmp)
      (v_linked_tree ptr h0) new_data)
  =
  let h0 = get () in
  Spec.height_lte_size (v_linked_tree ptr h0);
  Impl.Mono.insert_avl r cmp ptr new_data

let delete
  (cmp: cmp data) (ptr: t)
  (data_to_rm: data)
  : Steel t
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0) /\
    v_linked_tree ptr' h1
    == Spec.delete_avl (spec_convert cmp)
      (v_linked_tree ptr h0)
      data_to_rm)
  =
  Impl.Mono.delete_avl cmp ptr data_to_rm

let cardinal
  (ptr: t)
  : Steel (U64.t)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun h0 s h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    U64.v s == Spec.sot_wds (v_linked_tree ptr h0) /\
    U64.v s == Spec.size_of_tree (v_linked_tree ptr h0))
  =
  Impl.Mono.sot_wds ptr

let mem
  (cmp: cmp data) (ptr: t)
  (v: data)
  : Steel bool
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_bst (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 b h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1)
  =
  Impl.Mono.member cmp ptr v

let rec find
  (cmp: cmp data) (ptr: t)
  (v: data)
  : Steel (option US.t)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 r h1 ->
    v_linked_tree ptr h1 == v_linked_tree ptr h0)
    //Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
    //r == Spec.Map.find_avl #a #b (spec_convert cmp) (v_linked_tree ptr h0) v)
  =
  if is_null_t ptr then (
    null_is_leaf ptr;
    return None
  ) else (
    let node = unpack_tree ptr in
    let delta = cmp v (get_data node) in
  if I64.eq delta szero then (
    pack_tree ptr
      (get_left node) (get_right node)
      (get_size node) (get_height node);
    let r = (get_data node).size in
    return (Some r)
  ) else (
    if I64.lt delta szero then (
      let r = find cmp (get_left node) v in
      pack_tree ptr
        (get_left node) (get_right node)
        (get_size node) (get_height node);
      return r
    ) else (
      let r = find cmp (get_right node) v in
      pack_tree ptr
        (get_left node) (get_right node)
        (get_size node) (get_height node);
      return r
    )
  ))

let find2
  (cmp: cmp data) (ptr: t)
  (v: data)
  : Steel (U64.t)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 r h1 ->
    v_linked_tree ptr h1 == v_linked_tree ptr h0)
  =
  let a = find cmp ptr v in
  if Some? a
  then return 1UL
  else return 0UL


//let mem (#a #b: Type) (cmp: cmp a) (ptr: t (a & b))
//  (v: a)
//  (b_inhabitant: b)
//  : Steel bool
//  (linked_tree ptr)
//  (fun _ -> linked_tree ptr)
//  (requires fun h0 ->
//    Spec.is_bst (spec_convert cmp) (v_linked_tree ptr h0))
//  (ensures fun h0 b h1 ->
//    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
//    Spec.is_bst (spec_convert cmp) (v_linked_tree ptr h0) /\
//    (Spec.mem (spec_convert cmp) (v_linked_tree ptr h0) (v, b_inhabitant) <==> b) /\
//    (Spec.memopt (spec_convert cmp) (v_linked_tree ptr h0) (v, b_inhabitant) <==> b))
//  =
//  Impl.member (convert cmp) ptr (v, b_inhabitant)
