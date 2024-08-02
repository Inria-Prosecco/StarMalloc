module Impl.BST.M

open Steel.Effect.Atomic
open Steel.Effect

module U = FStar.UInt64
module I = FStar.Int64

open Impl.Core
open Impl.Common
open Impl.Trees.Types
open Impl.Trees.M

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@BST
#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rec member (ptr: t) (v: data)
  : Steel bool (linked_tree pred p ptr) (fun _ -> linked_tree pred p ptr)
  (requires fun h0 ->
    Spec.is_bst (convert cmp) (v_linked_tree pred p ptr h0))
  (ensures fun h0 b h1 ->
    v_linked_tree pred p ptr h0 == v_linked_tree pred p ptr h1 /\
    Spec.is_bst (convert cmp) (v_linked_tree pred p ptr h0) /\
    (Spec.mem (convert cmp) (v_linked_tree pred p ptr h0) v <==> b) /\
    (Spec.memopt (convert cmp) (v_linked_tree pred p ptr h0) v <==> b))
  =
  let h = get () in
  Spec.equivmem (convert cmp) (v_linked_tree pred p ptr h) v;
  if is_null_t ptr then (
    (**) null_is_leaf pred p ptr;
    return false
  ) else (
    (**) let node = unpack_tree pred p ptr in
    let data = get_data node in
    let delta = cmp v data in
    if I.eq delta szero then (
      (**) pack_tree pred p ptr (get_left node) (get_right node)
        (get_size node) (get_height node) (get_data node);
      return true
    ) else if I.lt delta szero then (
      let b = member (get_left node) v in
      (**) pack_tree pred p ptr (get_left node) (get_right node)
        (get_size node) (get_height node) (get_data node);
      return b
    ) else (
      let b = member (get_right node) v in
      (**) pack_tree pred p ptr (get_left node) (get_right node)
        (get_size node) (get_height node) (get_data node);
      return b
    )
  )
#pop-options
