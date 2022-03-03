module Impl.BST

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

//module Spec = Trees
module U = FStar.UInt64
module I = FStar.Int64

open Impl.Core
open Impl.Common
open Impl.Trees

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@BST
#push-options "--fuel 1 --ifuel 1"
let rec member (#a: Type) (cmp:cmp a) (ptr: t a) (v: a)
  : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 b h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0) /\
    (Spec.mem (convert cmp) (v_linked_tree ptr h0) v <==> b) /\
    (Spec.memopt (convert cmp) (v_linked_tree ptr h0) v <==> b))
  =
  let h = get () in
  Spec.equivmem (convert cmp) (v_linked_tree ptr h) v;
  if is_null_t #a ptr then (
    (**) null_is_leaf ptr;
    return false
  ) else (
    (**) let node = unpack_tree ptr in
    let data = get_data node in
    let delta = cmp v data in
    if I.eq delta szero then begin
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      return true
    end else if I.lt delta szero then begin
      let b = member cmp (get_left node) v in
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      return b
    end else begin
      let b = member cmp (get_right node) v in
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      return b
    end
  )
#pop-options
