module Impl.Trees.Rotate.M

open Steel.Effect.Atomic
open Steel.Effect

module U = FStar.UInt64
module G = FStar.Ghost

open Spec.Trees
open Impl.Core
open Impl.Trees.Types
open Impl.Trees.M

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@Trees (rotate*)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rotate_left (ptr: t)
  : Steel t
  (linked_tree p ptr)
  (fun ptr' -> linked_tree p ptr')
  (requires (fun h0 ->
    let t = v_linked_tree p ptr h0 in
    let r = rotate_left t in
    Some? r /\
    height_of_tree (Some?.v r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_left (v_linked_tree p ptr h0)
    == Some (v_linked_tree p ptr' h1)
  ))
  =
  let h = get () in
  assert (size_of_tree (v_linked_tree p ptr h) <= c);
  rotate_left_size (v_linked_tree p ptr h);
  (**) node_is_not_null p ptr;
  (**) let x_node = unpack_tree p ptr in
  let x = get_data x_node in
  (**) node_is_not_null p (get_right x_node);
  (**) let z_node = unpack_tree p (get_right x_node) in
  let z = get_data z_node in

  let new_subnode = merge_tree_no_alloc x
    (get_left x_node) (get_left z_node)
    ptr in
  let new_node = merge_tree_no_alloc z
    new_subnode (get_right z_node)
    (get_right x_node) in
  return new_node
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rotate_right (ptr: t)
  : Steel t
  (linked_tree p ptr)
  (fun ptr' -> linked_tree p ptr')
  (requires (fun h0 ->
    let t = v_linked_tree p ptr h0 in
    let r = rotate_right t in
    Some? r /\
    height_of_tree (Some?.v r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_right (v_linked_tree p ptr h0)
    == Some (v_linked_tree p ptr' h1)
  ))
  =
  let h = get () in
  assert (size_of_tree (v_linked_tree p ptr h) <= c);
  rotate_right_size (v_linked_tree p ptr h);
  (**) node_is_not_null p ptr;
  (**) let x_node = unpack_tree p ptr in
  let x = get_data x_node in
  (**) node_is_not_null p (get_left x_node);
  let z_node = unpack_tree p (get_left x_node) in
  let z = get_data z_node in

  let new_subnode = merge_tree_no_alloc x
    (get_right z_node) (get_right x_node)
    ptr in
  let new_node = merge_tree_no_alloc z
    (get_left z_node) new_subnode
    (get_left x_node) in
  return new_node
#pop-options
