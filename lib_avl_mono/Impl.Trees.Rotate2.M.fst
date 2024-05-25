module Impl.Trees.Rotate2.M

open Steel.Effect.Atomic
open Steel.Effect

module U = FStar.UInt64

open Spec.Trees
open Impl.Core
open Impl.Trees.Types
open Impl.Trees.M

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

val rotate_right_left (ptr: t)
  : Steel t
  (linked_tree p ptr)
  (fun ptr' -> linked_tree p ptr')
  (requires (fun h0 ->
    let t = v_linked_tree p ptr h0 in
    let r = rotate_right_left t in
    Some? r /\
    height_of_tree (Some?.v r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_right_left (v_linked_tree p ptr h0)
    == Some (v_linked_tree p ptr' h1)
  ))

module G = FStar.Ghost

#push-options "--fuel 1 --ifuel 1 --z3rlimit 75"
let rotate_right_left ptr
  =
  let h0 = get () in
  let s0 = G.hide (size_of_tree (v_linked_tree p ptr h0)) in
  assert (G.reveal s0 <= c);
  (**) node_is_not_null p ptr;
  // original root node
  (**) let x_node = unpack_tree p ptr in
  let x = get_data x_node in
  (**) node_is_not_null p (get_right x_node);
  // original right node
  // z = get_right x_node
  (**) let z_node = unpack_tree p (get_right x_node) in
  let z = get_data z_node in
  (**) node_is_not_null p (get_left z_node);
  // original left (right node)
  // y = get_left (z_node)
  (**) let y_node = unpack_tree p (get_left z_node) in
  let y = get_data y_node in

  let new_x = merge_tree_no_alloc x
    (get_left x_node) (get_left y_node)
    ptr in
  let new_z = merge_tree_no_alloc z
    (get_right y_node) (get_right z_node)
    (get_right x_node) in
  let new_y = merge_tree_no_alloc y
    new_x new_z
    (get_left z_node) in
  return new_y
#pop-options
