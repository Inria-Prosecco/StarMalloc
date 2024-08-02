module Impl.Trees.Rotate3.M

open Steel.Effect.Atomic
open Steel.Effect

module U = FStar.UInt64
module G = FStar.Ghost

open Spec.Trees
open Impl.Core
open Impl.Trees.Types
open Impl.Trees.M

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

val rotate_left_right (ptr: t)
  : Steel t
  (linked_tree pred p ptr)
  (fun ptr' -> linked_tree pred p ptr')
  (requires (fun h0 ->
    let t = v_linked_tree pred p ptr h0 in
    let r = rotate_left_right t in
    Some? r /\
    height_of_tree (Some?.v r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_left_right (v_linked_tree pred p ptr h0)
    == Some (v_linked_tree pred p ptr' h1)
  ))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 75"
let rotate_left_right ptr
  =
  let h0 = get () in
  let s0 = G.hide (size_of_tree (v_linked_tree pred p ptr h0)) in
  assert (G.reveal s0 <= c);
  (**) node_is_not_null pred p ptr;
  // original root node
  (**) let x_node = unpack_tree pred p ptr in
  let x = get_data x_node in
  change_equal_slprop
    (p (get_data x_node))
    (p x);
  (**) node_is_not_null pred p (get_left x_node);
  // original left node
  // z = get_left x_node
  (**) let z_node = unpack_tree pred p (get_left x_node) in
  let z = get_data z_node in
  change_equal_slprop
    (p (get_data z_node))
    (p z);
  (**) node_is_not_null pred p (get_right z_node);
  // original right (left node)
  (**) let y_node = unpack_tree pred p (get_right z_node) in
  let y = get_data y_node in
  change_equal_slprop
    (p (get_data y_node))
    (p y);

  let new_z = merge_tree_no_alloc z
    (get_left z_node) (get_left y_node)
    (get_left x_node) in
  let new_x = merge_tree_no_alloc x
    (get_right y_node) (get_right x_node)
    ptr in
  let new_y = merge_tree_no_alloc y
    new_z new_x
    (get_right z_node) in
  return new_y
#pop-options
