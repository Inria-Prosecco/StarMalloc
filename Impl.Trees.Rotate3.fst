module Impl.Trees.Rotate3

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

open Spec.Trees
open Impl.Core
open Impl.Common
open Impl.Trees

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rotate_left_right (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = rotate_left_right_wdm t in
    Some? r /\
    height_of_tree (opt_get r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_left_right (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  (**) node_is_not_null ptr;
  // original root node
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_left x_node);
  // original left node
  // z = get_left x_node
  (**) let z_node = unpack_tree (get_left x_node) in
  let z = get_data z_node in
  (**) node_is_not_null (get_right z_node);
  // original right (left node)
  // y = get_right (z_node)
  (**) let y_node = unpack_tree (get_right z_node) in
  let y = get_data y_node in

  let new_z = merge_tree_no_alloc z
    (get_left z_node) (get_left y_node)
    (get_size y_node) (get_height y_node) (get_left x_node) in
  let new_x = merge_tree_no_alloc x
    (get_right y_node) (get_right x_node)
    (get_size z_node) (get_height z_node) ptr in
  let new_y = merge_tree_no_alloc y
    new_z new_x
    (get_size x_node) (get_height x_node) (get_right z_node) in
  return new_y
#pop-options
