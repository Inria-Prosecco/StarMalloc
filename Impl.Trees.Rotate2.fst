module Impl.Trees.Rotate2

//open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

//module U = FStar.UInt64
//module I = FStar.Int64

open Spec.Trees
open Impl.Core
open Impl.Common
open Impl.Trees

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rotate_right_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = rotate_right_left_wdm t in
    Some? r /\
    height_of_tree (Some?.v r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_right_left (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  (**) node_is_not_null ptr;
  // original root node
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_right x_node);
  // original right node
  // z = get_right x_node
  (**) let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  (**) node_is_not_null (get_left z_node);
  // original left (right node)
  // y = get_left (z_node)
  (**) let y_node = unpack_tree (get_left z_node) in
  let y = get_data y_node in

  let new_x = merge_tree_no_alloc x
    (get_left x_node) (get_left y_node)
    (get_size y_node) (get_height y_node) ptr in
  let new_z = merge_tree_no_alloc z
    (get_right y_node) (get_right z_node)
    (get_size z_node) (get_height z_node) (get_right x_node) in
  let new_y = merge_tree_no_alloc y
    new_x new_z
    (get_size x_node) (get_height x_node) (get_left z_node) in
  return new_y
#pop-options
