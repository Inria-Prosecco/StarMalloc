module Impl.Trees.Rotate.M

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
module U32 = FStar.UInt32
module I = FStar.Int64

open Spec.Trees
open Impl.Core
open Impl.Common
open Impl.Trees.M

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

let a = Impl.Trees.M.a

//@Trees (rotate*)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rotate_left (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = rotate_left t in
    Some? r /\
    height_of_tree (Some?.v r) <= height_of_tree t
  ))

  (ensures (fun h0 ptr' h1 ->
    rotate_left (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (size_of_tree (v_linked_tree ptr h) <= c);
  rotate_left_size (v_linked_tree ptr h);
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_right x_node);
  (**) let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in

  let new_subnode = merge_tree_no_alloc x
    (get_left x_node) (get_left z_node)
    (get_size z_node) (get_height z_node) ptr in
  let new_node = merge_tree_no_alloc z
    new_subnode (get_right z_node)
    (get_size x_node) (get_height x_node) (get_right x_node) in
  return new_node
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rotate_right (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = rotate_right t in
    Some? r /\
    height_of_tree (Some?.v r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_right (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (size_of_tree (v_linked_tree ptr h) <= c);
  rotate_right_size (v_linked_tree ptr h);
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_left x_node);
  let z_node = unpack_tree (get_left x_node) in
  let z = get_data z_node in

  let new_subnode = merge_tree_no_alloc x
    (get_right z_node) (get_right x_node)
    (get_size z_node) (get_height z_node) ptr in
  let new_node = merge_tree_no_alloc z
    (get_left z_node) new_subnode
    (get_size x_node) (get_height x_node) (get_left x_node) in
  return new_node
#pop-options