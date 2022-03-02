module Impl.Trees.Rotate2.Old

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
module I = FStar.Int64

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
    height_of_tree (opt_get r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_right_left_wdm (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (size_of_tree (v_linked_tree ptr h) <= c);
  rotate_right_left_size (v_linked_tree ptr h);
  assert (size_of_tree (opt_get (rotate_right_left_wdm (v_linked_tree ptr h)))
  == size_of_tree (v_linked_tree ptr h));
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
  let s1 = sot_wds (get_left x_node) in
  let s2 = sot_wds (get_left y_node) in
  let s3 = sot_wds (get_right y_node) in
  let s4 = sot_wds (get_right z_node) in

  let h1 = hot_wdh (get_left x_node) in
  let h2 = hot_wdh (get_left y_node) in
  let h3 = hot_wdh (get_right y_node) in
  let h4 = hot_wdh (get_right z_node) in
  let h12 = if U.gt h1 h2 then U.add h1 one else U.add h2 one in
  let h34 = if U.gt h3 h4 then U.add h3 one else U.add h4 one in
  let h1234 = if U.gt h12 h34 then U.add h12 one else U.add h34 one in

  let s12 = U.add (U.add s1 s2) one in
  write (get_size y_node) s12;
  write (get_height y_node) h12;
  let s34 = U.add (U.add s3 s4) one in
  write (get_size z_node) s34;
  write (get_height z_node) h34;
  write (get_height x_node) h1234;

  let new_x = mk_node x (get_left x_node) (get_left y_node)
    (get_size y_node) (get_height y_node) in
  let new_z = mk_node z (get_right y_node) (get_right z_node)
    (get_size z_node) (get_height z_node) in
  let new_y = mk_node y ptr (get_right x_node)
    (get_size x_node) (get_height x_node) in

  write ptr new_x;
  write (get_right x_node) new_z;
  write (get_left z_node) new_y;

  (**) pack_tree ptr (get_left x_node) (get_left y_node)
    (get_size y_node) (get_height y_node);
  (**) pack_tree (get_right x_node) (get_right y_node) (get_right z_node)
    (get_size z_node) (get_height z_node);
  (**) pack_tree (get_left z_node) ptr (get_right x_node)
    (get_size x_node) (get_height x_node);

  return (get_left z_node)
#pop-options
