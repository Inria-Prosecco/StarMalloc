module Impl.Trees.Rotate.Old

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

//@Trees (rotate*)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rotate_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = rotate_left_wdm t in
    Some? r /\
    height_of_tree (opt_get r) <= height_of_tree t
  ))

  (ensures (fun h0 ptr' h1 ->
    rotate_left_wdm (v_linked_tree ptr h0)
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
  let s1 = sot_wds (get_left x_node) in
  let s2 = sot_wds (get_left z_node) in
  let s12 = U.add (U.add s1 s2) one in

  let h1 = hot_wdh (get_left x_node) in
  let h2 = hot_wdh (get_left z_node) in
  let h3 = hot_wdh (get_right z_node) in
  let h12 = if U.gt h1 h2 then U.add h1 one else U.add h2 one in
  let h123 = if U.gt h12 h3 then U.add h12 one else U.add h3 one in
  write (get_size z_node) s12;
  write (get_height z_node) h12;
  let new_subnode = mk_node x
    (get_left x_node) (get_left z_node)
    (get_size z_node) (get_height z_node) in
  write (get_height x_node) h123;
  let new_node = mk_node z ptr (get_right z_node)
    (get_size x_node) (get_height x_node) in
  write (get_right x_node) new_node;
  write ptr new_subnode;
  (**) pack_tree ptr (get_left x_node) (get_left z_node)
  (get_size z_node) (get_height z_node);
  (**) pack_tree (get_right x_node) ptr (get_right z_node)
  (get_size x_node) (get_height x_node);
  return (get_right x_node)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rotate_right (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = rotate_right_wdm t in
    Some? r /\
    height_of_tree (opt_get r) <= height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    rotate_right_wdm (v_linked_tree ptr h0)
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
  let s1 = sot_wds (get_right z_node) in
  let s2 = sot_wds (get_right x_node) in
  let s12 = U.add (U.add s1 s2) one in

  let h1 = hot_wdh (get_right z_node) in
  let h2 = hot_wdh (get_right x_node) in
  let h3 = hot_wdh (get_left z_node) in
  let h12 = if U.gt h1 h2 then U.add h1 one else U.add h2 one in
  let h123 = if U.gt h12 h3 then U.add h12 one else U.add h3 one in
  write (get_size z_node) s12;
  write (get_height z_node) h12;
  let new_subnode = mk_node x (get_right z_node) (get_right x_node)
    (get_size z_node) (get_height z_node) in
  write (get_height x_node) h123;
  let new_node = mk_node z (get_left z_node) ptr
    (get_size x_node) (get_height x_node) in
  write (get_left x_node) new_node;
  write ptr new_subnode;
  (**) pack_tree ptr (get_right z_node) (get_right x_node)
    (get_size z_node) (get_height z_node);
  (**) pack_tree (get_left x_node) (get_left z_node) ptr
    (get_size x_node) (get_height x_node);
  return (get_left x_node)
#pop-options
