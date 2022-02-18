module Impl.Trees.Rotate

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

// TODO : please prettify output after squash equiv...
//#push-options "--ifuel 1 --fuel 2 --z3rlimit 200"
(*
let rotate_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 -> Some? (Spec.rotate_left (v_linked_tree ptr h0)))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_left_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
  ))
  =
  let h0 = get () in
  Spec.rotate_left_size (v_linked_tree ptr h0);
  assert (Spec.size_of_tree (Spec.get (Spec.rotate_left_wds (v_linked_tree ptr h0)))
  == Spec.size_of_tree (v_linked_tree ptr h0));
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  // let ptr2 = get_right x_node in
  // TODO : node_is_not_null ptr2 should work
  (**) node_is_not_null (get_right x_node);
  (**) let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  //let h1 = get () in
  //let t1 = v_linked_tree (get_left x_node) h1 in
  //let t2 = v_linked_tree (get_left z_node) h1 in
  //let t3 = v_linked_tree (get_right z_node) h1 in
  let s1 = sot_wds (get_left x_node) in
  let s2 = sot_wds (get_left z_node) in
  let sx = U.add (U.add s1 s2) one in
  //assert (U.v sx == (U.v s1) + (U.v s2) + 1);
  //assert (U.v s1 = Spec.sot_wds (v_linked_tree (get_left x_node) h1));
  //assert (U.v s2 = Spec.sot_wds (v_linked_tree (get_left z_node) h1));
  write (get_size z_node) sx;
  let tx = mk_node x (get_left x_node) (get_left z_node) (get_size z_node) in
  write ptr tx;
  //let h = get () in
  //assert (fst (Spec.is_wds (v_linked_tree ptr h)));
  //assert (U.v (sel (get_size z_node) h) == Spec.size_of_tree (v_linked_tree (get_left x_node) h)
                                  //+ Spec.size_of_tree (v_linked_tree (get_left z_node) h) + 1);
  //let h = get () in
  //assert (fst (Spec.is_wds (v_linked_tree ptr h)));
  pack_tree ptr (get_left x_node) (get_left z_node) (get_size z_node);
  let tz = mk_node z ptr (get_right z_node) (get_size x_node) in
  write (get_right x_node) tz;
  //let h2 = get() in
  //let t1' = v_linked_tree (get_left x_node) h2 in
  //let h = get () in
  //assert (fst (Spec.is_wds (v_linked_tree (get_right x_node) h)));
  //assert (sel (get_size x_node) h == Spec.size_of_tree (v_linked_tree ptr h)
  //                                 + Spec.size_of_tree (v_linked_tree (get_right z_node) h) + 1);
  pack_tree (get_right x_node) ptr (get_right z_node) (get_size x_node);
  //let h1 = get () in
  //assert (Spec.size_of_tree (v_linked_tree ptr h1) == Spec.size_of_tree (v_linked_tree ptr h0));
  return (get_right x_node)
*)
//(*)
//#push-options "--ifuel 1 --fuel 2"

//@Trees (rotate*)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rotate_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = Spec.rotate_left_wdm t in
    Some? r /\
    Spec.height_of_tree (Spec.get r) <= Spec.height_of_tree t
  ))

  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_left_wdm (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_left_size (v_linked_tree ptr h);
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
    let r = Spec.rotate_right_wdm t in
    Some? r /\
    Spec.height_of_tree (Spec.get r) <= Spec.height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_right_wdm (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_right_size (v_linked_tree ptr h);
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rotate_right_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = Spec.rotate_right_left_wdm t in
    Some? r /\
    Spec.height_of_tree (Spec.get r) <= Spec.height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_right_left_wdm (v_linked_tree ptr h0)
    == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_right_left_size (v_linked_tree ptr h);
  assert (Spec.size_of_tree (Spec.get (Spec.rotate_right_left_wdm (v_linked_tree ptr h)))
  == Spec.size_of_tree (v_linked_tree ptr h));
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rotate_left_right (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    let t = v_linked_tree ptr h0 in
    let r = Spec.rotate_left_right_wdm t in
    Some? r /\
    Spec.height_of_tree (Spec.get r) <= Spec.height_of_tree t
  ))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_left_right_wdm (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_left_right_size (v_linked_tree ptr h);
  assert (Spec.size_of_tree (Spec.get (Spec.rotate_left_right_wdm (v_linked_tree ptr h)))
  == Spec.size_of_tree (v_linked_tree ptr h));
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
  let s1 = sot_wds (get_left z_node) in
  let s2 = sot_wds (get_left y_node) in
  let s3 = sot_wds (get_right y_node) in
  let s4 = sot_wds (get_right x_node) in


  let h1 = hot_wdh (get_left z_node) in
  let h2 = hot_wdh (get_left y_node) in
  let h3 = hot_wdh (get_right y_node) in
  let h4 = hot_wdh (get_right x_node) in
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

  let new_z = mk_node z (get_left z_node) (get_left y_node)
    (get_size y_node) (get_height y_node) in
  let new_x = mk_node x (get_right y_node) (get_right x_node)
    (get_size z_node) (get_height z_node) in
  let new_y = mk_node y (get_left x_node) ptr
    (get_size x_node) (get_height x_node) in

  write (get_left x_node) new_z;
  write ptr new_x;
  write (get_right z_node) new_y;

  (**) pack_tree (get_left x_node) (get_left z_node) (get_left y_node)
    (get_size y_node) (get_height y_node);
  (**) pack_tree ptr (get_right y_node) (get_right x_node)
    (get_size z_node) (get_height z_node);
  (**) pack_tree (get_right z_node) (get_left x_node) ptr
    (get_size x_node) (get_height x_node);

  return (get_right z_node)
#pop-options
