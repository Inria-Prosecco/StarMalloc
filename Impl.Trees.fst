module Impl.Trees

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module Spec = Spec.Trees
module U = FStar.UInt64
module I = FStar.Int64
module M = FStar.Math.Lib

open Impl.Core
open Impl.Common

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@Trees
inline_for_extraction noextract
let create_leaf (#a: Type0) (_: unit) : Steel (t a)
  emp (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_linked_tree ptr h1 == Spec.Leaf)
  = intro_linked_tree_leaf ();
    // TODO: it should be possible to remove next line
    let h = get () in
    return null_t

//@Trees
#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
let create_tree (#a: Type0) (v: a) : Steel (t a)
  emp (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_linked_tree ptr h1 ==
    Spec.Node v Spec.Leaf Spec.Leaf (U.v one) (U.v one))
  =
  let l = create_leaf () in
  let r = create_leaf () in
  let sr = malloc 1UL in
  let hr = malloc 1UL in
  let n = mk_node v l r sr hr in
  let ptr = malloc n in
  pack_tree ptr l r sr hr;
  return ptr
#pop-options

//@Trees
inline_for_extraction noextract
let sot_wds (#a: Type) (ptr: t a)
  : Steel (U.t)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures (fun h0 s h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    U.v s == Spec.sot_wds (v_linked_tree ptr h0) /\
    U.v s == Spec.size_of_tree (v_linked_tree ptr h0)
  ))
  =
  if is_null_t ptr then (
    assert (is_null_t ptr);
    null_is_leaf ptr;
    let h = get () in
    assert (0 == Spec.sot_wds (v_linked_tree ptr h));
    return zero
  ) else (
    let h1 = get () in
    (**) let node = unpack_tree ptr in
    let h2 = get () in
    let ptr_t1 = hide (v_linked_tree ptr h1) in
    let ptr_t2 = hide (Spec.Node
      (get_data (sel ptr h2))
      (v_linked_tree (get_left node) h2)
      (v_linked_tree (get_right node) h2)
      (U.v (sel (get_size node) h2))
      (U.v (sel (get_height node) h2))
    ) in
    assert (reveal ptr_t1 == reveal ptr_t2);
    assert (Spec.is_wds (reveal ptr_t1));
    let ptr_s1 = hide (Spec.sot_wds ptr_t1) in
    let ptr_s2 = hide (Spec.sot_wds ptr_t2) in
    assert (reveal ptr_s1 == reveal ptr_s2);
    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));
    let s = read (get_size node) in
    assert (U.v s == Spec.sot_wds (v_linked_tree ptr h1));
    pack_tree ptr
      (get_left node)
      (get_right node)
      (get_size node)
      (get_height node);
    return s
  )

inline_for_extraction noextract
let hot_wdh (#a: Type) (ptr: t a)
  : Steel (U.t)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures (fun h0 h h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    U.v h == Spec.hot_wdh (v_linked_tree ptr h0) /\
    U.v h == Spec.height_of_tree (v_linked_tree ptr h0)
  ))
  =
  if is_null_t ptr then (
    assert (is_null_t ptr);
    null_is_leaf ptr;
    let h = get () in
    assert (0 == Spec.hot_wdh (v_linked_tree ptr h));
    return zero
  ) else (
    let h1 = get () in
    (**) let node = unpack_tree ptr in
    let h2 = get () in
    let ptr_t1 = hide (v_linked_tree ptr h1) in
    let ptr_t2 = hide (Spec.Node
      (get_data (sel ptr h2))
      (v_linked_tree (get_left node) h2)
      (v_linked_tree (get_right node) h2)
      (U.v (sel (get_size node) h2))
      (U.v (sel (get_height node) h2))
    ) in
    assert (reveal ptr_t1 == reveal ptr_t2);
    assert (Spec.is_wds (reveal ptr_t1));
    let ptr_s1 = hide (Spec.sot_wds ptr_t1) in
    let ptr_s2 = hide (Spec.sot_wds ptr_t2) in
    assert (reveal ptr_s1 == reveal ptr_s2);
    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));
    let h = read (get_height node) in
    assert (U.v h == Spec.hot_wdh (v_linked_tree ptr h1));
    pack_tree ptr
      (get_left node)
      (get_right node)
      (get_size node)
      (get_height node);
    return h
  )


//@Trees
let merge_tree (#a: Type0) (v: a) (l r: t a) : Steel (t a)
  (linked_tree l `star` linked_tree r)
  (fun ptr -> linked_tree ptr)
  (requires fun h0 ->
    let sl = Spec.size_of_tree (v_linked_tree l h0) in
    let sr = Spec.size_of_tree (v_linked_tree r h0) in
    let hl = Spec.height_of_tree (v_linked_tree l h0) in
    let hr = Spec.height_of_tree (v_linked_tree r h0) in
    sl + sr + 1 <= c /\
    M.max hl hr + 1 <= c)
  (ensures fun h0 ptr h1 ->
    let sl = Spec.size_of_tree (v_linked_tree l h0) in
    let sr = Spec.size_of_tree (v_linked_tree r h0) in
    let s = sl + sr + 1 in
    let hl = Spec.height_of_tree (v_linked_tree l h0) in
    let hr = Spec.height_of_tree (v_linked_tree r h0) in
    let h = M.max hl hr + 1 in
    s <= c /\
    h <= c /\
    v_linked_tree ptr h1 ==
    Spec.Node v
      (v_linked_tree l h0)
      (v_linked_tree r h0)
      s h)
  =
  let s1 = sot_wds l in
  let s2 = sot_wds r in
  let s = U.add (U.add s1 s2) one in
  let sr = malloc s in
  let h1 = hot_wdh l in
  let h2 = hot_wdh r in
  let h = if U.gt h1 h2 then U.add h1 one else U.add h2 one in
  let hr = malloc h in
  let n = mk_node v l r sr hr in
  let ptr = malloc n in
  pack_tree ptr l r sr hr;
  return ptr

//let rec append_left #a (ptr: t a) (v: a)
//  : Steel (t a)
//  (linked_tree ptr)
//  (fun ptr' -> linked_tree ptr')
//  (requires (fun h0 ->
//    Spec.size_of_tree (v_linked_tree ptr h0) < c))
//  (ensures (fun h0 ptr' h1 ->
//    v_linked_tree ptr' h1
//    == Spec.append_left (v_linked_tree ptr h0) v /\
//    Spec.size_of_tree (v_linked_tree ptr' h1)
//    == Spec.size_of_tree (v_linked_tree ptr h0) + 1 /\
//    Spec.size_of_tree (v_linked_tree ptr' h1) <= c))
//  =
//  let h = get () in
//  assert (Spec.size_of_tree (v_linked_tree ptr h) < c);
//  if is_null_t ptr then (
//    // TODO: use create_leaf?
//    //(**) elim_linked_tree_leaf ptr;
//    (**) null_is_leaf ptr;
//    (**) let second_leaf = create_leaf () in
//    let sr = malloc one in
//    //let node = mk_node v ptr null_t sr in
//    let node = mk_node v ptr second_leaf sr in
//    let new_tree = malloc node in
//    //(**) intro_linked_tree_leaf ();
//    (**) pack_tree new_tree ptr second_leaf sr;
//    return new_tree
//    // return new_tree
//  ) else (
//    let h1 = get () in
//    (**) let node = NTreeC3.unpack_tree ptr in
//    let h2 = get () in
//
//    let ptr_t1 = hide (v_linked_tree ptr h1) in
//    let ptr_t2 = hide (Spec.Node
//      (get_data (sel ptr h2))
//      (v_linked_tree (get_left node) h2)
//      (v_linked_tree (get_right node) h2)
//      (U.v (sel (get_size node) h2))) in
//    assert (reveal ptr_t1 == reveal ptr_t2);
//    assert (Spec.is_wds ptr_t1);
//    assert (Spec.is_wds ptr_t2);
//    let ptr_s1 = hide (Spec.sot_wds (reveal ptr_t1)) in
//    let ptr_s2 = hide (Spec.sot_wds (reveal ptr_t2)) in
//    assert (reveal ptr_s1 == reveal ptr_s2);
//    //Spec.check (reveal ptr_t1);
//    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));
//
//    (**) let new_left = append_left (get_left node) v in
//    let h3 = get () in
//    let old_left_t = hide (v_linked_tree (get_left node) h2) in
//    let new_left_t = hide (v_linked_tree new_left h3) in
//    let old_right_t = hide (v_linked_tree (get_right node) h2) in
//    let new_right_t = hide (v_linked_tree (get_right node) h3) in
//    //let old_left_s = hide (Spec.size_of_tree (reveal old_left_t)) in
//    //let new_left_s = hide (Spec.size_of_tree (reveal new_left_t)) in
//    //let old_right_s = hide (Spec.size_of_tree (reveal old_right_t)) in
//    //let new_right_s = hide (Spec.size_of_tree (reveal new_right_t)) in
//    //assert (fst (Spec.is_wds (reveal ptr_t2)));
//    //assert (reveal ptr_s2 ==
//    //reveal old_left_s + reveal old_right_s + 1);
//
//    //assert (fst (Spec.is_wds (reveal old_left_t)));
//    //assert (fst (Spec.is_wds (reveal new_left_t)));
//    //assert (old_right_t == new_right_t);
//    //assert (fst (Spec.is_wds old_right_t));
//    Spec.append_left_aux_size (reveal old_left_t) v;
//    //assert (reveal new_left_s == reveal old_left_s + 1);
//    //assert (reveal old_right_s == reveal new_right_s);
//
//    // TODO : incr (get_size node);
//    let old_size = read (get_size node) in
//    (***) write (get_size node) (U.add old_size one);
//    let h4 = get () in
//    //assert (sel (get_size node) h4 == U.add (sel (get_size node) h3) one);
//    //assert (U.v (sel (get_size node) h4) == new_left_s + new_right_s + 1);
//
//    let new_node = mk_node
//      (get_data node)
//      new_left
//      (get_right node)
//      (get_size node)
//    in
//    //assert (get_size new_node == get_size node);
//    (***) write ptr new_node;
//    let h5 = get () in
//    //assert (U.v (sel (get_size node) h5) <= c);
//    (**) pack_tree ptr new_left (get_right node) (get_size node);
//    return ptr
//  )
//
//// Alternative possible dans le corps de la fonction suivante
////free old_sr;
////let new_sr = malloc (old_size + 1) in
//
//let rec append_right #a (ptr: t a) (v: a)
//  : Steel (t a)
//  (linked_tree ptr)
//  (fun ptr' -> linked_tree ptr')
//  (requires (fun h0 ->
//    Spec.size_of_tree (v_linked_tree ptr h0) < c))
//  (ensures (fun h0 ptr' h1 ->
//    v_linked_tree ptr' h1
//    == Spec.append_right (v_linked_tree ptr h0) v))
//  =
//  let h = get () in
//  assert (Spec.size_of_tree (v_linked_tree ptr h) < c);
//  if is_null_t ptr then (
//    //(**) elim_linked_tree_leaf ptr;
//    (**) null_is_leaf ptr;
//    (**) let second_leaf = create_leaf () in
//    let sr = malloc one in
//    let node = mk_node v second_leaf ptr sr in
//    let new_tree = malloc node in
//    //(**) intro_linked_tree_leaf ();
//    (**) pack_tree new_tree second_leaf ptr sr;
//    return new_tree
//  ) else (
//    (**) let node = unpack_tree ptr in
//    let h2 = get () in
//    let ptr_t2 = hide (Spec.Node
//      (get_data (sel ptr h2))
//      (v_linked_tree (get_left node) h2)
//      (v_linked_tree (get_right node) h2)
//      (U.v (sel (get_size node) h2))) in
//    assert (Spec.is_wds ptr_t2);
//    let ptr_s2 = hide (Spec.sot_wds (reveal ptr_t2)) in
//    //Spec.check (reveal ptr_t2);
//    assert (reveal ptr_s2 == Spec.size_of_tree (reveal ptr_t2));
//
//    (**) let new_right = append_right (get_right node) v in
//    let h3 = get () in
//    let old_left_t = hide (v_linked_tree (get_left node) h2) in
//    let new_left_t = hide (v_linked_tree (get_left node) h3) in
//    let old_right_t = hide (v_linked_tree (get_right node) h2) in
//    let new_right_t = hide (v_linked_tree new_right h3) in
//    //let old_left_s = hide (Spec.size_of_tree (reveal old_left_t)) in
//    //let new_left_s = hide (Spec.size_of_tree (reveal new_left_t)) in
//    //let old_right_s = hide (Spec.size_of_tree (reveal old_right_t)) in
//    //let new_right_s = hide (Spec.size_of_tree (reveal new_right_t)) in
//    //assert (reveal ptr_s2
//    //== reveal old_left_s + reveal old_right_s + 1);
//    //assert (reveal new_left_s == reveal old_left_s);
//    Spec.append_right_aux_size (reveal old_right_t) v;
//    //assert (reveal new_right_s == reveal old_right_s + 1);
//
//    let old_size = read (get_size node) in
//    write (get_size node) (U.add old_size one);
//    let new_node = mk_node
//      (get_data node)
//      (get_left node)
//      new_right
//      (get_size node)
//    in
//    write ptr new_node;
//    (**) pack_tree ptr (get_left node) new_right (get_size node);
//    return ptr
//  )

(*)
//@Trees
#push-options "--fuel 1 --ifuel 1"
let rec height (#a: Type0) (ptr: t a)
  : Steel U.t (linked_tree ptr) (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun h0 x h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    Spec.height (v_linked_tree ptr h0) == U.v x)
  =
  if is_null_t ptr then (
    (**) null_is_leaf ptr;
    return zero
  ) else (
    let h = get () in
    (**) not_null_is_node ptr;
    let s = hide (Spec.sot_wds (v_linked_tree ptr h)) in
    (**) let node = unpack_tree ptr in
    assert (reveal s <= c);
    Spec.height_lte_size (v_linked_tree ptr h);
    assert (Spec.height (v_linked_tree ptr h) <= c);
    let hleft = height (get_left node) in
    let hright = height (get_right node) in
    (**) pack_tree ptr (get_left node) (get_right node) (get_size node);
    let hptr = if U.gt hleft hright then U.add hleft one else U.add hright one in
    return hptr
  )
#pop-options
