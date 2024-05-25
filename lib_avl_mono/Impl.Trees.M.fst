module Impl.Trees.M

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module Spec = Spec.Trees
module U = FStar.UInt64
module I = FStar.Int64
module M = FStar.Math.Lib
module G = FStar.Ghost

open Impl.Core
open Impl.Common
open Impl.Trees.Types

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@Trees
inline_for_extraction noextract
let create_leaf
  (_:unit)
  : Steel t
  emp (fun ptr -> linked_tree p ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_linked_tree p ptr h1 == Spec.Leaf /\
    (G.reveal p) ptr)

  =
  admit ();
  intro_linked_tree_leaf p ();
  return null_t

//@Trees
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
inline_for_extraction noextract
let create_tree
  (f1: f_malloc) (f2: f_free)
  (v: data)
  : Steel t
  emp (fun ptr -> linked_tree p ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    not (is_null_t ptr) /\
    v_linked_tree p ptr h1 ==
    Spec.Node v Spec.Leaf Spec.Leaf (U.v one) (U.v one))
  =
  let l = create_leaf () in
  let r = create_leaf () in
  assert ((G.reveal p) l);
  let sr = one in
  let hr = one in
  let n = mk_node v l r sr hr in
  let ptr = f1 n in
  pack_tree p ptr l r sr hr;
  node_is_not_null p ptr;
  return ptr
#pop-options

//@Trees
inline_for_extraction noextract
let sot_wds
  //(f1: f_malloc) (f2: f_free)
  (ptr: t)
  : Steel U.t
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun _ -> True)
  (ensures (fun h0 s h1 ->
    v_linked_tree p ptr h0 == v_linked_tree p ptr h1 /\
    U.v s == Spec.sot_wds (v_linked_tree p ptr h0) /\
    U.v s == Spec.size_of_tree (v_linked_tree p ptr h0)
  ))
  =
  if is_null_t ptr then (
    assert (is_null_t ptr);
    null_is_leaf p ptr;
    let h = get () in
    assert (0 == Spec.sot_wds (v_linked_tree p ptr h));
    return zero
  ) else (
    let h1 = get () in
    (**) let node = unpack_tree p ptr in
    let h2 = get () in
    let ptr_t1 = hide (v_linked_tree p ptr h1) in
    let ptr_t2 = hide (Spec.Node
      (get_data (sel ptr h2))
      (v_linked_tree p (get_left node) h2)
      (v_linked_tree p (get_right node) h2)
      (U.v (get_size node))
      (U.v (get_height node))
    ) in
    assert (reveal ptr_t1 == reveal ptr_t2);
    assert (Spec.is_wds (reveal ptr_t1));
    let ptr_s1 = hide (Spec.sot_wds ptr_t1) in
    let ptr_s2 = hide (Spec.sot_wds ptr_t2) in
    assert (reveal ptr_s1 == reveal ptr_s2);
    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));
    let s = (get_size node) in
    assert (U.v s == Spec.sot_wds (v_linked_tree p ptr h1));
    pack_tree p ptr
      (get_left node)
      (get_right node)
      (get_size node)
      (get_height node);
    return s
  )

inline_for_extraction noextract
let hot_wdh
  //(f1: f_malloc) (f2: f_free)
  (ptr: t)
  : Steel U.t
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun _ -> True)
  (ensures (fun h0 h h1 ->
    v_linked_tree p ptr h0 == v_linked_tree p ptr h1 /\
    U.v h == Spec.hot_wdh (v_linked_tree p ptr h0) /\
    U.v h == Spec.height_of_tree (v_linked_tree p ptr h0)
  ))
  =
  if is_null_t ptr then (
    assert (is_null_t ptr);
    null_is_leaf p ptr;
    let h = get () in
    assert (0 == Spec.hot_wdh (v_linked_tree p ptr h));
    return zero
  ) else (
    let h1 = get () in
    (**) let node = unpack_tree p ptr in
    let h2 = get () in
    let ptr_t1 = hide (v_linked_tree p ptr h1) in
    let ptr_t2 = hide (Spec.Node
      (get_data (sel ptr h2))
      (v_linked_tree p (get_left node) h2)
      (v_linked_tree p (get_right node) h2)
      (U.v (get_size node))
      (U.v (get_height node))
    ) in
    assert (reveal ptr_t1 == reveal ptr_t2);
    assert (Spec.is_wds (reveal ptr_t1));
    let ptr_s1 = hide (Spec.sot_wds ptr_t1) in
    let ptr_s2 = hide (Spec.sot_wds ptr_t2) in
    assert (reveal ptr_s1 == reveal ptr_s2);
    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));
    let h = (get_height node) in
    assert (U.v h == Spec.hot_wdh (v_linked_tree p ptr h1));
    pack_tree p ptr
      (get_left node)
      (get_right node)
      (get_size node)
      (get_height node);
    return h
  )

//@Trees
let merge_tree
  (f1: f_malloc) (f2: f_free)
  (v: data) (l r: t)
  : Steel t
  (linked_tree p l `star` linked_tree p r)
  (fun ptr -> linked_tree p ptr)
  (requires fun h0 ->
    let sl = Spec.size_of_tree (v_linked_tree p l h0) in
    let sr = Spec.size_of_tree (v_linked_tree p r h0) in
    let hl = Spec.height_of_tree (v_linked_tree p l h0) in
    let hr = Spec.height_of_tree (v_linked_tree p r h0) in
    sl + sr + 1 <= c /\
    M.max hl hr + 1 <= c)
  (ensures fun h0 ptr h1 ->
    v_linked_tree p ptr h1
    == Spec.merge_tree
      v
      (v_linked_tree p l h0)
      (v_linked_tree p r h0)
    /\
    Spec.csize (v_linked_tree p ptr h1) <= c /\
    Spec.cheight (v_linked_tree p ptr h1) <= c)
  =
  let s1 = sot_wds l in
  let s2 = sot_wds r in
  let s = U.add (U.add s1 s2) one in
  let h1 = hot_wdh l in
  let h2 = hot_wdh r in
  let h = U.add (umax h1 h2) one in
  let n = mk_node v l r s h in
  let ptr = f1 n in
  pack_tree p ptr l r s h;
  return ptr

inline_for_extraction noextract
let merge_tree_no_alloc
  (v: data) (l r: t) (ptr: t)
  : Steel t
  (linked_tree p l `star`
  linked_tree p r `star`
  vptr ptr)
  (fun ptr' -> linked_tree p ptr')
  (requires fun h0 ->
    let sl = Spec.size_of_tree (v_linked_tree p l h0) in
    let sr = Spec.size_of_tree (v_linked_tree p r h0) in
    let hl = Spec.height_of_tree (v_linked_tree p l h0) in
    let hr = Spec.height_of_tree (v_linked_tree p r h0) in
    sl + sr + 1 <= c /\
    M.max hl hr + 1 <= c /\
    (G.reveal p) l /\
    (G.reveal p) r
  )
  (ensures fun h0 ptr' h1 ->
    v_linked_tree p ptr' h1
    == Spec.merge_tree
      v
      (v_linked_tree p l h0)
      (v_linked_tree p r h0)
    /\
    Spec.csize (v_linked_tree p ptr' h1) <= c /\
    Spec.cheight (v_linked_tree p ptr' h1) <= c)
  =
  let s1 = sot_wds l in
  let s2 = sot_wds r in
  let s = U.add (U.add s1 s2) one in
  let h1 = hot_wdh l in
  let h2 = hot_wdh r in
  let h = U.add (umax h1 h2) one in
  let n = mk_node v l r s h in
  write ptr n;
  pack_tree p ptr l r s h;
  return ptr
