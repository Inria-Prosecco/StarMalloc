module P1

open NTreeC3
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module Spec = Trees
module U = FStar.UInt64
module I = FStar.Int64

#set-options "--ide_id_info_off"

inline_for_extraction noextract
let one = U.uint_to_t 1
inline_for_extraction noextract
let zero = U.uint_to_t 0

inline_for_extraction noextract
let sone = I.int_to_t 1
inline_for_extraction noextract
let szero = I.int_to_t 0

val create_leaf (#a: Type0) (_: unit) : Steel (t a)
  emp (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_linked_tree ptr h1 == Trees.Leaf)

val create_tree (#a: Type0) (v: a) : Steel (t a)
  emp (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_linked_tree ptr h1 ==
    Trees.Node v Trees.Leaf Trees.Leaf (U.v one))

/// Returns the size of the tree that [ptr] points to, in O(1)
val sot_wds (#a: Type) (ptr: t a)
    : Steel (U.t) (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures (fun h0 s h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        U.v s == Spec.sot_wds (v_linked_tree ptr h0) /\
        U.v s == Spec.size_of_tree (v_linked_tree ptr h0)))

val merge_tree (#a: Type0) (v: a) (l: t a) (r: t a) : Steel (t a)
  (linked_tree l `star` linked_tree r)
  (fun ptr -> linked_tree ptr)
  (requires fun h0 ->
    let s1 = Spec.size_of_tree (v_linked_tree l h0) in
    let s2 = Spec.size_of_tree (v_linked_tree r h0) in
    s1 + s2 < c - 1)
  (ensures fun h0 ptr h1 ->
    let s1 = Spec.size_of_tree (v_linked_tree l h0) in
    let s2 = Spec.size_of_tree (v_linked_tree r h0) in
    let s = s1 + s2 + 1 in
    s < c /\
    v_linked_tree ptr h1 ==
    Trees.Node v
      (v_linked_tree l h0)
      (v_linked_tree r h0)
      s)

/// This module provides a library of operations on trees.
/// The definition of the `linked_tree` predicate is hidden behind the `Selectors.Tree.Core` interface.
/// As such, folding and unfolding this predicate can only be done by calling the helpers exposed in Selectors.Tree.Core.

(**** Stateful operations on generic trees *)
/// Appends value [v] at the leftmost leaf of the tree that [ptr] points to.
val append_left (#a: Type0) (ptr: t a) (v: a)
    : Steel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> Spec.size_of_tree (v_linked_tree ptr h0) < c - 1))
      (ensures (fun h0 ptr' h1 -> v_linked_tree ptr' h1 == Spec.append_left (v_linked_tree ptr h0) v))

/// Appends value [v] at the rightmost leaf of the tree that [ptr] points to.
val append_right (#a: Type0) (ptr: t a) (v: a)
    : Steel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> Spec.size_of_tree (v_linked_tree ptr h0) < c - 1))
      (ensures (fun h0 ptr' h1 ->
        v_linked_tree ptr' h1 == Spec.append_right (v_linked_tree ptr h0) v
      ))

/// Returns the height of the tree that [ptr] points to
val height (#a: Type0) (ptr: t a)
    : Steel U.t (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        Spec.height (v_linked_tree ptr h0) == U.v x)

/// Returns a boolean indicating whether element [v] belongs to the tree that [ptr] points to
val member (#a: eqtype) (ptr: t a) (v: a)
    : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        (Spec.mem (v_linked_tree ptr h0) v <==> b))

type cmp (a: Type) = compare: (a -> a -> I.t){
  squash (forall x. I.eq (compare x x) I.zero) /\
  squash (forall x y. I.gt (compare x y) I.zero
                 <==> I.lt (compare y x) I.zero) /\
  squash (forall x  y z. I.gte (compare x y) I.zero /\
                         I.gte (compare y z) I.zero /\
                         I.gte (compare x z) I.zero)
}

let convert (#a: Type) (cmp: cmp a) : GTot (Spec.cmp a)
  = fun x y -> I.v (cmp x y)

val insert_bst (#a: Type0) (cmp:cmp a) (ptr:t a) (v: a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.size_of_tree (v_linked_tree ptr h0) < c - 1 /\
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0) /\
    Spec.insert_bst (convert cmp) (v_linked_tree ptr h0) v
    == v_linked_tree ptr' h1)

(*** Rotation functions used internally to balance AVL trees ***)

val rotate_left (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_left_wds (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_left_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

val rotate_right (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_right_wds (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_right_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

val rotate_right_left (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_right_left_wds (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_right_left_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

val rotate_left_right (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_left_right_wds (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_left_right_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

(*** Functions related to AVL trees ***)

/// Returns a boolean indicating if the tree that [ptr] points to is balanced
val is_balanced (#a: Type) (ptr: t a)
    : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun h0 -> True)
    (ensures (fun h0 b h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        Spec.is_balanced (v_linked_tree ptr h0) == b))

(*)
/// Rebalances a tree according to the comparison function [cmp] on the tree elements
val rebalance_avl (#a: Type) (cmp:Spec.cmp a) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> True)
    (ensures fun h0 ptr' h1 ->
        Spec.rebalance_avl_wds (v_linked_tree ptr h0) == v_linked_tree ptr' h1)

/// Inserts an element [v] in an AVL tree, while preserving the AVL tree invariant
val insert_avl (#a: Type) (cmp:Spec.cmp a) (ptr: t a) (v: a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Spec.is_avl cmp (v_linked_tree ptr h0))
    (ensures fun h0 ptr' h1 ->
        Spec.is_avl cmp (v_linked_tree ptr h0) /\
        Spec.insert_avl cmp (v_linked_tree ptr h0) v == v_linked_tree ptr' h1)
