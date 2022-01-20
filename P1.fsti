module P1

open NTreeC3
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module Spec = Trees
module U = FStar.UInt64

#set-options "--ide_id_info_off"

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

/// Returns the size of the tree that [ptr] points to, in O(1)
val sot_wds (#a: Type) (ptr: t a)
    : Steel (U.t) (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures (fun h0 s h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        U.v s == Spec.sot_wds (v_linked_tree ptr h0) /\
        U.v s == Spec.size_of_tree (v_linked_tree ptr h0)))

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
