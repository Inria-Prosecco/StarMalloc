module ArrayListGen

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef

module A = Steel.Array
module L = FStar.List.Tot
module US = FStar.SizeT
module FS = FStar.FiniteSet.Base
open FStar.FiniteSet.Ambient

(** A library for doubly linked lists, that are located in memory in a contiguous region (an array) *)

/// The type of cells for the doubly linked list. Compared to a standard doubly linked list,
/// the `prev` and `next` fields are not pointers, but offsets in the array containing the list.
/// To keep unsigned (positive) integers, we will represent NULL as 0, and not store anything
/// in the first element slot of the array
val cell (t:Type0) : Type0

inline_for_extraction noextract
val get_data (#a:Type0) (c:cell a) : a

/// As a convention, we represent NULL as 0
noextract inline_for_extraction
let null : nat = 0
noextract inline_for_extraction
let null_ptr : US.t = 0sz

/// The toplevel specification of being a list
/// When [hd] is the head pointer of the list, the set of visited nodes
/// is initially empty, and the prev "pointer" should be "NULL"
val is_dlist (#a:Type0) (pred: a -> prop)  (hd:nat) (s:Seq.seq (cell a)) : prop

/// Offset [x] belongs to the list starting at [hd]
val mem (#a:Type0) (x:nat) (hd:nat) (s:Seq.seq (cell a)) : prop

/// An alternative specification for belonging to the list,
/// `ptrs_in` returns the set of elements in the list starting
/// at [hd]
val ptrs_in (#a:Type) (hd:nat) (s:Seq.seq (cell a)) : GTot (FS.set nat)

/// Set of all pointers contained in the three doubly linked lists
let ptrs_all (#a:Type) (hd1 hd2 hd3:nat) (s:Seq.seq (cell a)) =
  FS.union (ptrs_in hd1 s) (FS.union (ptrs_in hd2 s) (ptrs_in hd3 s))

/// Membership of element [x] in any of the dlist pointed to by [hd1], [hd2], or [hd3]
let mem_all (#a:Type0) (x:nat) (hd1 hd2 hd3:nat) (s:Seq.seq (cell a)) =
  FS.mem x (ptrs_all hd1 hd2 hd3 s)

/// Equivalence lemma between `mem` and membership in `ptrs_in`
val lemma_mem_ptrs_in (#a:Type)
  (hd: nat)
  (s: Seq.seq (cell a))
  (x: nat)
  : Lemma (mem x hd s <==> FS.mem x (ptrs_in hd s))

/// Disjointness between two lists, specified directly on the sets of pointers
/// to alleviate the need for recursive reasoning
val disjoint (#a:Type)
  (s: Seq.seq (cell a))
  (hd1 hd2: nat)
  : prop

/// Mutual exclusiveness for three dlists
let disjoint3 (#a:Type) (s:Seq.seq (cell a)) (hd1 hd2 hd3: nat) =
  disjoint s hd1 hd2 /\ disjoint s hd1 hd3 /\ disjoint s hd2 hd3

/// The array is partitioned exactly between the three lists
let partition (#a:Type) (s:Seq.seq (cell a)) (hd1 hd2 hd3: nat) =
  forall (i:nat{i < Seq.length s}). i == null \/ (FS.mem i (ptrs_all hd1 hd2 hd3 s))

(** Some helpers to use cells *)

val read_data (#a:Type) (c:cell a) : a

val write_data (#a:Type0) (c:cell a) (v:a) : cell a

(** Steel functions and vprops *)

/// The refinement predicate for varraylist, stating that the sequence contains
/// three mutually exclusive doubly linked lists
let varraylist_refine (#a:Type)
  (pred1 pred2 pred3: a -> prop)
  (hd1 hd2 hd3:nat)
  (s:Seq.seq (cell a)) : prop
  = is_dlist pred1 hd1 s /\ is_dlist pred2 hd2 s /\ is_dlist pred3 hd3 s /\ disjoint3 s hd1 hd2 hd3

/// The main vprop of this module.
/// We have access to an array, such that the array contains three mutually
/// exclusive doubly linked list, starting at offsets [hd1] [hd2] and [hd3]
/// respectively
[@@__steel_reduce__]
let varraylist (#a:Type) (pred1 pred2 pred3: a -> prop) (r:A.array (cell a)) (hd1 hd2 hd3:nat) : vprop
  = A.varray r `vrefine` (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3)

/// Create an arraylist with an empty sequence
val intro_arraylist_nil (#a:Type) (#opened:inames)
  (pred1 pred2 pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3:US.t) :
  SteelGhost unit opened
    (A.varray r)
    (fun _ -> varraylist pred1 pred2 pred3 r (US.v hd1) (US.v hd2) (US.v hd3))
    (requires fun _ ->
      A.length r == 0 /\
      hd1 == null_ptr /\
      hd2 == null_ptr /\
      hd3 == null_ptr)
    (ensures fun _ _ h1 ->
      h1 (varraylist pred1 pred2 pred3 r (US.v hd1) (US.v hd2) (US.v hd3)) `Seq.equal` Seq.empty
    )

/// If the head of one of the lists is not null, then it is in the list
val intro_head1_not_null_mem (#a:Type) (#opened:inames)
  (pred1 pred2 pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3:US.t) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 r (US.v hd1) (US.v hd2) (US.v hd3))
    (fun _ -> varraylist pred1 pred2 pred3 r (US.v hd1) (US.v hd2) (US.v hd3))
    (requires fun _ -> hd1 <> null_ptr)
    (ensures fun h0 _ h1 ->
      // Framing
      h0 (varraylist pred1 pred2 pred3 r (US.v hd1) (US.v hd2) (US.v hd3)) ==
      h1 (varraylist pred1 pred2 pred3 r (US.v hd1) (US.v hd2) (US.v hd3)) /\
      // Functional property
      mem (US.v hd1) (US.v hd1) (h1 (varraylist pred1 pred2 pred3 r (US.v hd1) (US.v hd2) (US.v hd3)))
    )

/// Reads at index [idx] in the array.
inline_for_extraction noextract
val read_in_place (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel a
          (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (requires fun _ -> True)
          (ensures fun h0 _ h1 ->
            h0 (varraylist pred1 pred2 pred3 r hd1 hd2 hd3) ==
            h1 (varraylist pred1 pred2 pred3 r hd1 hd2 hd3))

/// Updates the `data` field of the cell at index [idx] in the array [r] with [v]
/// We define three different functions, depending on which list the element
/// belongs to. In all three cases, we require [v] to satisfy the predicate
/// corresponding to a given list
inline_for_extraction noextract
val write_in_place1 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  (v:a)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (requires fun h -> pred1 v /\ mem (US.v idx) hd1 (h (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)))
          (ensures fun h0 _ h1 -> True) // TODO

inline_for_extraction noextract
val write_in_place2 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  (v:a)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (requires fun h -> pred2 v /\ mem (US.v idx) hd2 (h (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)))
          (ensures fun h0 _ h1 -> True) // TODO

inline_for_extraction noextract
val write_in_place3 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  (v:a)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (requires fun h -> pred3 v /\ mem (US.v idx) hd3 (h (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)))
          (ensures fun h0 _ h1 -> True) // TODO

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
inline_for_extraction noextract
val remove1 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1:US.t)
  (hd2 hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3)
          (fun hd' -> varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)
          (requires fun h -> mem (US.v idx) (US.v hd1) (h (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3)))
          (ensures fun h0 hd' h1 ->
            ptrs_in (US.v hd') (h1 (varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)) ==
            FS.remove (US.v idx) (ptrs_in (US.v hd1) (h0 (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3))) /\
            ptrs_in hd2 (h1 (varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)) ==
            ptrs_in hd2 (h0 (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3)) /\
            ptrs_in hd3 (h1 (varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)) ==
            ptrs_in hd3 (h0 (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3))
          )

/// Removes the element at offset [idx] from the dlist pointed to by [hd2]
inline_for_extraction noextract
val remove2 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1:Ghost.erased nat)
  (hd2:US.t)
  (hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3)
          (fun hd' -> varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)
          (requires fun h -> mem (US.v idx) (US.v hd2) (h (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3)))
          (ensures fun h0 hd' h1 ->
            ptrs_in (US.v hd') (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)) ==
            FS.remove (US.v idx) (ptrs_in (US.v hd2) (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3))) /\
            ptrs_in hd1 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)) ==
            ptrs_in hd1 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3)) /\
            ptrs_in hd3 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)) ==
            ptrs_in hd3 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3))
          )

/// Removes the element at offset [idx] from the dlist pointed to by [hd3]
inline_for_extraction noextract
val remove3 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2:Ghost.erased nat)
  (hd3:US.t)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3))
          (fun hd' -> varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd'))
          (requires fun h -> mem (US.v idx) (US.v hd3) (h (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3))))
          (ensures fun h0 hd' h1 ->
            ptrs_in (US.v hd') (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd'))) ==
            FS.remove (US.v idx) (ptrs_in (US.v hd3) (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3)))) /\
            ptrs_in hd1 (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd'))) ==
            ptrs_in hd1 (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3))) /\
            ptrs_in hd2 (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd'))) ==
            ptrs_in hd2 (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3)))
          )

/// Requires that the element at offset [idx] does not belong to any dlist.
/// If so, insert it at the head of list [hd1]
inline_for_extraction noextract
val insert1 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd2 hd3:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: a)
   : Steel unit
          (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r (US.v idx) hd2 hd3)
          (requires fun h -> pred1 v /\
            (~ (mem_all (US.v idx) (US.v hd) hd2 hd3 (h (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3)))))
          (ensures fun h0 hd' h1 ->
            ptrs_in (US.v idx) (h1 (varraylist pred1 pred2 pred3 r (US.v idx) hd2 hd3)) ==
            FS.insert (US.v idx) (ptrs_in (US.v hd) (h0 (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3))) /\
            ptrs_in hd2 (h1 (varraylist pred1 pred2 pred3 r (US.v idx) hd2 hd3)) ==
            ptrs_in hd2 (h0 (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3)) /\
            ptrs_in hd3 (h1 (varraylist pred1 pred2 pred3 r (US.v idx) hd2 hd3)) ==
            ptrs_in hd3 (h0 (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3))
          )


/// Requires that the element at offset [idx] does not belong to any dlist.
/// If so, insert it at the head of list [hd2]
inline_for_extraction noextract
val insert2 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd1 hd3:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: a)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)
          (requires fun h -> pred2 v /\
            (~ (mem_all (US.v idx) hd1 (US.v hd) hd3 (h (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)))))
          (ensures fun h0 hd' h1 ->
            ptrs_in (US.v idx) (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)) ==
            FS.insert (US.v idx) (ptrs_in (US.v hd) (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3))) /\
            ptrs_in hd1 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)) ==
            ptrs_in hd1 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)) /\
            ptrs_in hd3 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)) ==
            ptrs_in hd3 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3))
          )

/// Requires that the element at offset [idx] does not belong to any dlist.
/// If so, insert it at the head of list [hd3]
inline_for_extraction noextract
val insert3 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd1 hd2:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: a)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))
          (requires fun h -> pred3 v /\
            (~ (mem_all (US.v idx) hd1 hd2 (US.v hd) (h (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))))))
          (ensures fun h0 hd' h1 ->
            ptrs_in (US.v idx) (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))) ==
            FS.insert (US.v idx) (ptrs_in (US.v hd) (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd)))) /\
            ptrs_in hd1 (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))) ==
            ptrs_in hd1 (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))) /\
            ptrs_in hd2 (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))) ==
            ptrs_in hd2 (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd)))
          )
