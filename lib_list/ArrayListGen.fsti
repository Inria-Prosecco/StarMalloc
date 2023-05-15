module ArrayListGen

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef

module A = Steel.Array
module L = FStar.List.Tot
module U32 = FStar.UInt32
module US = FStar.SizeT
module FS = FStar.FiniteSet.Base
open FStar.FiniteSet.Ambient

open Prelude

(** A library for doubly linked lists, that are located in memory in a contiguous region (an array) *)

/// The type of cells for the doubly linked list. Compared to a standard doubly linked list,
/// the `prev` and `next` fields are not pointers, but offsets in the array containing the list.
/// To keep unsigned (positive) integers, we will represent NULL as 0, and not store anything
/// in the first element slot of the array
val cell (t:Type0) : Type0

inline_for_extraction noextract
val get_data (#a:Type0) (c:cell a) : a

/// As a convention, we represent NULL as the max length of the metadata array + 1,
/// i.e., metadata_max + 1.
/// The + 1 is needed to handle the case where the metadata array will be full,
/// and the metadata counter will be exactly metadata_max
noextract inline_for_extraction
let null : nat = Config.alg_null
noextract inline_for_extraction
let null_ptr : US.t = Config.alg_null_sizet

let null_ptr_check () =
  assert (US.v null_ptr == US.v Config.metadata_max + 1)

/// Erases the next and prev field to return a sequence of data
val dataify (#a:Type)
  (s: Seq.seq (cell a))
  : GTot (Seq.lseq a (Seq.length s))

/// Accessing index [i] of dataify is the same as calling `get_data` on
/// the underlying array
val lemma_dataify_index (#a:Type)
  (s:Seq.seq (cell a))
  (i:nat{i < Seq.length s})
  : Lemma (Seq.index (dataify s) i == get_data (Seq.index s i))

val lemma_dataify_slice (#a:Type)
  (s: Seq.seq (cell a))
  (n:nat{n <= Seq.length s})
  : Lemma (dataify (Seq.slice s 0 n) == Seq.slice (dataify s) 0 n)

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

/// Set of all pointers contained in the four doubly linked lists
let ptrs_all (#a:Type) (hd1 hd2 hd3 hd4:nat) (s:Seq.seq (cell a)) =
  FS.union
    (FS.union (ptrs_in hd1 s) (ptrs_in hd2 s))
    (FS.union (ptrs_in hd3 s) (ptrs_in hd4 s))

/// Membership of element [x] in any of the dlist pointed to by [hd1], [hd2], or [hd3]
let mem_all (#a:Type0) (x:nat) (hd1 hd2 hd3 hd4:nat) (s:Seq.seq (cell a)) =
  FS.mem x (ptrs_all hd1 hd2 hd3 hd4 s)

/// Equivalence lemma between `mem` and membership in `ptrs_in`
val lemma_mem_ptrs_in (#a:Type)
  (hd: nat)
  (s: Seq.seq (cell a))
  (x: nat)
  : Lemma (mem x hd s <==> FS.mem x (ptrs_in hd s))

/// If an element belongs to a list, then it satisfies the corresponding
/// list predicate
val lemma_mem_implies_pred (#a:Type)
  (pred: a -> prop)
  (hd:nat)
  (s: Seq.seq (cell a))
  (x:nat{x < Seq.length s})
  : Lemma
    (requires mem x hd s /\ is_dlist pred hd s)
    (ensures pred (get_data (Seq.index s x)))

/// Disjointness between two lists, specified directly on the sets of pointers
/// to alleviate the need for recursive reasoning
val disjoint (#a:Type)
  (s: Seq.seq (cell a))
  (hd1 hd2: nat)
  : prop

/// Mutual exclusiveness for four dlists
let disjoint4 (#a:Type) (s:Seq.seq (cell a)) (hd1 hd2 hd3 hd4: nat) =
  disjoint s hd1 hd2 /\
  disjoint s hd1 hd3 /\
  disjoint s hd1 hd4 /\
  disjoint s hd2 hd3 /\
  disjoint s hd2 hd4 /\
  disjoint s hd3 hd4

/// The array is partitioned exactly between the four lists
let partition (#a:Type) (s:Seq.seq (cell a)) (hd1 hd2 hd3 hd4: nat) =
  forall (i:nat{i < Seq.length s}). FS.mem i (ptrs_all hd1 hd2 hd3 hd4 s)

(** Some helpers to use cells *)

val read_data (#a:Type) (c:cell a) : a

val write_data (#a:Type0) (c:cell a) (v:a) : cell a

(** Steel functions and vprops *)

/// The refinement predicate for varraylist, stating that the sequence contains
/// four mutually exclusive doubly linked lists
let varraylist_refine (#a:Type)
  (pred1 pred2 pred3 pred4: a -> prop)
  (hd1 hd2 hd3 hd4:nat)
  (s:Seq.seq (cell a)) : prop
  =
  is_dlist pred1 hd1 s /\
  is_dlist pred2 hd2 s /\
  is_dlist pred3 hd3 s /\
  is_dlist pred4 hd4 s /\
  disjoint4 s hd1 hd2 hd3 hd4

/// The main vprop of this module.
/// We have access to an array, such that the array contains four mutually
/// exclusive doubly linked list, starting at offsets [hd1] [hd2] and [hd3]
/// respectively
[@@__steel_reduce__]
let varraylist (#a:Type) (pred1 pred2 pred3 pred4: a -> prop) (r:A.array (cell a)) (hd1 hd2 hd3 hd4:nat) : vprop
  = A.varray r `vrefine` (varraylist_refine pred1 pred2 pred3 pred4 hd1 hd2 hd3 hd4)

/// Create an arraylist with an empty sequence
val intro_arraylist_nil (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:US.t) :
  SteelGhost unit opened
    (A.varray r)
    (fun _ ->
      varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
    (requires fun _ ->
      A.length r == 0 /\
      hd1 == null_ptr /\
      hd2 == null_ptr /\
      hd3 == null_ptr /\
      hd4 == null_ptr)
    (ensures fun _ _ h1 ->
      h1 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
      `Seq.equal`
      Seq.empty
    )

/// If the head of one of the lists is not null, then it is in the list
val lemma_head_not_null_mem (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:US.t) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r
      (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
    (fun _ ->
      varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4)) in
      let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4)) in
      // Framing
      gs1 == gs0 /\
      // Functional property
      (hd1 = null_ptr \/ mem (US.v hd1) (US.v hd1) gs1) /\
      (hd2 = null_ptr \/ mem (US.v hd2) (US.v hd2) gs1) /\
      (hd3 = null_ptr \/ mem (US.v hd3) (US.v hd3) gs1) /\
      (hd4 = null_ptr \/ mem (US.v hd4) (US.v hd4) gs1)
    )

/// If the head of one of the lists is not null, then it is smaller than the length
/// of the underlying array
val lemma_head1_in_bounds (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1: US.t)
  (hd2 hd3 hd4: Ghost.erased nat) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)
    (fun _ -> varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) hd2 hd3 hd4) in
      let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) hd2 hd3 hd4) in
      // Framing
      gs1 == gs0 /\
      // Functional property
      (hd1 == null_ptr \/ US.v hd1 < A.length r)
    )

/// If the head of one of the lists is not null, then it is smaller than the length
/// of the underlying array
val lemma_head2_in_bounds (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1: Ghost.erased nat)
  (hd2: US.t)
  (hd3 hd4: Ghost.erased nat) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd2) hd3 hd4)
    (fun _ -> varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd2) hd3 hd4)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        hd1 (US.v hd2) hd3 hd4) in
      let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r
        hd1 (US.v hd2) hd3 hd4) in
      // Framing
      gs1 == gs0 /\
      // Functional property
      (hd2 == null_ptr \/ US.v hd2 < A.length r)
    )

/// If the head of one of the lists is not null, then it satisfies the corresponding predicate
val lemma_head1_implies_pred1 (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1:US.t{US.v hd1 < A.length r})
  (hd2 hd3 hd4:US.t) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
    (fun _ -> varraylist pred1 pred2 pred3 pred4 r (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
    (requires fun h -> hd1 <> null_ptr)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4)) in
      let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4)) in
      // Framing
      gs1 == gs0 /\
      // Functional property
      pred1 (get_data (Seq.index gs1 (US.v hd1)))
    )

/// If the head of one of the lists is not null, then it satisfies the corresponding predicate
val lemma_head2_implies_pred2 (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1:US.t)
  (hd2:US.t{US.v hd2 < A.length r})
  (hd3 hd4:US.t) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
    (fun _ -> varraylist pred1 pred2 pred3 pred4 r (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4))
    (requires fun h -> hd2 <> null_ptr)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4)) in
      let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r
        (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4)) in
      // Framing
      gs1 == gs0 /\
      // Functional property
      pred2 (get_data (Seq.index gs1 (US.v hd2)))
    )

/// The order of the four lists does not matter, we can permute them in the varraylist predicate.
/// We permute here the first and second lists
val permute12 (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:nat) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
    (fun _ -> varraylist pred2 pred1 pred3 pred4 r hd2 hd1 hd3 hd4)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        hd1 hd2 hd3 hd4) in
      let gs1 = h1 (varraylist pred2 pred1 pred3 pred4 r
        hd2 hd1 hd3 hd4) in
      // Framing
      gs1 == gs0
    )

/// The order of the four lists does not matter, we can permute them in the varraylist predicate
/// We permute here the first and third lists
val permute13 (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:nat) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
    (fun _ -> varraylist pred3 pred2 pred1 pred4 r hd3 hd2 hd1 hd4)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        hd1 hd2 hd3 hd4) in
      let gs1 = h1 (varraylist pred3 pred2 pred1 pred4 r
        hd3 hd2 hd1 hd4) in
      // Framing
      gs1 == gs0
    )

/// The order of the four lists does not matter, we can permute them in the varraylist predicate
/// We permute here the first and third lists
val permute14 (#a:Type) (#opened:inames)
  (pred1 pred2 pred3 pred4: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:nat) :
  SteelGhost unit opened
    (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
    (fun _ -> varraylist pred4 pred2 pred3 pred1 r hd4 hd2 hd3 hd1)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
        hd1 hd2 hd3 hd4) in
      let gs1 = h1 (varraylist pred4 pred2 pred3 pred1 r
        hd4 hd2 hd3 hd1) in
      // Framing
      gs1 == gs0
    )

/// Reads at index [idx] in the array.
inline_for_extraction noextract
val read_in_place (#a:Type)
  (#pred1 #pred2 #pred3 #pred4: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel a
  (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
  (requires fun _ -> True)
  (ensures fun h0 res h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r
      hd1 hd2 hd3 hd4) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r
      hd1 hd2 hd3 hd4) in
    // Framing
    gs1 == gs0 /\
    // Functional correctness
    res == get_data (Seq.index gs0 (US.v idx))
  )

//TODO: to be removed
/// Updates the `data` field of the cell at index [idx] in the array [r] with [v]
/// We define four different functions, depending on which list the element
/// belongs to. In all four cases, we require [v] to satisfy the predicate
/// corresponding to a given list
/// Note, we only expose the version for [hd1] to avoid duplication,
/// but we can easily obtain versions for [hd2] and [hd3] using the
/// permutations above. See instantiations in `src/ArrayList.fst`
inline_for_extraction noextract
val write_in_place (#a:Type)
  (#pred1 #pred2 #pred3 #pred4: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  (v:a)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4) in
    pred1 v /\ mem (US.v idx) hd1 gs0
  )
  (ensures fun h0 _ h1 -> True)

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
/// Note, we only expose the version for [hd1] to avoid duplication,
/// but we can easily obtain versions for [hd2] and [hd3] using the
/// permutations above. See instantiations in `src/ArrayList.fst`
inline_for_extraction noextract
val remove (#a:Type)
  (#pred1 #pred2 #pred3 #pred4: a -> prop)
  (r:A.array (cell a))
  (hd1:US.t)
  (hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel US.t
  (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)
  (fun hd' -> varraylist pred1 pred2 pred3 pred4 r (US.v hd') hd2 hd3 hd4)
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4) in
    mem (US.v idx) (US.v hd1) gs0
  )
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r (US.v hd') hd2 hd3 hd4) in
    ptrs_in (US.v hd') gs1 ==
    FS.remove (US.v idx) (ptrs_in (US.v hd1) gs0) /\
    ptrs_in hd2 gs1 == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs1 == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs1 == ptrs_in hd4 gs0 /\
    (~ (mem_all (US.v idx) (US.v hd') hd2 hd3 hd4 gs1)) /\
    dataify gs1 == dataify gs0
  )

/// Requires that the element at offset [idx] does not belong to any dlist.
/// If so, insert it at the head of list [hd1].
/// Note, we only expose the version for [hd1] to avoid duplication,
/// but we can easily obtain versions for [hd2] and [hd3] using the
/// permutations above. See instantiations in `src/ArrayList.fst`
inline_for_extraction noextract
val insert (#a:Type)
  (#pred1 #pred2 #pred3 #pred4: a -> prop)
  (r:A.array (cell a))
  (hd1:US.t)
  (hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: a)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 r (US.v idx) hd2 hd3 hd4)
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4) in
    pred1 v /\ (~ (mem_all (US.v idx) (US.v hd1) hd2 hd3 hd4 gs0))
  )
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r (US.v idx) hd2 hd3 hd4) in
    ptrs_in (US.v idx) gs1 ==
    FS.insert (US.v idx) (ptrs_in (US.v hd1) gs0) /\
    ptrs_in hd2 gs1 == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs1 == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs1 == ptrs_in hd4 gs0 /\
    dataify gs1 == Seq.upd (dataify gs0) (US.v idx) v
  )

val extend_aux (#a:Type) (#opened:_)
  (#pred1 #pred2 #pred3 #pred4: a -> prop)
  (n: US.t)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4:Ghost.erased nat)
  (k:US.t{US.v k + US.v n <= A.length r /\ US.fits (US.v k + US.v n)})
  (v:a)
  : SteelGhost unit opened
  (
    varraylist pred1 pred2 pred3 pred4 (A.split_l r k) hd1 hd2 hd3 hd4 `star`
    A.varray (A.split_l (A.split_r r k) n)
  )
  (fun _ -> varraylist pred1 pred2 pred3 pred4
    (A.split_l r (k `US.add` n))
    hd1 hd2 hd3 hd4)
  (requires fun _ -> k <> null_ptr /\ pred1 v)
  (ensures fun h0 _ h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 (A.split_l r k) hd1 hd2 hd3 hd4) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 (A.split_l r (k `US.add` n)) hd1 hd2 hd3 hd4) in
    ptrs_in hd1 gs1 == ptrs_in hd1 gs0 /\
    ptrs_in hd2 gs1 == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs1 == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs1 == ptrs_in hd4 gs0 /\
    (forall (j:nat{0 <= j /\ j < US.v n}).
      ~ (mem_all (US.v k + j) hd1 hd2 hd3 hd4 gs1)
    ) /\
    Seq.slice gs1 0 (US.v k)
    ==
    gs0
  )

module G = FStar.Ghost

val set (bound1 bound2: nat)
  : Pure (G.erased (FS.set nat))
  (requires bound1 <= bound2)
  (ensures fun r ->
    forall (k:nat{bound1 <= k /\ k < bound2}). FS.mem k r
  )

open Config

val extend_insert (#a: Type)
  (#pred1 #pred2 #pred3 #pred4: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4: US.t)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1) /\ k <> null_ptr})
  (v1: a)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4
    (A.split_l r (k `US.add` n1))
    (US.v k) (US.v hd2) (US.v hd3) (US.v hd4))
  (fun _ -> varraylist pred1 pred2 pred3 pred4
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4))
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4
      (A.split_l r (k `US.add` n1))
      (US.v k) (US.v hd2) (US.v hd3) (US.v hd4)) in
    pred1 v1 /\
    A.length r <= US.v metadata_max /\
    (forall (j:nat{1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) gs0))
  )
  (ensures fun h0 _ h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4
      (A.split_l r (k `US.add` n1))
      (US.v k) (US.v hd2) (US.v hd3) (US.v hd4)) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4)) in
    ptrs_in (US.v k + US.v n2) gs1
    == FS.union
      (set (US.v k) (US.v k + US.v n2 + 1))
      (ptrs_in (US.v k) gs0) /\
    ptrs_in (US.v hd2) gs1 == ptrs_in (US.v hd2) gs0 /\
    ptrs_in (US.v hd3) gs1 == ptrs_in (US.v hd3) gs0 /\
    ptrs_in (US.v hd4) gs1 == ptrs_in (US.v hd4) gs0 /\
    Seq.slice (dataify gs1) 0 (US.v k + US.v n2 + 1)
    == Seq.append
      (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v n2) v1) /\
    (forall (j:nat{US.v n2 + 1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) gs1)) /\
    True
  )
