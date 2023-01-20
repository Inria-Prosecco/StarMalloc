module ArrayList

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef

module A = Steel.Array
module L = FStar.List.Tot
module US = FStar.SizeT
module FS = FStar.FiniteSet.Base
open FStar.FiniteSet.Ambient

(** A library for linked lists, that are located in memory in a contiguous region (an array) *)

/// The type of cells for the linked list. Compared to a standard linked list, the next field is
/// not a pointer, but an offset in the array containing the list.
/// To keep unsigned (positive) integers, we will represent NULL as the length of the bsae array
noeq
type cell (a:Type0) = {
  next: US.t;
  data: a;
}


/// The core logical predicate: For a sequence of cells [s], corresponding to the contents of an array,
/// there is a linked list starting at s.[idx].
/// The [visited] argument is needed to ensure termination, it corresponds to the set of cells
/// previously visited. Acyclicity is specified by guaranteeing that we do not visit a cell twice
/// Note, as a convention, we consider that length of the sequence corresponds to the NULL case
let rec is_list' (#a:Type0) (hd:nat) (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Tot prop (decreases (Seq.length s - FS.cardinality visited)) =
  // Null case.
  if hd = Seq.length s then True
  else
    // Forbid cycles, ensure well-formedness of the "pointers"
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd > Seq.length s then False
    else
      let next = US.v (Seq.index s hd).next in
      is_list' next s (FS.insert hd visited)

/// The toplevel specification of being a list
/// When [hd] is the head pointer of the list, the set of visited nodes
/// is initially empty.
let is_list (#a:Type0) (hd:nat) (s:Seq.seq (cell a)) : prop =
  is_list' hd s FS.emptyset

let rec mem' (#a:Type0) (x:nat) (hd:nat) (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Tot prop (decreases (Seq.length s - FS.cardinality visited)) =
  if x >= Seq.length s then False
  else
    if x = hd then True
    else
      // Ill-formed list
      if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then False
      else
        let next = US.v (Seq.index s hd).next in
        mem' x next s (FS.insert hd visited)

/// Offset [x] belongs to the list starting at [hd]
let mem (#a:Type0) (x:nat) (hd:nat) (s:Seq.seq (cell a)) : prop =
  mem' x hd s FS.emptyset

(** Some helpers to use cells *)

let read_data (#a:Type) (c:cell a) : a = c.data

let write_data (#a:Type0) (c:cell a) (v:a) : cell a =
  {c with data = v}

/// Framing lemma: Only changing the `data` field of a cell
/// does not change the structure of the linked list
let rec lemma_write_data_frame' (#a:Type0)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  (v:a)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Lemma
      (requires is_list' hd s visited)
      (ensures is_list' hd (Seq.upd s idx (write_data (Seq.index s idx) v)) visited)
      (decreases (Seq.length s - FS.cardinality visited))
  = let s' = Seq.upd s idx (write_data (Seq.index s idx) v) in
    if hd = Seq.length s then ()
    else
      if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd > Seq.length s then ()
      else
        let next1 = US.v (Seq.index s hd).next in
        let next2 = US.v (Seq.index s' hd).next in
        assert (next1 == next2);
        lemma_write_data_frame' next1 s idx v (FS.insert hd visited)

let lemma_write_data_frame (#a:Type0)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  (v:a)
  : Lemma
      (requires is_list hd s)
      (ensures is_list hd (Seq.upd s idx (write_data (Seq.index s idx) v)))
  = lemma_write_data_frame' hd s idx v FS.emptyset

/// The main vprop of this module.
/// We have access to an array, such that the array contains a linked list
/// when starting at offset [hd]
let varraylist (#a:Type) (r:A.array (cell a)) (hd:nat{hd < A.length r}) : vprop
  = A.varray r `vrefine` (is_list hd)

/// Reads at index [idx] in the array.
/// TODO: The hd pointer should be ghost
val read_in_place (#a:Type) (r:A.array (cell a)) (hd:nat{hd < A.length r}) (idx:US.t{US.v idx < A.length r})
  : Steel a
          (varraylist r hd)
          (fun _ -> varraylist r hd)
          (requires fun _ -> True)
          (ensures fun h0 _ h1 -> h0 (varraylist r hd) == h1 (varraylist r hd))

let read_in_place #a r hd idx =
  elim_vrefine (A.varray r) (is_list hd);
  let res = A.index r idx in
  intro_vrefine (A.varray r) (is_list hd);
  return res.data

/// Updates the `data` field of the cell at index [idx] in the array [r] with [v]
val write_in_place (#a:Type) (r:A.array (cell a)) (hd:nat{hd < A.length r}) (idx:US.t{US.v idx < A.length r}) (v:a)
   : Steel unit
          (varraylist r hd)
          (fun _ -> varraylist r hd)
          (requires fun _ -> True)
          (ensures fun h0 _ h1 -> True) // TODO

let write_in_place #a r hd idx v =
  elim_vrefine (A.varray r) (is_list hd);
  let c = A.index r idx in
  (**) let gs = gget (A.varray r) in
  A.upd r idx (write_data c v);
  lemma_write_data_frame hd gs (US.v idx) v;
  intro_vrefine (A.varray r) (is_list hd)

// remove
// insert
