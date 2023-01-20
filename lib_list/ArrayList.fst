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

noeq
type cell (a:Type0) = {
  next: US.t;
  data: a;
}

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

let is_list (#a:Type0) (hd:nat) (s:Seq.seq (cell a)) : prop =
  is_list' hd s FS.emptyset

let read_data (#a:Type) (c:cell a) : a = c.data

let write_data (#a:Type0) (c:cell a) (v:a) : cell a =
  {c with data = v}

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

let varraylist (#a:Type) (r:A.array (cell a)) (hd:nat{hd < A.length r}) : vprop
  = A.varray r `vrefine` (is_list hd)



// read_in_place
// write_in_place
// remove
// insert
