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
noeq
type cell (a:Type0) = {
  prev: US.t;
  next: US.t;
  data: a;
}

let get_data c = c.data

let dataify (#a:Type)
  (s: Seq.seq (cell a))
  : GTot (Seq.lseq a (Seq.length s))
  =
  Seq.map_seq_len get_data s;
  Seq.map_seq get_data s

/// The core logical predicate: For a sequence of cells [s], corresponding to the contents of an array,
/// there is a doubly linked list starting at s.[idx].
/// The [visited] argument is needed to ensure termination, it corresponds to the set of cells
/// previously visited. Acyclicity is specified by guaranteeing that we do not visit a cell twice.
/// [prev] corresponds to the index of the previous cell.
/// The list is parametric in a predicate [pred], operating on the data, that all elements
/// of the list must satisfy
/// Note, as a convention, we consider that NULL corresponds to 0, and do not store anything there
let rec is_dlist' (#a:Type0) (pred: a -> prop) (hd:nat) (s:Seq.seq (cell a)) (prev:nat)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Tot prop (decreases (Seq.length s - FS.cardinality visited)) =
  // Null case.
  if hd = null then True
  else
    // Forbid cycles, ensure well-formedness of the "pointers"
    if FS.cardinality visited = Seq.length s ||
       FS.mem hd visited ||
       // If the prev pointer is not null, it should be in the visited set
       not (prev = null || FS.mem prev visited) ||
       hd >= Seq.length s then False
    else
      let cur = Seq.index s hd in
      let next = US.v cur.next in
      // The tail of the list is a doubly linked list
      is_dlist' pred next s hd (FS.insert hd visited) /\
      // The previous field correctly points to the previous element
      US.v cur.prev == prev /\
      // The data of the list satisfies the predicate [pred]
      pred cur.data

/// The toplevel specification of being a list
/// When [hd] is the head pointer of the list, the set of visited nodes
/// is initially empty, and the prev "pointer" should be "NULL"
let is_dlist (#a:Type0) (pred: a -> prop)  (hd:nat) (s:Seq.seq (cell a)) : prop =
  is_dlist' pred hd s null FS.emptyset

let rec mem' (#a:Type0) (x:nat) (hd:nat) (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Tot prop (decreases (Seq.length s - FS.cardinality visited)) =
  if x = null || x >= Seq.length s || hd = null then False
  else
    // Ill-formed list
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then False
    else
      if x = hd then True
      else
        let next = US.v (Seq.index s hd).next in
        mem' x next s (FS.insert hd visited)

/// Offset [x] belongs to the list starting at [hd]
let mem (#a:Type0) (x:nat) (hd:nat) (s:Seq.seq (cell a)) : prop =
  mem' x hd s FS.emptyset

/// An alternative specification for belonging to the list,
/// `ptrs_in` returns the set of elements in the list starting
/// at [hd]
let rec ptrs_in' (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : GTot (FS.set nat)
        (decreases (Seq.length s - FS.cardinality visited)) =
  if hd = null then FS.emptyset
  else
    // Ill-formed list
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then
      FS.emptyset
    else
      let next = US.v (Seq.index s hd).next in
      FS.insert hd (ptrs_in' next s (FS.insert hd visited))

let ptrs_in (#a:Type) (hd:nat) (s:Seq.seq (cell a)) = ptrs_in' hd s FS.emptyset

/// Equivalence lemma between `mem` and membership in `ptrs_in`
let rec lemma_mem_ptrs_in' (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  (x:nat)
  : Lemma
    (ensures mem' x hd s visited <==> FS.mem x (ptrs_in' hd s visited))
    (decreases (Seq.length s - FS.cardinality visited))
  = if hd = null then ()
    else
      if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then
        ()
      else
        let next = US.v (Seq.index s hd).next in
        lemma_mem_ptrs_in' next s (FS.insert hd visited) x

let lemma_mem_ptrs_in (#a:Type)
  (hd: nat)
  (s: Seq.seq (cell a))
  (x: nat)
  : Lemma (mem x hd s <==> FS.mem x (ptrs_in hd s))
  = lemma_mem_ptrs_in' hd s FS.emptyset x

/// Disjointness between two lists, specified directly on the sets of pointers
/// to alleviate the need for recursive reasoning
let disjoint' (#a:Type)
  (s: Seq.seq (cell a))
  (hd1 hd2:nat)
  (visited1: FS.set nat{FS.cardinality visited1 <= Seq.length s})
  (visited2: FS.set nat{FS.cardinality visited2 <= Seq.length s})
  = ptrs_in' hd1 s visited1 `FS.disjoint` ptrs_in' hd2 s visited2

let disjoint (#a:Type)
  (s: Seq.seq (cell a))
  (hd1 hd2: nat)
  = disjoint' s hd1 hd2 FS.emptyset FS.emptyset /\ True

(** Some helpers to use cells *)

let read_data (#a:Type) (c:cell a) : a = c.data

let write_data (#a:Type0) (c:cell a) (v:a) : cell a =
  {c with data = v}

let next_ptr (#a:Type)
  (pred:a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev:nat)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})

  : Ghost nat
          (requires is_dlist' pred hd s prev visited /\ hd <> null)
          (ensures fun _ -> True)
  = US.v (Seq.index s hd).next

(** Lemmas about the dlist predicate *)

/// Framing lemma: Only changing the `data` field of a cell
/// does not change the structure of the doubly linked list,
/// as long as we store an element satisfying [pred]
let rec lemma_write_data_frame' (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev:nat)
  (idx:nat{idx < Seq.length s})
  (v:a)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Lemma
      (requires is_dlist' pred hd s prev visited /\ pred v)
      (ensures (
        let s' = Seq.upd s idx (write_data (Seq.index s idx) v) in
        is_dlist' pred hd s' prev visited /\
        ptrs_in' hd s visited == ptrs_in' hd s' visited)
      )
      (decreases (Seq.length s - FS.cardinality visited))
  = let s' = Seq.upd s idx (write_data (Seq.index s idx) v) in
    if hd = null then ()
    else
      if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd > Seq.length s then ()
      else
        let next1 = US.v (Seq.index s hd).next in
        let next2 = US.v (Seq.index s' hd).next in
        assert (next1 == next2);
        lemma_write_data_frame' pred next1 s hd idx v (FS.insert hd visited)

val lemma_write_data_frame (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  (v:a)
  : Lemma
      (requires is_dlist pred hd s /\ pred v)
      (ensures (
        let s' = Seq.upd s idx (write_data (Seq.index s idx) v) in
        is_dlist pred hd s' /\
        ptrs_in hd s == ptrs_in hd s'))

let lemma_write_data_frame #a pred hd s idx v =
  lemma_write_data_frame' pred hd s null idx v FS.emptyset

let null_or_valid (#a:Type) (ptr:nat) (s:Seq.seq (cell a)) = ptr = null \/ ptr < Seq.length s

val lemma_mem_valid_or_null_next_prev' (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev: nat)
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (idx:nat)
  : Lemma
      (requires
        is_dlist' pred hd s prev visited /\
        mem' idx hd s visited /\
        null_or_valid prev s /\
        not (FS.mem idx visited))
      (ensures
        (let cell = Seq.index s idx in
        null_or_valid (US.v cell.next) s /\
        null_or_valid (US.v cell.prev) s /\
        (US.v cell.next == null \/ mem' (US.v cell.next) hd s visited))
      )
      (decreases (Seq.length s - FS.cardinality visited))

let rec lemma_mem_valid_or_null_next_prev' #a pred hd s prev visited idx
  =
  assert (not (idx = null || idx >= Seq.length s));
  let cur = Seq.index s hd in
  let next = US.v cur.next in
  if hd = idx then () else
  if hd = null then begin
    assert (idx <> null);
    assert (mem' idx null s visited);
    //mem_null #a idx s visited;
    assert (~ (mem' idx null s visited))
  end else begin
    assert (not (FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s));
    assert (is_dlist' pred next s hd (FS.insert hd visited));
    assert (mem' idx next s (FS.insert hd visited));
    lemma_mem_valid_or_null_next_prev' pred next s hd (FS.insert hd visited) idx
  end

val lemma_mem_valid_or_null_next_prev (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat)
  : Lemma
      (requires is_dlist pred hd s /\ mem idx hd s)
      (ensures
        (let cell = Seq.index s idx in
        null_or_valid (US.v cell.prev) s /\ null_or_valid (US.v cell.next) s)
      )

let lemma_mem_valid_or_null_next_prev #a pred hd s idx =
  lemma_mem_valid_or_null_next_prev' pred hd s null FS.emptyset idx

/// If idx belongs to the dlist, then either it is the head of the dlist
/// or its prev pointer does not belong to the visited set
val lemma_dlist_head_or_prev_not_visited (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev: nat)
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (idx:nat)
  : Lemma
      (requires
        is_dlist' pred hd s prev visited /\
        mem' idx hd s visited /\
        null_or_valid prev s /\
        not (FS.mem idx visited))
      (ensures
        (let cell = Seq.index s idx in
         idx == hd \/
         (mem' (US.v cell.prev) hd s visited /\ (~ (FS.mem (US.v cell.prev) visited))))
      )
      (decreases (Seq.length s - FS.cardinality visited))

let rec lemma_dlist_head_or_prev_not_visited pred hd s prev visited idx =
  if idx = hd || hd = null then ()
  else
    let cur = Seq.index s hd in
    let next = US.v cur.next in
    lemma_dlist_head_or_prev_not_visited pred next s hd (FS.insert hd visited) idx

(** Functional specifications of the more complicated functions *)

/// A ghost specification of the insertion function for doubly linked lists
let insert_spec (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < Seq.length s})
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (v:a)
  : Ghost (Seq.seq (cell a))
         (requires is_dlist pred (US.v hd) s /\ ~ (mem (US.v idx) (US.v hd) s))
         (ensures fun _ -> True)
  = let cell = {data = v; prev = null_ptr; next = hd} in
    let s = Seq.upd s (US.v idx) cell in
    if hd <> null_ptr then
      let cell = Seq.index s (US.v hd) in
      let cell = {cell with prev = idx} in
      Seq.upd s (US.v hd) cell
    else s


/// A ghost specification of the remove function for doubly linked lists
let remove_spec (#a:Type)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev:nat)
  (idx:nat{idx < Seq.length s})
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Ghost (Seq.seq (cell a))
         (requires
           is_dlist' pred hd s prev visited /\
           mem' idx hd s visited /\
           null_or_valid prev s /\
           not (FS.mem idx visited))
         (ensures fun s' -> Seq.length s == Seq.length s')
         =
  let cell = Seq.index s idx in
  lemma_mem_valid_or_null_next_prev' pred hd s prev visited idx;
  let s =
    if cell.next <> null_ptr then
      // Next is not null, we need to update it
      let next = Seq.index s (US.v cell.next) in
      let next = {next with prev = cell.prev} in
      Seq.upd s (US.v cell.next) next
    else s
  in

  let s =
    if cell.prev <> null_ptr then
      let prev = Seq.index s (US.v cell.prev) in
      let prev = {prev with next = cell.next} in
      Seq.upd s (US.v cell.prev) prev
    else s
  in s


(** Functional correctness lemmas for insert and remove *)

let rec lemma_dlist_upd' (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (prev: nat)
  (other:nat{other <> null /\ other < Seq.length s})
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (v: cell a)
  : Lemma
  (requires
    is_dlist' pred hd s prev visited /\
    ~ (mem' idx hd s visited) /\
    ~ (mem' other hd s visited))
  (ensures (
    let s' = Seq.upd s idx v in
    is_dlist' pred hd s' prev visited /\
    ~ (mem' idx hd s' visited) /\
    ~ (mem' other hd s' visited))
    )
  (decreases (Seq.length s - FS.cardinality visited))
  =
  let s' = Seq.upd s idx v in
  if hd = null
  then
    ()
  else begin
    let cur = Seq.index s hd in
    let next = cur.next in
    assert (is_dlist' pred (US.v next) s hd (FS.insert hd visited));
    assert (~ (mem' idx hd s (FS.insert hd visited)));
    lemma_dlist_upd' pred s (US.v next) idx hd other (FS.insert hd visited) v
  end

let lemma_dlist_upd (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (other:nat{other <> null /\ other < Seq.length s})
  (v: cell a)
  : Lemma
  (requires
    is_dlist pred hd s /\
    ~ (mem idx hd s) /\
    ~ (mem other hd s)
    )
  (ensures (
    let s' = Seq.upd s idx v in
    is_dlist pred hd s' /\
    ~ (mem idx hd s') /\
    ~ (mem other hd s')
    ))
  = lemma_dlist_upd' pred s hd idx null other FS.emptyset v

/// Framing lemma about dlists: Updating any element outside the dlist
/// does not change any of the characteristics of the dlist
let rec lemma_dlist_frame' (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (prev: nat)
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (v: cell a)
  : Lemma
  (requires
    is_dlist' pred hd s prev visited /\
    ~ (mem' idx hd s visited))
  (ensures (
    let s' = Seq.upd s idx v in
    is_dlist' pred hd s' prev visited /\
    ptrs_in' hd s visited `FS.equal` ptrs_in' hd s' visited)
    )
  (decreases (Seq.length s - FS.cardinality visited))
  = let s' = Seq.upd s idx v in
    if hd = null then ()
    else begin
      let cur = Seq.index s hd in
      let next = cur.next in
      lemma_dlist_frame' pred s (US.v next) idx hd (FS.insert hd visited) v
    end

let lemma_dlist_frame (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (v:cell a)
  : Lemma
  (requires
    is_dlist pred hd s /\
    ~ (mem idx hd s)
  )
  (ensures (
    let s' = Seq.upd s idx v in
    is_dlist pred hd s' /\
    ptrs_in hd s == ptrs_in hd s'
  ))
  = lemma_dlist_frame' pred s hd idx null FS.emptyset v

/// If we have a finiteset of elements smaller than a given n,
/// and one element is not in the set, then the cardinality is not n
let lemma_finiteset_full_n (n:nat) (i:nat{i < n}) (s:FS.set nat)
  : Lemma
    (requires
      (forall (i:nat). FS.mem i s ==> i < n) /\
      ~ (FS.mem i s)
    )
    (ensures FS.cardinality s < n)
 = let rec aux (k:nat) : Pure (FS.set nat)
     (requires True)
     (ensures fun s ->
       FS.cardinality s == k /\
       (forall i. FS.mem i s <==> i < k))
   = if k = 0 then FS.emptyset else FS.singleton (k-1) `FS.union` aux (k-1)
   in
   let s_full = aux n in
   assert (FS.(
     cardinality (union s s_full) ==
     cardinality (difference s s_full) + cardinality (difference s_full s) + cardinality (intersection s s_full)))

let rec lemma_dlist_insert_visited (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (prev: nat)
  (visited: FS.set nat{FS.cardinality visited < Seq.length s})
  : Lemma
  (requires
    (forall i. FS.mem i visited ==> i < Seq.length s) /\
    is_dlist' pred hd s prev visited /\
    ~ (mem' idx hd s visited))
  (ensures
    is_dlist' pred hd s prev (FS.insert idx visited) /\
    ptrs_in' hd s visited == ptrs_in' hd s (FS.insert idx visited))
  (decreases (Seq.length s - FS.cardinality visited))
  =
  if hd = null
  then ()
  else begin
    let cur = Seq.index s hd in
    let next = cur.next in
    assert (is_dlist' pred (US.v next) s hd (FS.insert hd visited));
    assert (~ (mem' idx hd s (FS.insert hd visited)));

    if US.v next = null then (
      lemma_finiteset_full_n (Seq.length s) hd (FS.insert idx visited)
    )
    else begin
      assert (FS.cardinality (FS.insert hd visited) < Seq.length s);
      lemma_dlist_insert_visited pred s (US.v next) idx hd (FS.insert hd visited);
      // Need to explicitly introduce Set extensionality
      assert (
        FS.insert hd (FS.insert idx visited)
        `FS.equal`
        FS.insert idx (FS.insert hd visited)
      )
    end
  end

let rec lemma_dlist_remove_visited (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (prev: nat{prev <> idx})
  (visited: FS.set nat{FS.cardinality visited < Seq.length s})
  : Lemma
  (requires
    (forall i. FS.mem i visited ==> i < Seq.length s) /\
    is_dlist' pred hd s prev (FS.insert idx visited) /\
    ~ (mem' idx hd s (FS.insert idx visited)))
  (ensures
    is_dlist' pred hd s prev visited /\
    ptrs_in' hd s visited == ptrs_in' hd s (FS.insert idx visited))
  (decreases (Seq.length s - FS.cardinality visited))
  = if hd = null then ()
    else begin
      let cur = Seq.index s hd in
      let next = cur.next in
      if US.v next = null then (
        lemma_finiteset_full_n (Seq.length s) hd (FS.insert idx visited)
      )
      else begin
        assert (
          FS.insert idx (FS.insert hd  visited)
            `FS.equal`
          FS.insert hd (FS.insert idx visited)
        );
        lemma_dlist_remove_visited pred s (US.v next) idx hd (FS.insert hd visited)
      end
    end

/// If an element belongs to the visited set, then it
/// does not belong to the dlist
let rec lemma_mem_not_in_visited (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat)
  (prev:nat)
  (visited:FS.set nat{FS.cardinality visited <= Seq.length s})
  (ptr:nat)
  : Lemma
  (requires
    is_dlist' pred hd s prev visited /\
    FS.mem ptr visited
  )
  (ensures
    ~ (mem' ptr hd s visited))
  (decreases (Seq.length s - FS.cardinality visited))
  = if hd = null then ()
    else
      let cur = Seq.index s hd in
      let next = cur.next in
      lemma_mem_not_in_visited pred s (US.v next) hd (FS.insert hd visited) ptr

let lemma_dlist_mem_uniq (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat{hd <> null \/ hd < Seq.length s})
  (prev: nat)
  (visited: FS.set nat{FS.cardinality visited < Seq.length s})
  : Lemma
  (requires
    is_dlist' pred hd s prev visited
  )
  (ensures (
    let cur = Seq.index s hd in
    let next = cur.next in
    ~ (mem' hd (US.v next) s (FS.insert hd visited))
  ))
  =
  if hd = null then ()
  else
    let cur = Seq.index s hd in
    let next = cur.next in
    assert (not (FS.mem hd visited));
    assert (is_dlist' pred (US.v next) s hd (FS.insert hd visited));
    lemma_mem_not_in_visited pred s (US.v next) hd (FS.insert hd visited) hd

/// If a dlist is well-formed, the prev element does not belong to
/// the list
let lemma_dlist_prev_not_mem (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:nat)
  (prev:nat)
  (visited:FS.set nat{FS.cardinality visited <= Seq.length s})
  : Lemma
  (requires
    is_dlist' pred hd s prev visited
  )
  (ensures
    ~ (mem' prev hd s visited))
  (decreases (Seq.length s - FS.cardinality visited))
  = if hd = null || prev = null then ()
    else lemma_mem_not_in_visited pred s hd prev visited prev

/// Functional correctness of the insert_spec function:
/// The resulting list is still a doubly linked list, and it contains
/// the newly added element in addition to all the previous ones
let lemma_insert_spec (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < Seq.length s})
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (v:a)
  : Lemma (requires pred v /\ is_dlist pred (US.v hd) s /\ (~ (mem (US.v idx) (US.v hd) s)))
          (ensures (
            let s' = insert_spec pred s hd idx v in
            is_dlist pred (US.v idx) s' /\
            ptrs_in (US.v idx) s' `FS.equal` FS.insert (US.v idx) (ptrs_in (US.v hd) s))
          )
  =
  assert (is_dlist' pred (US.v hd) s null FS.emptyset);
  let cell = {data = v; prev = null_ptr; next = hd} in
  let s' = Seq.upd s (US.v idx) cell in
  lemma_dlist_upd pred s (US.v hd) (US.v idx) (US.v idx) cell;
  lemma_dlist_frame pred s (US.v hd) (US.v idx) cell;
  assert (is_dlist' pred (US.v hd) s' null FS.emptyset);
  assert (ptrs_in (US.v hd) s == ptrs_in (US.v hd) s');

  if hd <> null_ptr then begin
    lemma_dlist_insert_visited pred s' (US.v hd) (US.v idx) null FS.emptyset;
    let fs1 = FS.singleton (US.v idx) in
    assert (fs1 `FS.equal` FS.insert (US.v idx) FS.emptyset);
    assert (is_dlist' pred (US.v hd) s' null fs1);
    assert (ptrs_in (US.v idx) s' == FS.insert (US.v idx) (ptrs_in (US.v hd) s));
    let cell = Seq.index s' (US.v hd) in
    let cell = {cell with prev = idx} in
    let cur = Seq.index s' (US.v hd) in
    let next = cur.next in
    let fs2 = FS.singleton (US.v hd) in
    assert (FS.insert (US.v hd) fs1 `FS.equal` FS.insert (US.v idx) fs2);
    assert (is_dlist' pred (US.v next) s' (US.v hd) (FS.insert (US.v idx) fs2));
    // dedicated aux lemma
    lemma_dlist_mem_uniq pred s' (US.v hd) null fs1;
    assert (~ (mem' (US.v hd) (US.v next) s' (FS.insert (US.v idx) fs2)));
    lemma_dlist_upd' pred s' (US.v next) (US.v hd) (US.v hd) (US.v hd) (FS.insert (US.v idx) fs2) cell;
    lemma_dlist_frame' pred s' (US.v next) (US.v hd) (US.v hd) (FS.insert (US.v idx) fs2) cell;
    let s1 = Seq.upd s' (US.v hd) cell in
    assert (is_dlist' pred (US.v next) s1 (US.v hd) (FS.insert (US.v idx) fs2));
    assert (is_dlist' pred (US.v hd) s1 (US.v idx) fs1
    <==>
    is_dlist' pred (US.v next) s1 (US.v hd) (FS.insert (US.v hd) fs1) /\
    (US.v (Seq.index s1 (US.v hd)).prev == US.v idx)
    );
    assert (US.v (Seq.index s1 (US.v hd)).prev == US.v idx);
    let s2 = insert_spec pred s hd idx v in
    assert (s1 == s2);
    ()
  end else ()

/// Inserting an element in list1 that was not in list2 does not impact list2
val lemma_insert_spec_frame (#a:Type)
  (pred pred': a -> prop)
  (s:Seq.seq (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < Seq.length s})
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (hd':nat)
  (v:a)
  : Lemma (requires
            is_dlist pred (US.v hd) s /\ (~ (mem (US.v idx) (US.v hd) s)) /\
            is_dlist pred' hd' s /\ (~ (FS.mem (US.v idx) (ptrs_in hd' s))) /\
            disjoint s (US.v hd) hd')
          (ensures (
            let s' = insert_spec pred s hd idx v in
            is_dlist pred' hd' s' /\
            ptrs_in hd' s' == ptrs_in hd' s
          ))

let lemma_insert_spec_frame pred pred' s hd idx hd' v =
  let cell = {data = v; prev = null_ptr; next = hd} in
  let s1 = Seq.upd s (US.v idx) cell in
  lemma_mem_ptrs_in hd' s (US.v idx);
  lemma_dlist_frame pred' s hd' (US.v idx) cell;
  assert (is_dlist pred' hd' s1);
  assert (ptrs_in hd' s1 == ptrs_in hd' s);

  if hd <> null_ptr then begin
    let cell = Seq.index s1 (US.v hd) in
    let cell = {cell with prev = idx} in
    assert (mem (US.v hd) (US.v hd) s);
    lemma_mem_ptrs_in (US.v hd) s (US.v hd);
    lemma_mem_ptrs_in hd' s1 (US.v hd);
    assert (~ (mem (US.v hd) hd' s1));
    lemma_dlist_frame pred' s1 hd' (US.v hd) cell
  end else ()

/// Functional correctness on data of inserting an element
val lemma_insert_spec_dataify (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < Seq.length s})
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (v:a)
  : Lemma (requires pred v /\ is_dlist pred (US.v hd) s /\ (~ (mem (US.v idx) (US.v hd) s)))
          (ensures (
            let s' = insert_spec pred s hd idx v in
            dataify s' `Seq.equal` Seq.upd (dataify s) (US.v idx) v
          ))

let lemma_insert_spec_dataify pred s hd idx v =
  let s' = insert_spec pred s hd idx v in
  let aux (i:nat{i < Seq.length s /\ i <> US.v idx}) : Lemma (Seq.index (dataify s) i == Seq.index (dataify s') i) =
    Seq.map_seq_index get_data s i;
    Seq.map_seq_index get_data s' i
  in
  Seq.map_seq_index get_data s (US.v idx);
  Seq.map_seq_index get_data s' (US.v idx);

  Classical.forall_intro aux

/// Functional correctness of the remove_spec function:
/// The resulting list is still a doubly linked list, and
/// the element pointed to by [idx] was successfully removed
val lemma_remove_spec' (#a:Type)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev:nat)
  (idx:nat{idx < Seq.length s})
  (visited:FS.set nat{FS.cardinality visited <= Seq.length s})
  : Lemma (requires
            (forall i. FS.mem i visited ==> i < Seq.length s) /\
            is_dlist' pred hd s prev visited /\
            mem' idx hd s visited /\
            null_or_valid prev s /\
            not (FS.mem idx visited))
          (ensures (
            let c = Seq.index s idx in
            let hd' = if hd = idx then US.v c.next else hd in
            let s' = remove_spec pred hd s prev idx visited in
            is_dlist' pred hd' s' prev visited /\
            FS.remove idx (ptrs_in' hd s visited) `FS.equal` ptrs_in' hd' s' visited
          ))
          (decreases (Seq.length s - FS.cardinality visited))

#push-options "--z3rlimit 20"
let rec lemma_remove_spec' #a pred hd s prev idx visited =
  if hd = null then ()
  else begin

    let cur = Seq.index s hd in
    let next = US.v cur.next in
    let s' = remove_spec pred hd s prev idx visited in

    // Base case, we are at the head of the list
    if hd = idx then begin
      if next = null then ()
      else begin
        let nc0 = Seq.index s next in
        let nc = {nc0 with prev = cur.prev} in
        let sint = Seq.upd s next nc in

        let fs = FS.insert hd visited in
        assert (is_dlist' pred next s hd fs);
        assert (next <> null);

        let next2 = US.v nc0.next in
        assert (is_dlist' pred next2 s next (FS.insert next fs));
        lemma_dlist_mem_uniq pred s next hd fs;
        lemma_dlist_upd' pred s next2 next next next (FS.insert next fs) nc;
        assert (is_dlist' pred next2 sint next (FS.insert next fs));
        assert (is_dlist' pred next sint (US.v cur.prev) fs);

        lemma_dlist_frame' pred s next2 next next (FS.insert next fs) nc;
        // Direct conclusion of lemma above
        assert (ptrs_in' next2 s (FS.insert next fs) == ptrs_in' next2 sint (FS.insert next fs));
        // By definition
        assert (ptrs_in' next sint fs == FS.insert next (ptrs_in' next2 s (FS.insert next fs))) ;

        lemma_mem_not_in_visited pred sint next (US.v cur.prev) fs hd;
        assert (~ (mem' hd next sint fs));
        lemma_mem_ptrs_in' next sint fs hd;
        assert (not (FS.mem hd (ptrs_in' next sint fs)));

        lemma_dlist_remove_visited pred sint next hd (US.v cur.prev) visited;
        assert (is_dlist' pred next sint (US.v cur.prev) visited);
        assert (ptrs_in' next sint fs == ptrs_in' next sint visited);

        // Allows us to conclude the following
        assert (FS.remove idx (ptrs_in' hd s visited) `FS.equal` ptrs_in' next sint visited);

        if US.v cur.prev = null then ()
        else begin
          lemma_dlist_prev_not_mem pred sint next (US.v cur.prev) visited;
          assert (~ (mem' (US.v cur.prev) next sint visited));
          let pc0 = Seq.index s (US.v cur.prev) in
          let pc = {pc0 with next = cur.next} in
          assert (s' == Seq.upd sint (US.v cur.prev) pc);
          lemma_dlist_frame' pred sint next (US.v cur.prev) (US.v cur.prev) visited pc;
          lemma_mem_ptrs_in' next sint visited idx;
          assert (~ (mem' idx next sint visited));
          lemma_dlist_upd' pred sint next (US.v cur.prev) (US.v cur.prev) idx visited pc
        end
      end
    end
    else begin
      if next = null then ()
      else
        let c = Seq.index s idx in
        let hd' = if next = idx then US.v c.next else next in
        let vis' = FS.insert hd visited in
        lemma_remove_spec' pred next s hd idx vis';
        assert (remove_spec pred hd s prev idx visited ==
                remove_spec pred next s hd idx vis');

        assert (is_dlist' pred hd' s' hd vis');
        assert (FS.remove idx (ptrs_in' next s vis') == ptrs_in' hd' s' vis');

        let cur' = Seq.index s' hd in
        if next = idx then begin
          assert (US.v c.prev == hd);
          assert (cur' == {cur with next = c.next});
          assert (is_dlist' pred hd s' prev visited)
        end else begin
          lemma_mem_valid_or_null_next_prev' pred next s hd vis' idx;
          lemma_mem_not_in_visited pred s next hd vis' hd;
          assert (~ (mem' hd next s vis'));
          assert (hd <> US.v c.next);

          lemma_dlist_head_or_prev_not_visited pred next s hd vis' idx;
          assert (hd <> US.v c.prev);

          assert (cur' == cur);
          assert (is_dlist' pred hd s' prev visited)
        end
    end
  end
#pop-options

val lemma_remove_spec (#a:Type)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Lemma (requires is_dlist pred hd s /\ mem idx hd s)
          (ensures (
            let c = Seq.index s idx in
            let hd' = if hd = idx then US.v c.next else hd in
            let s' = remove_spec pred hd s null idx FS.emptyset in
            is_dlist pred hd' s' /\
            ptrs_in hd' s' == FS.remove idx (ptrs_in hd s)
          ))

let lemma_remove_spec #a pred hd s idx = lemma_remove_spec' pred hd s null idx FS.emptyset

/// Removing an element from a list does not impact a disjoint list
val lemma_remove_spec_frame (#a:Type)
  (pred pred': a -> prop)
  (hd hd':nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Lemma (requires
            is_dlist pred hd s /\ mem idx hd s /\
            is_dlist pred' hd' s /\ disjoint s hd hd')
          (ensures (
            let s' = remove_spec pred hd s null idx FS.emptyset in
            is_dlist pred' hd' s' /\
            ptrs_in hd' s' == ptrs_in hd' s
          ))

let lemma_remove_spec_frame pred pred' hd hd' s idx =
  let cell = Seq.index s idx in
  let s' = remove_spec pred hd s null idx FS.emptyset in

  lemma_mem_valid_or_null_next_prev' pred hd s null FS.emptyset idx;
  let sint =
    if cell.next <> null_ptr then
      // Next is not null, we need to update it
      let next = Seq.index s (US.v cell.next) in
      let next = {next with prev = cell.prev} in
      assert (mem (US.v cell.next) hd s);
      lemma_mem_ptrs_in hd s (US.v cell.next);
      lemma_mem_ptrs_in hd' s (US.v cell.next);

      lemma_dlist_frame pred' s hd' (US.v cell.next) next;
      Seq.upd s (US.v cell.next) next
    else s
  in

  assert (is_dlist pred' hd' sint);
  assert (ptrs_in hd' sint == ptrs_in hd' s);

  let sf =
    if cell.prev <> null_ptr then begin
      let prev = Seq.index sint (US.v cell.prev) in
      let prev = {prev with next = cell.next} in
      lemma_dlist_head_or_prev_not_visited pred hd s null FS.emptyset idx;
      assert (mem (US.v cell.prev) hd s);

      lemma_mem_ptrs_in hd s (US.v cell.prev);
      lemma_mem_ptrs_in hd' sint (US.v cell.prev);
      assert (~ (mem (US.v cell.prev) hd' sint));

      lemma_dlist_frame pred' sint hd' (US.v cell.prev) prev;
      Seq.upd sint (US.v cell.prev) prev
  end else sint
  in
  assert (sf == s');
  assert (is_dlist pred' hd' sf);
  assert (ptrs_in hd' sf == ptrs_in hd' sint)

/// Removing an element from the list does not change the data fields
val lemma_remove_spec_dataify (#a:Type)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Lemma (requires is_dlist pred hd s /\ mem idx hd s)
          (ensures (
            let c = Seq.index s idx in
            let s' = remove_spec pred hd s null idx FS.emptyset in
            dataify s `Seq.equal` dataify s'
          ))

let lemma_remove_spec_dataify pred hd s idx =
  let s' = remove_spec pred hd s null idx FS.emptyset in
  lemma_mem_valid_or_null_next_prev' pred hd s null FS.emptyset idx;

  let aux (i:nat{i < Seq.length s}) : Lemma (Seq.index (dataify s) i == Seq.index (dataify s') i) =
    Seq.map_seq_index get_data s i;
    Seq.map_seq_index get_data s' i
  in
  Classical.forall_intro aux


/// AF: The regular noop does not seem to pick the equality of selectors, not sure why
val noop (#opened:inames) (#p:vprop) (_:unit)
  : SteelGhostF unit opened p (fun _ -> p) (requires fun _ -> True) (ensures fun h0 _ h1 -> h0 p == h1 p)
let noop () = noop ()

/// Create an arraylist with
let intro_arraylist_nil #a #opened pred1 pred2 pred3 r hd1 hd2 hd3 =
  intro_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 (US.v hd1) (US.v hd2) (US.v hd3))

let lemma_head1_not_null_mem  pred1 pred2 pred3 r hd1 hd2 hd3 = noop ()

let lemma_head1_in_bounds pred1 pred2 pred3 r hd1 hd2 hd3 = noop ()

let lemma_head2_in_bounds pred1 pred2 pred3 r hd1 hd2 hd3 = noop ()

let lemma_head1_implies_pred1 pred1 pred2 pred3 r hd1 hd2 hd3 = noop ()

/// Reads at index [idx] in the array.
let read_in_place #a #pred1 #pred2 #pred3 r hd1 hd2 hd3 idx =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3);
  let res = A.index r idx in
  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3);
  (**) return res.data

/// Updates the `data` field of the cell at index [idx] in the array [r] with [v]
/// We define three different functions, depending on which list the element
/// belongs to. In all three cases, we require [v] to satisfy the predicate
/// corresponding to a given list
let write_in_place1 #a #pred1 #pred2 #pred3 r hd1 hd2 hd3 idx v =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3);
  let c = A.index r idx in
  (**) let gs = gget (A.varray r) in
  A.upd r idx (write_data c v);
  (**) lemma_write_data_frame pred1 hd1 gs (US.v idx) v;
  // The three lemmas below in conjunction with disjoint3 enable to infer
  // that idx does not belong to the hd2 or hd3 dlists
  (**) lemma_mem_ptrs_in hd1 gs (US.v idx);
  (**) lemma_mem_ptrs_in hd2 gs (US.v idx);
  (**) lemma_mem_ptrs_in hd3 gs (US.v idx);
  // Framing of the hd2 and hd3 dlists
  (**) lemma_dlist_frame pred2 gs hd2 (US.v idx) (write_data c v);
  (**) lemma_dlist_frame pred3 gs hd3 (US.v idx) (write_data c v);
  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3)

let write_in_place2 #a #pred1 #pred2 #pred3 r hd1 hd2 hd3 idx v =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3);
  let c = A.index r idx in
  (**) let gs = gget (A.varray r) in
  A.upd r idx (write_data c v);
  (**) lemma_write_data_frame pred2 hd2 gs (US.v idx) v;
  // The three lemmas below in conjunction with disjoint3 enable to infer
  // that idx does not belong to the hd1 or hd3 dlists
  (**) lemma_mem_ptrs_in hd1 gs (US.v idx);
  (**) lemma_mem_ptrs_in hd2 gs (US.v idx);
  (**) lemma_mem_ptrs_in hd3 gs (US.v idx);
  // Framing of the hd1 and hd3 dlists
  (**) lemma_dlist_frame pred1 gs hd1 (US.v idx) (write_data c v);
  (**) lemma_dlist_frame pred3 gs hd3 (US.v idx) (write_data c v);
  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3)

let write_in_place3  #a #pred1 #pred2 #pred3 r hd1 hd2 hd3 idx v =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3);
  let c = A.index r idx in
  (**) let gs = gget (A.varray r) in
  A.upd r idx (write_data c v);
  (**) lemma_write_data_frame pred3 hd3 gs (US.v idx) v;
  // The three lemmas below in conjunction with disjoint3 enable to infer
  // that idx does not belong to the hd1 or hd2 dlists
  (**) lemma_mem_ptrs_in hd1 gs (US.v idx);
  (**) lemma_mem_ptrs_in hd2 gs (US.v idx);
  (**) lemma_mem_ptrs_in hd3 gs (US.v idx);
  // Framing of the hd1 and hd2 dlists
  (**) lemma_dlist_frame pred2 gs hd2 (US.v idx) (write_data c v);
  (**) lemma_dlist_frame pred1 gs hd1 (US.v idx) (write_data c v);
  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3)


/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
let remove1 #a #pred1 #pred2 #pred3 r hd1 hd2 hd3 idx =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 (US.v hd1) hd2 hd3);
  (**) let gs0 = gget (A.varray r) in

  // Derive that idx is not in the two other lists, through disjointness and belonging to
  // the first list
  (**) lemma_mem_ptrs_in (US.v hd1) gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd2 gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd3 gs0 (US.v idx);

  let cell = A.index r idx in
  (**) lemma_mem_valid_or_null_next_prev pred1 (US.v hd1) gs0 (US.v idx);

  if cell.next <> null_ptr then
    // Next is not null, we need to update it
    let next = A.index r cell.next in
    let next = {next with prev = cell.prev} in
    A.upd r cell.next next
  else noop ();

  if cell.prev <> null_ptr then
    // Prev is not null, we need to update it
    let prev = A.index r cell.prev in
    let prev = {prev with next = cell.next} in
    A.upd r cell.prev prev
  else noop ();

  (**) let gs1 = gget (A.varray r) in
  let hd' = if hd1 = idx then cell.next else hd1 in
  (**) lemma_remove_spec pred1 (US.v hd1) gs0 (US.v idx);
  (**) lemma_remove_spec_frame pred1 pred2 (US.v hd1) hd2 gs0 (US.v idx);
  (**) lemma_remove_spec_frame pred1 pred3 (US.v hd1) hd3 gs0 (US.v idx);

  (**) lemma_remove_spec_dataify pred1 (US.v hd1) gs0 (US.v idx);

  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 (US.v hd') hd2 hd3);
  return hd'

/// Removes the element at offset [idx] from the dlist pointed to by [hd2]
let remove2 #a #pred1 #pred2 #pred3 r hd1 hd2 hd3 idx =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 (US.v hd2) hd3);
  (**) let gs0 = gget (A.varray r) in
  let cell = A.index r idx in
  (**) lemma_mem_valid_or_null_next_prev pred2 (US.v hd2) gs0 (US.v idx);

  // Derive that idx is not in the two other lists, through disjointness and belonging to
  // the first list
  (**) lemma_mem_ptrs_in (US.v hd2) gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd1 gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd3 gs0 (US.v idx);

  if cell.next <> null_ptr then
    // Next is not null, we need to update it
    let next = A.index r cell.next in
    let next = {next with prev = cell.prev} in
    A.upd r cell.next next
  else noop ();

  if cell.prev <> null_ptr then
    // Prev is not null, we need to update it
    let prev = A.index r cell.prev in
    let prev = {prev with next = cell.next} in
    A.upd r cell.prev prev
  else noop ();

  (**) let gs1 = gget (A.varray r) in
  let hd' = if hd2 = idx then cell.next else hd2 in
  (**) lemma_remove_spec pred2 (US.v hd2) gs0 (US.v idx);
  (**) lemma_remove_spec_frame pred2 pred1 (US.v hd2) hd1 gs0 (US.v idx);
  (**) lemma_remove_spec_frame pred2 pred3 (US.v hd2) hd3 gs0 (US.v idx);

  (**) lemma_remove_spec_dataify pred2 (US.v hd2) gs0 (US.v idx);

  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 (US.v hd') hd3);
  return hd'

/// Removes the element at offset [idx] from the dlist pointed to by [hd3]
let remove3 #a #pred1 #pred2 #pred3 r hd1 hd2 hd3 idx =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 (US.v hd3));
  (**) let gs0 = gget (A.varray r) in
  let cell = A.index r idx in
  (**) lemma_mem_valid_or_null_next_prev pred3 (US.v hd3) gs0 (US.v idx);

  // Derive that idx is not in the two other lists, through disjointness and belonging to
  // the first list
  (**) lemma_mem_ptrs_in (US.v hd3) gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd2 gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd1 gs0 (US.v idx);

  if cell.next <> null_ptr then
    // Next is not null, we need to update it
    let next = A.index r cell.next in
    let next = {next with prev = cell.prev} in
    A.upd r cell.next next
  else noop ();

  if cell.prev <> null_ptr then
    // Prev is not null, we need to update it
    let prev = A.index r cell.prev in
    let prev = {prev with next = cell.next} in
    A.upd r cell.prev prev
  else noop ();

  (**) let gs1 = gget (A.varray r) in
  let hd' = if hd3 = idx then cell.next else hd3 in
  (**) lemma_remove_spec pred3 (US.v hd3) gs0 (US.v idx);
  (**) lemma_remove_spec_frame pred3 pred2 (US.v hd3) hd2 gs0 (US.v idx);
  (**) lemma_remove_spec_frame pred3 pred1 (US.v hd3) hd1 gs0 (US.v idx);

  (**) lemma_remove_spec_dataify pred3 (US.v hd3) gs0 (US.v idx);

  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 (US.v hd'));
  return hd'

let insert1 #a #pred1 #pred2 #pred3 r hd hd2 hd3 idx v =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 (US.v hd) hd2 hd3);
  (**) let gs0 = gget (A.varray r) in

  let cell = {data = v; prev = null_ptr; next = hd} in
  A.upd r idx cell;
  if hd <> null_ptr then
    let cell = A.index r hd in
    let cell = {cell with prev = idx} in
    A.upd r hd cell
  else noop ();

  let gs1 = gget (A.varray r) in

  (**) lemma_mem_ptrs_in (US.v hd) gs0 (US.v idx);
  (**) lemma_insert_spec pred1 gs0 hd idx v;
  (**) lemma_insert_spec_frame pred1 pred2 gs0 hd idx hd2 v;
  (**) lemma_insert_spec_frame pred1 pred3 gs0 hd idx hd3 v;

  (**) lemma_insert_spec_dataify pred1 gs0 hd idx v;

  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 (US.v idx) hd2 hd3)

let insert2 #a #pred1 #pred2 #pred3 r hd hd1 hd3 idx v =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 (US.v hd) hd3);
  (**) let gs0 = gget (A.varray r) in

  let cell = {data = v; prev = null_ptr; next = hd} in
  A.upd r idx cell;
  if hd <> null_ptr then
    let cell = A.index r hd in
    let cell = {cell with prev = idx} in
    A.upd r hd cell
  else noop ();

  let gs1 = gget (A.varray r) in

  (**) lemma_mem_ptrs_in (US.v hd) gs0 (US.v idx);
  (**) lemma_insert_spec pred2 gs0 hd idx v;
  (**) lemma_insert_spec_frame pred2 pred1 gs0 hd idx hd1 v;
  (**) lemma_insert_spec_frame pred2 pred3 gs0 hd idx hd3 v;

  (**) lemma_insert_spec_dataify pred2 gs0 hd idx v;

  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 (US.v idx) hd3)

let insert3 #a #pred1 #pred2 #pred3 r hd hd1 hd2 idx v =
  (**) elim_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 (US.v hd));
  (**) let gs0 = gget (A.varray r) in

  let cell = {data = v; prev = null_ptr; next = hd} in
  A.upd r idx cell;
  if hd <> null_ptr then
    let cell = A.index r hd in
    let cell = {cell with prev = idx} in
    A.upd r hd cell
  else noop ();

  let gs1 = gget (A.varray r) in

  (**) lemma_mem_ptrs_in (US.v hd) gs0 (US.v idx);
  (**) lemma_insert_spec pred3 gs0 hd idx v;
  (**) lemma_insert_spec_frame pred3 pred2 gs0 hd idx hd2 v;
  (**) lemma_insert_spec_frame pred3 pred1 gs0 hd idx hd1 v;

  (**) lemma_insert_spec_dataify pred3 gs0 hd idx v;

  (**) intro_vrefine (A.varray r) (varraylist_refine pred1 pred2 pred3 hd1 hd2 (US.v idx))

/// An implementation of a map_seq_slice lemma currently not in F* ulib, specialized for `cell a`
let dataify_slice (#a:Type)
  (s: Seq.seq (cell a))
  (n:nat{n <= Seq.length s})
  : Lemma (dataify (Seq.slice s 0 n) == Seq.slice (dataify s) 0 n)
  = let s1 = dataify (Seq.slice s 0 n) in
    let s2 = Seq.slice (dataify s) 0 n in
    let aux (i:nat{i < n}) : Lemma (Seq.index s1 i == Seq.index s2 i)
      = Seq.map_seq_index get_data s i;
        Seq.map_seq_index get_data (Seq.slice s 0 n) i
    in Classical.forall_intro aux;
    Seq.lemma_eq_intro s1 s2

/// If we have a dlist on sequence [s], and [s'] is an extension of [s],
/// then we have a dlist on [s'] and the set of pointers in the list are
/// the same
let rec lemma_extend_dlist' (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev: nat)
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (s':Seq.seq (cell a))
  (n:nat{n <= Seq.length s})
  : Lemma
      (requires
        is_dlist' pred hd s prev visited /\
        Seq.length s' >= Seq.length s /\
        s `Seq.equal` Seq.slice s' 0 n)
      (ensures
        is_dlist' pred hd s' prev visited /\
        ptrs_in' hd s visited == ptrs_in' hd s' visited
      )
      (decreases (Seq.length s - FS.cardinality visited))
  = if hd = null then ()
    else if FS.cardinality visited = Seq.length s ||
       FS.mem hd visited ||
       // If the prev pointer is not null, it should be in the visited set
       not (prev = null || FS.mem prev visited) ||
       hd >= Seq.length s then ()
    else
      let cur = Seq.index s hd in
      let next = US.v cur.next in
      lemma_extend_dlist' pred next s hd (FS.insert hd visited) s' n

let lemma_extend_dlist (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (s':Seq.seq (cell a))
  (n:nat{n <= Seq.length s})
  : Lemma
      (requires
        is_dlist pred hd s /\
        Seq.length s' >= Seq.length s /\
        s `Seq.equal` Seq.slice s' 0 n)
      (ensures
        is_dlist pred hd s' /\
        ptrs_in hd s == ptrs_in hd s'
      )
  = lemma_extend_dlist' pred hd s null FS.emptyset s' n

#push-options "--z3rlimit 50"
let extend_aux (#a:Type) (#opened:_)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd1 hd2 hd3:Ghost.erased nat)
  (k:US.t{US.v k + 1 <= A.length r /\ US.fits (US.v k + 1)})
  (v:a)
  : SteelGhost unit opened
          (varraylist pred1 pred2 pred3 (A.split_l r k) hd1 hd2 hd3 `star`
            A.varray (A.split_l (A.split_r r k) 1sz))
          (fun _ -> varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) hd1 hd2 hd3)
          (requires fun _ ->
            k <> null_ptr /\ pred1 v)
          (ensures fun h0 _ h1 ->
            (~ (mem_all (US.v k) hd1 hd2 hd3
              (h1 (varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) hd1 hd2 hd3)))) /\
            Seq.slice (dataify (h1 (varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) hd1 hd2 hd3))) 0 (US.v k)
              ==
            dataify (h0 (varraylist pred1 pred2 pred3 (A.split_l r k) hd1 hd2 hd3))
          )
  =
  (**) let s0 = gget (varraylist pred1 pred2 pred3 (A.split_l r k) hd1 hd2 hd3) in

  (**) elim_vrefine (A.varray (A.split_l r k)) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3);
  (**) let gs0 = gget (A.varray (A.split_l r k)) in

  (**) A.ghost_join (A.split_l r k) (A.split_l (A.split_r r k) 1sz) ();
  (**) change_equal_slprop
         (A.varray (A.merge (A.split_l r k) (A.split_l (A.split_r r k) 1sz)))
         (A.varray (A.split_l r (k `US.add` 1sz)));

  (**) let gs1 = gget (A.varray (A.split_l r (k `US.add` 1sz))) in

  (**) lemma_extend_dlist pred1 hd1 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) lemma_extend_dlist pred2 hd2 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) lemma_extend_dlist pred3 hd3 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) assert (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3 (Ghost.reveal gs1));

  (**) lemma_mem_ptrs_in hd1 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd2 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd3 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd1 (Ghost.reveal gs1) (US.v k);
  (**) lemma_mem_ptrs_in hd2 (Ghost.reveal gs1) (US.v k);
  (**) lemma_mem_ptrs_in hd3 (Ghost.reveal gs1) (US.v k);
  (**) assert (~ (mem_all (US.v k) hd1 hd2 hd3 gs1));

  (**) intro_vrefine (A.varray (A.split_l r (k `US.add` 1sz))) (varraylist_refine pred1 pred2 pred3 hd1 hd2 hd3);

  (**) let s1 = gget (varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) hd1 hd2 hd3) in
  // Derived from the postcondition of join
  (**) assert (Ghost.reveal s0 `Seq.equal` Seq.slice #(cell a) (Ghost.reveal s1) 0 (US.v k));
  // Move the slice out of dataify
  (**) dataify_slice #a (Ghost.reveal s1) (US.v k)
#pop-options

#restart-solver
#push-options "--z3rlimit 100"
let extend1 (#a:Type)
  (#pred1 #pred2 #pred3: a -> prop)
  (r:A.array (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd2 hd3:Ghost.erased nat)
  (k:US.t{US.v k + 1 <= A.length r /\ US.fits (US.v k + 1)})
  (v:a)
  : Steel unit
          (varraylist pred1 pred2 pred3 (A.split_l r k) (US.v hd) hd2 hd3 `star`
            A.varray (A.split_l (A.split_r r k) 1sz))
          (fun _ -> varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3)
          (requires fun _ ->
            k <> null_ptr /\ pred1 v)
          (ensures fun h0 _ h1 ->
            dataify (h1 (varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3))
              ==
            Seq.append (dataify (h0 (varraylist pred1 pred2 pred3 (A.split_l r k) (US.v hd) hd2 hd3))) (Seq.create 1 v)
          )
  =
  (**) let s0 = gget (varraylist pred1 pred2 pred3 (A.split_l r k) (US.v hd) hd2 hd3) in

  extend_aux r (US.v hd) hd2 hd3 k v;

  insert1 (A.split_l r (k `US.add` 1sz)) hd hd2 hd3 k v;

  (**) let s2 = gget (varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3) in

  // Final conclusion
  (**) Seq.lemma_eq_intro #a
   (Seq.append (dataify (Ghost.reveal s0)) (Seq.create 1 v))
   (dataify (Ghost.reveal s2))
#pop-options
