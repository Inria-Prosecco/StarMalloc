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

/// As a convention, we represent NULL as 0
let null : nat = 0
noextract inline_for_extraction
let null_ptr : US.t = 0sz

/// The core logical predicate: For a sequence of cells [s], corresponding to the contents of an array,
/// there is a doubly linked list starting at s.[idx].
/// The [visited] argument is needed to ensure termination, it corresponds to the set of cells
/// previously visited. Acyclicity is specified by guaranteeing that we do not visit a cell twice.
/// [prev] corresponds to the index of the previous cell.
/// Note, as a convention, we consider that NULL corresponds to 0, and do not store anything there
let rec is_dlist' (#a:Type0) (hd:nat) (s:Seq.seq (cell a)) (prev:nat)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Tot prop (decreases (Seq.length s - FS.cardinality visited)) =
  // Null case.
  if hd = null then True
  else
    // Forbid cycles, ensure well-formedness of the "pointers"
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then False
    else
      let cur = Seq.index s hd in
      let next = US.v cur.next in
      is_dlist' next s hd (FS.insert hd visited) /\ US.v cur.prev == prev

/// The toplevel specification of being a list
/// When [hd] is the head pointer of the list, the set of visited nodes
/// is initially empty, and the prev "pointer" should be "NULL"
let is_dlist (#a:Type0) (hd:nat) (s:Seq.seq (cell a)) : prop =
  is_dlist' hd s null FS.emptyset

let rec mem' (#a:Type0) (x:nat) (hd:nat) (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Tot prop (decreases (Seq.length s - FS.cardinality visited)) =
  if x = null || x >= Seq.length s || hd = null then False
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

let next_ptr (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev:nat)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})

  : Ghost nat
          (requires is_dlist' hd s prev visited /\ hd <> null)
          (ensures fun _ -> True)
  = US.v (Seq.index s hd).next

(** Lemmas about the dlist predicate *)

/// Framing lemma: Only changing the `data` field of a cell
/// does not change the structure of the doubly linked list
let rec lemma_write_data_frame' (#a:Type0)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev:nat)
  (idx:nat{idx < Seq.length s})
  (v:a)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Lemma
      (requires is_dlist' hd s prev visited)
      (ensures is_dlist' hd (Seq.upd s idx (write_data (Seq.index s idx) v)) prev visited)
      (decreases (Seq.length s - FS.cardinality visited))
  = let s' = Seq.upd s idx (write_data (Seq.index s idx) v) in
    if hd = null then ()
    else
      if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd > Seq.length s then ()
      else
        let next1 = US.v (Seq.index s hd).next in
        let next2 = US.v (Seq.index s' hd).next in
        assert (next1 == next2);
        lemma_write_data_frame' next1 s hd idx v (FS.insert hd visited)

val lemma_write_data_frame (#a:Type0)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  (v:a)
  : Lemma
      (requires is_dlist hd s)
      (ensures is_dlist hd (Seq.upd s idx (write_data (Seq.index s idx) v)))

let lemma_write_data_frame #a hd s idx v =
  lemma_write_data_frame' hd s null idx v FS.emptyset

let null_or_valid (#a:Type) (ptr:nat) (s:Seq.seq (cell a)) = ptr = null \/ ptr < Seq.length s

val lemma_mem_valid_or_null_next_prev' (#a:Type0)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev: nat)
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (idx:nat)
  : Lemma
      (requires
        is_dlist' hd s prev visited /\
        mem' idx hd s visited /\
        null_or_valid prev s /\
        not (FS.mem idx visited))
      (ensures
        (let cell = Seq.index s idx in
        null_or_valid (US.v cell.next) s /\
        null_or_valid (US.v cell.prev) s /\
        True)
      )
      (decreases (Seq.length s - FS.cardinality visited))

let rec lemma_mem_valid_or_null_next_prev' #a hd s prev visited idx
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
    assert (is_dlist' next s hd (FS.insert hd visited));
    assert (mem' idx next s (FS.insert hd visited));
    lemma_mem_valid_or_null_next_prev' #a next s hd (FS.insert hd visited) idx
  end

val lemma_mem_valid_or_null_next_prev (#a:Type0)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat)
  : Lemma
      (requires is_dlist hd s /\ mem idx hd s)
      (ensures
        (let cell = Seq.index s idx in
        null_or_valid (US.v cell.prev) s /\ null_or_valid (US.v cell.next) s)
      )

let lemma_mem_valid_or_null_next_prev #a hd s idx =
  lemma_mem_valid_or_null_next_prev' hd s null FS.emptyset idx

(** Functional specifications of the more complicated functions *)

/// A ghost specification of the insertion function for doubly linked lists
let insert_spec (#a:Type)
  (s:Seq.seq (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < Seq.length s})
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (v:a)
  : Ghost (Seq.seq (cell a))
         (requires is_dlist (US.v hd) s /\ ~ (mem (US.v idx) (US.v hd) s))
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
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Ghost (Seq.seq (cell a))
         (requires is_dlist hd s /\ mem idx hd s)
         (ensures fun _ -> True)
         =
  let cell = Seq.index s idx in
  lemma_mem_valid_or_null_next_prev hd s idx;
  let s =
    if cell.prev <> null_ptr then
      let prev = Seq.index s (US.v cell.prev) in
      let prev = {prev with next = cell.next} in
      Seq.upd s (US.v cell.prev) prev
    else s
  in

  let s =
    if cell.next <> null_ptr then
      // Next is not null, we need to update it
      let next = Seq.index s (US.v cell.next) in
      let next = {next with prev = cell.prev} in
      Seq.upd s (US.v cell.next) next
    else s
  in s

(** Functional correctness lemmas for insert and remove *)

let rec lemma_dlist_upd' (#a:Type)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (prev: nat)
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (v: cell a)
  : Lemma
  (requires
    is_dlist' hd s prev visited /\
    ~ (mem' idx hd s visited))
  (ensures (
    let s' = Seq.upd s idx v in
    is_dlist' hd s' prev visited /\
    ~ (mem' idx hd s' visited)))
  (decreases (Seq.length s - FS.cardinality visited))
  =
  let s' = Seq.upd s idx v in
  if hd = null
  then
    ()
  else begin
    let cur = Seq.index s hd in
    let next = cur.next in
    assert (is_dlist' (US.v next) s hd (FS.insert hd visited));
    assert (~ (mem' idx hd s (FS.insert hd visited)));
    lemma_dlist_upd' s (US.v next) idx hd (FS.insert hd visited) v
  end

let lemma_dlist_upd (#a:Type)
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (v: cell a)
  : Lemma
  (requires
    is_dlist hd s /\
    ~ (mem idx hd s))
  (ensures (
    let s' = Seq.upd s idx v in
    is_dlist hd s' /\
    ~ (mem idx hd s')))
  = lemma_dlist_upd' s hd idx null FS.emptyset v

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
  (s:Seq.seq (cell a))
  (hd:nat{hd == null \/ hd < Seq.length s})
  (idx:nat{idx <> null /\ idx < Seq.length s})
  (prev: nat)
  (visited: FS.set nat{FS.cardinality visited < Seq.length s})
  : Lemma
  (requires
    (forall i. FS.mem i visited ==> i < Seq.length s) /\
    is_dlist' hd s prev visited /\
    ~ (mem' idx hd s visited))
  (ensures
    is_dlist' hd s prev (FS.insert idx visited) /\
    ~ (mem' idx hd s (FS.insert idx visited)))
  (decreases (Seq.length s - FS.cardinality visited))
  =
  if hd = null
  then ()
  else begin
    let cur = Seq.index s hd in
    let next = cur.next in
    assert (is_dlist' (US.v next) s hd (FS.insert hd visited));
    assert (~ (mem' idx hd s (FS.insert hd visited)));

    if US.v next = null then (
      lemma_finiteset_full_n (Seq.length s) hd (FS.insert idx visited)
    )
    else begin
      assert (FS.cardinality (FS.insert hd visited) < Seq.length s);
      lemma_dlist_insert_visited s (US.v next) idx hd (FS.insert hd visited);
      // Need to explicitly introduce Set extensionality
      assert (
        FS.insert hd (FS.insert idx visited)
        `FS.equal`
        FS.insert idx (FS.insert hd visited)
      )
    end
  end

/// If an element belongs to the visited set, then it
/// does not belong to the dlist
let rec lemma_mem_not_in_visited (#a:Type)
  (s:Seq.seq (cell a))
  (hd:nat)
  (prev:nat)
  (visited:FS.set nat{FS.cardinality visited <= Seq.length s})
  (ptr:nat)
  : Lemma
  (requires
    is_dlist' hd s prev visited /\
    FS.mem ptr visited
  )
  (ensures
    ~ (mem' ptr hd s visited))
  (decreases (Seq.length s - FS.cardinality visited))
  = if hd = null then ()
    else
      let cur = Seq.index s hd in
      let next = cur.next in
      lemma_mem_not_in_visited s (US.v next) hd (FS.insert hd visited) ptr

let lemma_dlist_mem_uniq (#a:Type)
  (s:Seq.seq (cell a))
  (hd:US.t{hd <> null_ptr \/ US.v hd < Seq.length s})
  (prev: nat)
  (visited: FS.set nat{FS.cardinality visited < Seq.length s})
  : Lemma
  (requires
    is_dlist' (US.v hd) s prev visited
  )
  (ensures (
    let cur = Seq.index s (US.v hd) in
    let next = cur.next in
    ~ (mem' (US.v hd) (US.v next) s (FS.insert (US.v hd) visited))
  ))
  =
  if US.v hd = null then ()
  else
    let cur = Seq.index s (US.v hd) in
    let next = cur.next in
    assert (not (FS.mem (US.v hd) visited));
    assert (is_dlist' (US.v next) s (US.v hd) (FS.insert (US.v hd) visited));
    lemma_mem_not_in_visited s (US.v next) (US.v hd) (FS.insert (US.v hd) visited) (US.v hd)


/// Functional correctness of the insert_spec function:
/// The resulting list is still a doubly linked list.
/// Note, proving that the element was added is trivial, so we do not include it here
let lemma_insert_spec (#a:Type)
  (s:Seq.seq (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < Seq.length s})
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (v:a)
  : Lemma (requires is_dlist (US.v hd) s /\ ~ (mem (US.v idx) (US.v hd) s))
          (ensures is_dlist (US.v idx) (insert_spec s hd idx v))
  =
  assert (is_dlist' (US.v hd) s null FS.emptyset);
  let cell = {data = v; prev = null_ptr; next = hd} in
  let s' = Seq.upd s (US.v idx) cell in
  lemma_dlist_upd s (US.v hd) (US.v idx) cell;
  assert (is_dlist' (US.v hd) s' null FS.emptyset);
  if hd <> null_ptr then begin
    lemma_dlist_insert_visited s' (US.v hd) (US.v idx) null FS.emptyset;
    let fs1 = FS.singleton (US.v idx) in
    FS.all_finite_set_facts_lemma ();
    assert (fs1 `FS.equal` FS.insert (US.v idx) FS.emptyset);
    assert (is_dlist' (US.v hd) s' null fs1);
    let cell = Seq.index s' (US.v hd) in
    let cell = {cell with prev = idx} in
    let cur = Seq.index s' (US.v hd) in
    let next = cur.next in
    let fs2 = FS.singleton (US.v hd) in
    assert (FS.insert (US.v hd) fs1 `FS.equal` FS.insert (US.v idx) fs2);
    assert (is_dlist' (US.v next) s' (US.v hd) (FS.insert (US.v idx) fs2));
    // dedicated aux lemma
    lemma_dlist_mem_uniq s' hd null fs1;
    assert (~ (mem' (US.v hd) (US.v next) s' (FS.insert (US.v idx) fs2)));
    lemma_dlist_upd' s' (US.v next) (US.v hd) (US.v hd) (FS.insert (US.v idx) fs2) cell;
    let s1 = Seq.upd s' (US.v hd) cell in
    assert (is_dlist' (US.v next) s1 (US.v hd) (FS.insert (US.v idx) fs2));
    assert (is_dlist' (US.v hd) s1 (US.v idx) fs1
    <==>
    is_dlist' (US.v next) s1 (US.v hd) (FS.insert (US.v hd) fs1) /\
    (US.v (Seq.index s1 (US.v hd)).prev == US.v idx)
    );
    assert (US.v (Seq.index s1 (US.v hd)).prev == US.v idx);
    let s2 = insert_spec s hd idx v in
    assert (s1 == s2);
    ()
  end else ()

/// Functional correctness of the remove_spec function:
/// The resulting list is still a doubly linked list, and
/// the element pointed to by [idx] was successfully removed
val lemma_remove_spec (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Lemma (requires is_dlist hd s /\ mem idx hd s)
          (ensures (
            let c = Seq.index s idx in
            let hd' = if hd = idx then US.v c.next else hd in
            let s' = remove_spec hd s idx in
            is_dlist hd' s' /\ ~ (mem idx hd' s')
          ))

let lemma_remove_spec #a hd s idx =
  // Derived trivially from the mem precondition
  assert (hd <> null);
  let cur = Seq.index s hd in
  let next = US.v cur.next in
  let s' = remove_spec hd s idx in

  if hd = idx then begin
    assert (cur.prev = null_ptr);
    if next = null then ()
    else begin
      assert (is_dlist' next s hd (FS.insert hd FS.emptyset));
      lemma_dlist_insert_visited s (cur.next) hd hd FS.emptyset;
      assume (is_dlist next s');
      assume (~ (mem idx next s'))
//      admit()
    end
//    assert (is_dlist' next s
  end else admit()

(** Steel functions and vprops *)

/// The main vprop of this module.
/// We have access to an array, such that the array contains a doubly linked list
/// when starting at offset [hd]
[@@__steel_reduce__]
let varraylist (#a:Type) (r:A.array (cell a)) (hd:nat) : vprop
  = A.varray r `vrefine` (is_dlist hd)


/// AF: The regular noop does not seem to pick the equality of selectors, not sure why
val noop (#opened:inames) (#p:vprop) (_:unit)
  : SteelGhostF unit opened p (fun _ -> p) (requires fun _ -> True) (ensures fun h0 _ h1 -> h0 p == h1 p)
let noop () = noop ()

/// Reads at index [idx] in the array.
/// TODO: The hd pointer should be ghost
val read_in_place (#a:Type)
  (r:A.array (cell a))
  (hd:nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel a
          (varraylist r hd)
          (fun _ -> varraylist r hd)
          (requires fun _ -> True)
          (ensures fun h0 _ h1 -> h0 (varraylist r hd) == h1 (varraylist r hd))

let read_in_place #a r hd idx =
  (**) elim_vrefine (A.varray r) (is_dlist hd);
  let res = A.index r idx in
  (**) intro_vrefine (A.varray r) (is_dlist hd);
  (**) return res.data


/// Updates the `data` field of the cell at index [idx] in the array [r] with [v]
/// TODO: The hd pointer should be ghost
val write_in_place (#a:Type)
  (r:A.array (cell a))
  (hd:nat)
  (idx:US.t{US.v idx < A.length r})
  (v:a)
   : Steel unit
          (varraylist r hd)
          (fun _ -> varraylist r hd)
          (requires fun _ -> True)
          (ensures fun h0 _ h1 -> True) // TODO

let write_in_place #a r hd idx v =
  (**) elim_vrefine (A.varray r) (is_dlist hd);
  let c = A.index r idx in
  (**) let gs = gget (A.varray r) in
  A.upd r idx (write_data c v);
  (**) lemma_write_data_frame hd gs (US.v idx) v;
  (**) intro_vrefine (A.varray r) (is_dlist hd)


/// Removes the element at offset [idx] from the dlist pointed to by [hd]
val remove (#a:Type)
  (r:A.array (cell a))
  (hd:nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel nat
          (varraylist r hd)
          (fun hd' -> varraylist r hd')
          (requires fun h -> mem (US.v idx) hd (h (varraylist r hd)))
          (ensures fun h0 hd' h1 ->
            ~ (mem (US.v idx) hd' (h1 (varraylist r hd')))) // TODO

let remove #a r hd idx =
  (**) elim_vrefine (A.varray r) (is_dlist hd);
  (**) let gs0 = gget (A.varray r) in
  let cell = A.index r idx in
  (**) lemma_mem_valid_or_null_next_prev hd gs0 (US.v idx);

  if cell.prev <> null_ptr then
    // Prev is not null, we need to update it
    let prev = A.index r cell.prev in
    let prev = {prev with next = cell.next} in
    A.upd r cell.prev prev
  else noop ();

  if cell.next <> null_ptr then
    // Next is not null, we need to update it
    let next = A.index r cell.next in
    let next = {next with prev = cell.prev} in
    A.upd r cell.next next
  else noop ();

  (**) let gs1 = gget (A.varray r) in
  let hd' = if hd = US.v idx then US.v cell.next else hd in
  (**) lemma_remove_spec hd gs0 (US.v idx);

  (**) intro_vrefine (A.varray r) (is_dlist hd');
  return hd'


/// Assuming the element at offset [idx] does not belong to the dlist,
/// insert it at the head
val insert (#a:Type)
  (r:A.array (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: a)
   : Steel unit
          (varraylist r (US.v hd))
          (fun _ -> varraylist r (US.v idx))
          (requires fun h -> ~ (mem (US.v idx) (US.v hd) (h (varraylist r (US.v hd)))))
          (ensures fun h0 hd' h1 ->
            mem (US.v idx) (US.v idx) (h1 (varraylist r (US.v idx)))) // TODO

let insert #a r hd idx v =
  (**) elim_vrefine (A.varray r) (is_dlist (US.v hd));
  (**) let gs0 = gget (A.varray r) in

  let cell = {data = v; prev = null_ptr; next = hd} in
  A.upd r idx cell;
  if hd <> null_ptr then
    let cell = A.index r hd in
    let cell = {cell with prev = idx} in
    A.upd r hd cell
  else noop ();

  (**) lemma_insert_spec gs0 hd idx v;
  (**) intro_vrefine (A.varray r) (is_dlist (US.v idx))
