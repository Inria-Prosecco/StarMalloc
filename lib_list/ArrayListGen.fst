module ArrayListGen

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef

module A = Steel.Array
module L = FStar.List.Tot
module US = FStar.SizeT
module FS = FStar.FiniteSet.Base
module G = FStar.Ghost
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

let lemma_dataify_index s i =
  Seq.map_seq_index get_data s i

/// An implementation of a map_seq_slice lemma currently not in F* ulib, specialized for `cell a`
let lemma_dataify_slice (#a:Type)
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
    if FS.cardinality visited = Seq.length s
    || hd >= Seq.length s
    || FS.mem hd visited
    then False
    else
      if x = hd then True
      else
        let next = US.v (Seq.index s hd).next in
        mem' x next s (FS.insert hd visited)

/// Offset [x] belongs to the list starting at [hd]
let mem (#a:Type0) (x:nat) (hd:nat) (s:Seq.seq (cell a)) : prop =
  mem' x hd s FS.emptyset

/// An alternative specification for belonging to the list,
/// `ptrs_in_list` returns the list of elements in the list starting
/// at [hd], in reverse order
let rec ptrs_in_list'' (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : GTot (v:list nat{
    (forall (x:nat). FS.mem x visited ==> not (L.mem x v))
  })
    (decreases (Seq.length s - FS.cardinality visited))
  =
  if hd = null then []
  else
    // Ill-formed list
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then
      []
    else
      let next = US.v (Seq.index s hd).next in
      hd::(ptrs_in_list'' next s (FS.insert hd visited))

let rec ptrs_in_list' (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : GTot (v:list nat{
    (forall (x:nat). FS.mem x visited ==> not (L.mem x v)) /\
    FS.list_nonrepeating v /\
    v == ptrs_in_list'' hd s visited /\
    (Cons? v ==> L.hd v < Seq.length s)
  })
    (decreases (Seq.length s - FS.cardinality visited))
  =
  if hd = null then []
  else
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then
      []
    else (
      let next = US.v (Seq.index s hd).next in
      hd::(ptrs_in_list' next s (FS.insert hd visited))
    )

let ptrs_in_list (#a:Type) (hd:nat) (s:Seq.seq (cell a))
  = ptrs_in_list' hd s FS.emptyset

let rec ptrs_in' (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : GTot (v:FS.set nat{FS.disjoint visited v})
  (decreases (Seq.length s - FS.cardinality visited))
  =
  if hd = null then FS.emptyset
  else
    // Ill-formed list
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then
      FS.emptyset
    else
      let next = US.v (Seq.index s hd).next in
      FS.insert hd (ptrs_in' next s (FS.insert hd visited))

let ptrs_in #a hd s
  = ptrs_in' hd s FS.emptyset

let rec ptrs_in'_equal_ptrs_in_list' (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Lemma
  (ensures (
    let v1 = ptrs_in' hd s visited in
    let v2 = ptrs_in_list' hd s visited in
    v1 `FS.equal` SU.list_to_set v2
  ))
  (decreases (Seq.length s - FS.cardinality visited))
  =
  let v1 = ptrs_in' hd s visited in
  let v2 = ptrs_in_list' hd s visited in
  if hd = null then (
    SU.list_to_set_empty #nat
  ) else (
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s then (
      SU.list_to_set_empty #nat
    ) else (
      let next = US.v (Seq.index s hd).next in
      let v1' = ptrs_in' next s (FS.insert hd visited) in
      let v2' = ptrs_in_list' next s (FS.insert hd visited) in
      ptrs_in'_equal_ptrs_in_list' next s (FS.insert hd visited);
      assert (SU.list_to_set v2' == v1');
      assert (v2 == hd::v2');
      SU.list_to_set_cons hd v2';
      assert (SU.list_to_set (hd::v2') `FS.equal` FS.insert hd (SU.list_to_set v2'));
      assert (SU.list_to_set v2 == FS.insert hd v1');
      assert (v1 `FS.equal` FS.insert hd v1')
    )
  )

let ptrs_in_equal_ptrs_in_list #a hd s
  = ptrs_in'_equal_ptrs_in_list' hd s FS.emptyset

#restart-solver

let is_dlist2 (#a:Type0) (pred: a -> prop) (hd tl:nat) (s:Seq.seq (cell a))
  : prop
  =
  is_dlist pred hd s /\
  (
    (hd = US.v null_ptr ==> tl = US.v null_ptr) /\
    (hd <> US.v null_ptr ==> (
      Cons? (ptrs_in_list hd s) /\
      L.last (ptrs_in_list hd s) == tl /\
      tl < Seq.length s /\
      (Seq.index s tl).next = null_ptr
    ))
  )

let is_dlist2_lemma (#a:Type0) (pred: a -> prop) (hd tl:nat) (s s':Seq.seq (cell a))
  : Lemma
  (requires
    Seq.length s' = Seq.length s /\
    ptrs_in_list hd s' == ptrs_in_list hd s /\
    ptrs_in hd s' == ptrs_in hd s /\
    is_dlist2 pred hd tl s /\
    (tl < Seq.length s ==>
      (Seq.index s' tl).next == (Seq.index s tl).next
    ) /\
    is_dlist pred hd s'
  )
  (ensures
    is_dlist2 pred hd tl s'
  )
  =
  ()

let is_dlist2_implies_spec (#a:Type0) (pred: a -> prop)
  (hd tl:nat)
  (s:Seq.seq (cell a))
  = ()

/// Equivalence lemma between `mem` and membership in `ptrs_in`
let rec lemma_mem_ptrs_in' (#a:Type)
  (hd:nat)
  (s:Seq.seq (cell a))
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  (x:nat)
  : Lemma
    (ensures
      mem' x hd s visited
      <==>
      FS.mem x (ptrs_in' hd s visited))
    (decreases (Seq.length s - FS.cardinality visited))
  =
  if hd = null then ()
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
  =
  lemma_mem_ptrs_in' hd s FS.emptyset x

/// If an element belongs to a list, then it satisfies the corresponding
/// list predicate
let rec lemma_mem_implies_pred' (#a:Type)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev:nat)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  (x:nat)
  : Lemma
    (requires mem' x hd s visited /\ is_dlist' pred hd s prev visited)
    (ensures pred (get_data (Seq.index s x)))
    (decreases (Seq.length s - FS.cardinality visited))
  = if hd = null || x = hd then ()
    else
      let next = US.v (Seq.index s hd).next in
      lemma_mem_implies_pred' pred next s hd (FS.insert hd visited) x

let lemma_mem_implies_pred (#a:Type)
  (pred: a -> prop)
  (hd:nat)
  (s: Seq.seq (cell a))
  (x:nat{x < Seq.length s})
  : Lemma
    (requires mem x hd s /\ is_dlist pred hd s)
    (ensures pred (get_data (Seq.index s x)))
  = lemma_mem_implies_pred' pred hd s null FS.emptyset x

/// Disjointness between two lists, specified directly on the sets of pointers
/// to alleviate the need for recursive reasoning
let disjoint (#a:Type)
  (s: Seq.seq (cell a))
  (hd1 hd2: nat)
  = ptrs_in hd1 s `FS.disjoint` ptrs_in hd2 s /\ True

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

val mem_and_not_head_implies_prev_not_null' (#a: Type)
  (_hd: nat)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd prev: nat)
  (idx: nat{idx < Seq.length s})
  (idx_prev: nat)
  (visited:FS.set nat{
    Seq.length s >= FS.cardinality visited
  })
  : Lemma
  (requires (
    let cell = Seq.index s idx in
    let s0 = ptrs_in _hd s in
    let s1 = ptrs_in' hd s visited in
    let s2 = visited in
    (hd = idx ==>
      idx_prev < Seq.length s /\
      FS.mem idx_prev (ptrs_in _hd s)
    ) /\
    idx_prev = US.v cell.prev /\
    is_dlist pred _hd s /\
    is_dlist' pred hd s prev visited /\
    FS.mem idx s1 /\
    FS.disjoint s1 s2 /\
    s0 `FS.equal` FS.union s1 s2 /\
    True
  ))
  (ensures
    idx_prev < Seq.length s /\
    idx_prev <> idx /\
    FS.mem idx_prev (ptrs_in _hd s)
  )
  (decreases (Seq.length s - FS.cardinality visited))

#restart-solver

#push-options "--z3rlimit 150 --query_stats --split_queries no --query_stats"
let rec mem_and_not_head_implies_prev_not_null' #a _hd pred s hd prev idx idx_prev visited
  =
  if hd = null
  then (
    assert (hd <> idx_prev)
  ) else (
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s
    then (
      assert (hd <> idx_prev)
    ) else (
      if hd = idx_prev then (
        assert (FS.mem idx_prev (ptrs_in' hd s visited));
        assert (ptrs_in' hd s visited `FS.subset` ptrs_in _hd s);
        assert (FS.mem idx_prev (ptrs_in _hd s));
        assert (idx_prev < Seq.length s);
        ()
      ) else (
        if hd = idx
        then (
          ()
        ) else (
          let next = US.v (Seq.index s hd).next in
          assert (is_dlist' pred next s hd (FS.insert hd visited));
          let s0 = ptrs_in _hd s in
          let s1 = visited in
          let s2 = ptrs_in' hd s visited in
          let s3 = FS.insert hd visited in
          let s4 = ptrs_in' next s s3 in
          assert (s0 `FS.equal` FS.union s1 s2);
          assert (FS.union s3 s4 `FS.equal` FS.union s1 s2);
          assert (s0 `FS.equal` FS.union s3 s4);
          assert (s2 == FS.insert hd s4);
          assert (s4 == FS.remove hd s2);
          assert (FS.disjoint s3 s4);
          assert (s0 == FS.union s3 s4);
          mem_and_not_head_implies_prev_not_null' _hd pred s next hd idx idx_prev s3;
          assert (idx_prev < Seq.length s)
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 30"
let mem_and_not_head_implies_prev_not_null (#a: Type)
  (_hd: nat)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (idx: nat{idx < Seq.length s})
  (idx_prev: nat)
  : Lemma
  (requires (
    let cell = Seq.index s idx in
    idx_prev = US.v cell.prev /\
    is_dlist pred _hd s /\
    mem idx _hd s /\
    idx <> _hd
  ))
  (ensures (
    idx_prev < Seq.length s /\
    idx_prev <> idx /\
    mem idx_prev _hd s
  ))
  =
  assert (_hd <> null);
  assert (_hd < Seq.length s);
  let next = US.v (Seq.index s _hd).next in
  assert (ptrs_in _hd s `FS.equal` ptrs_in' _hd s FS.emptyset);
  assert (ptrs_in' _hd s FS.emptyset
  `FS.equal`
  FS.insert _hd (ptrs_in' next s (FS.insert _hd FS.emptyset))
  );
  let s1 = ptrs_in' next s (FS.insert _hd FS.emptyset) in
  assert (s1 `FS.disjoint` (FS.insert _hd FS.emptyset));
  lemma_mem_ptrs_in _hd s idx;
  mem_and_not_head_implies_prev_not_null' _hd pred s
    next _hd
    idx idx_prev
    (FS.insert _hd FS.emptyset);
  lemma_mem_ptrs_in _hd s idx_prev
#pop-options

val null_or_mem_prev (#a: Type)
  (_hd: nat)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd prev: nat)
  (idx: nat{idx < Seq.length s})
  (idx_prev: nat)
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Lemma
  (requires (
    let cell = Seq.index s idx in
    let s0 = ptrs_in _hd s in
    let s1 = ptrs_in' hd s visited in
    let s2 = visited in
    idx_prev = US.v cell.prev /\
    is_dlist pred _hd s /\
    is_dlist' pred hd s prev visited /\
    FS.mem idx s1 /\
    FS.disjoint s1 s2 /\
    s0 `FS.equal` FS.union s1 s2
  ))
  (ensures
    idx_prev = null \/
    FS.mem idx_prev (ptrs_in _hd s)
  )
  (decreases (Seq.length s - FS.cardinality visited))

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150 --query_stats --split_queries no"

let rec null_or_mem_prev #a _hd pred s hd prev idx idx_prev visited
  =
  if hd = null
  then (
    assert (hd <> idx_prev)
  ) else (
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s
    then (
      assert (hd <> idx_prev)
    ) else (
      if hd = idx_prev then (
        assert (FS.mem idx_prev (ptrs_in' hd s visited));
        assert (ptrs_in' hd s visited `FS.subset` ptrs_in _hd s);
        assert (FS.mem idx_prev (ptrs_in _hd s));
        assert (idx_prev < Seq.length s);
        ()
      ) else (
        if hd = idx
        then (
          assert (prev = idx_prev);
          ()
        ) else (
          let next = US.v (Seq.index s hd).next in
          assert (is_dlist' pred next s hd (FS.insert hd visited));
          let s0 = ptrs_in _hd s in
          let s1 = visited in
          let s2 = ptrs_in' hd s visited in
          let s3 = FS.insert hd visited in
          let s4 = ptrs_in' next s s3 in
          assert (s0 `FS.equal` FS.union s1 s2);
          assert (FS.union s3 s4 `FS.equal` FS.union s1 s2);
          assert (s0 `FS.equal` FS.union s3 s4);
          assert (s2 == FS.insert hd s4);
          assert (s4 == FS.remove hd s2);
          assert (FS.disjoint s3 s4);
          assert (s0 == FS.union s3 s4);
          null_or_mem_prev _hd pred s next hd idx idx_prev s3
        )
      )
    )
  )
#pop-options

val next_null_is_last' (#a: Type)
  (_hd: nat)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd prev: nat)
  (idx: nat{idx < Seq.length s})
  (visited:FS.set nat{Seq.length s >= FS.cardinality visited})
  : Lemma
  (requires (
    let cell = Seq.index s idx in
    let s0 = ptrs_in _hd s in
    let s1 = ptrs_in' hd s visited in
    let s2 = visited in
    US.v cell.next = null /\
    is_dlist pred _hd s /\
    is_dlist' pred hd s prev visited /\
    FS.mem idx s1 /\
    FS.disjoint s1 s2 /\
    s0 `FS.equal` FS.union s1 s2
  ))
  (ensures
    idx = L.last (ptrs_in_list' hd s visited)
  )
  (decreases (Seq.length s - FS.cardinality visited))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150 --query_stats --split_queries no"
let rec next_null_is_last' #a _hd pred s hd prev idx visited
  =
 if hd = null
  then (
    ()
  ) else (
    if FS.cardinality visited = Seq.length s || FS.mem hd visited || hd >= Seq.length s
    then (
      ()
    ) else (
       if hd = idx
        then (
          ()
        ) else (
          let next = US.v (Seq.index s hd).next in
          assert (is_dlist' pred next s hd (FS.insert hd visited));
          let s0 = ptrs_in _hd s in
          let s1 = visited in
          let s2 = ptrs_in' hd s visited in
          let s3 = FS.insert hd visited in
          let s4 = ptrs_in' next s s3 in
          assert (s0 `FS.equal` FS.union s1 s2);
          assert (FS.union s3 s4 `FS.equal` FS.union s1 s2);
          assert (s0 `FS.equal` FS.union s3 s4);
          assert (s2 == FS.insert hd s4);
          assert (s4 == FS.remove hd s2);
          assert (FS.disjoint s3 s4);
          assert (s0 == FS.union s3 s4);
          next_null_is_last' _hd pred s next hd idx s3
        )
      )
    )
#pop-options

let next_null_is_last (#a: Type)
  (_hd: nat)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (idx: nat{idx < Seq.length s})
  : Lemma
  (requires (
    let cell = Seq.index s idx in
    US.v cell.next = null /\
    is_dlist pred _hd s /\
    mem idx _hd s
  ))
  (ensures
    idx = L.last (ptrs_in_list _hd s)
  )
  =
  lemma_mem_ptrs_in _hd s idx;
  next_null_is_last'
    _hd pred s _hd null idx FS.emptyset

let lemma_mem_implies_mem_prev (#a: Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Lemma
  (requires (
    let cell = Seq.index s idx in
    let prev = US.v cell.prev in
    null_or_valid prev s /\
    is_dlist pred hd s /\
    mem idx hd s
  ))
  (ensures (
    let cell = Seq.index s idx in
    let prev = US.v cell.prev in
    (prev = null \/ mem prev hd s)
  ))
  =
  let cell = Seq.index s idx in
  let x = US.v cell.prev in
  lemma_mem_ptrs_in hd s idx;
  null_or_mem_prev hd pred s hd null idx x FS.emptyset;
  lemma_mem_ptrs_in hd s x

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

#push-options "--fuel 2 --ifuel 2"
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
#pop-options

val lemma_mem_valid_or_null_next_prev (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (idx:nat)
  : Lemma
      (requires is_dlist pred hd s /\ mem idx hd s)
      (ensures (
        let cell = Seq.index s idx in
        null_or_valid (US.v cell.prev) s /\
        null_or_valid (US.v cell.next) s /\
        (US.v cell.next == null \/ mem (US.v cell.next) hd s) /\
        (US.v cell.prev == null \/ mem (US.v cell.prev) hd s)
      ))

let lemma_mem_valid_or_null_next_prev #a pred hd s idx
  =
  lemma_mem_valid_or_null_next_prev' pred hd s null FS.emptyset idx;
  lemma_mem_implies_mem_prev pred hd s idx

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

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
val lemma_dlist_insert_visited (#a:Type)
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
    ptrs_in_list' hd s visited == ptrs_in_list' hd s (FS.insert idx visited) /\
    ptrs_in' hd s visited == ptrs_in' hd s (FS.insert idx visited))
  (decreases (Seq.length s - FS.cardinality visited))

let rec lemma_dlist_insert_visited pred s hd idx prev visited
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
      lemma_dlist_insert_visited pred s (US.v next) idx hd (FS.insert hd visited);
      assert (
        FS.insert hd (FS.insert idx visited)
        `FS.equal`
        FS.insert idx (FS.insert hd visited)
      )
    end
  end
#pop-options

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

#push-options "--fuel 2 --ifuel 2"
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
    ptrs_in_list' hd s visited == ptrs_in_list' hd s' visited /\
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
#pop-options

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
    ptrs_in_list hd s == ptrs_in_list hd s' /\
    ptrs_in hd s == ptrs_in hd s'
  ))
  = lemma_dlist_frame' pred s hd idx null FS.emptyset v

#push-options "--fuel 2 --ifuel 2"
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
    ptrs_in_list' hd s visited == ptrs_in_list' hd s (FS.insert idx visited) /\
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

#push-options "--z3rlimit 30"
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
            ptrs_in_list (US.v idx) s' == (US.v idx)::(ptrs_in_list (US.v hd) s) /\
            ptrs_in (US.v idx) s' `FS.equal` FS.insert (US.v idx) (ptrs_in (US.v hd) s)
          ))
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
#pop-options

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
            ptrs_in_list hd' s' == ptrs_in_list hd' s /\
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

/// Inserting an element in list1 that was not in list2 does not impact list2
val lemma_insert_spec_frame2 (#a:Type)
  (pred pred': a -> prop)
  (s:Seq.seq (cell a))
  (hd:US.t{hd == null_ptr \/ US.v hd < Seq.length s})
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (hd5 tl5:nat)
  (v:a)
  : Lemma
  (requires
    is_dlist pred (US.v hd) s /\
    (~ (mem (US.v idx) (US.v hd) s)) /\
    is_dlist2 pred' hd5 tl5 s /\
    (~ (FS.mem (US.v idx) (ptrs_in hd5 s))) /\
    disjoint s (US.v hd) hd5)
  (ensures (
    let s' = insert_spec pred s hd idx v in
    is_dlist2 pred' hd5 tl5 s' /\
    ptrs_in_list hd5 s' == ptrs_in_list hd5 s /\
    ptrs_in hd5 s' == ptrs_in hd5 s
  ))

#restart-solver

open MiscList

let lemma_insert_spec_frame2 pred pred' s hd idx hd5 tl5 v =
  lemma_insert_spec_frame pred pred' s hd idx hd5 v;
  if hd5 <> null then (
    let l = ptrs_in_list hd5 s in
    last_mem_lemma l;
    assert (L.mem tl5 l);
    ptrs_in_equal_ptrs_in_list hd5 s;
    SU.list_to_set_equivmem l tl5;
    lemma_mem_ptrs_in hd5 s tl5;
    assert (mem tl5 hd5 s)
  ) else (
    assert (tl5 = null)
  )

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let lemma_insert_spec2 (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd tl: (v:US.t{v == null_ptr \/ US.v v < Seq.length s}))
  (idx:US.t{idx <> null_ptr /\ US.v idx < Seq.length s})
  (v:a)
  : Lemma
  (requires pred v /\
    is_dlist2 pred (US.v hd) (US.v tl) s /\
    (~ (mem (US.v idx) (US.v hd) s)))
  (ensures (
     let s' = insert_spec pred s hd idx v in
     let tl' = if hd = null_ptr then idx else tl in
     is_dlist2 pred (US.v idx) (US.v tl') s' /\
     ptrs_in (US.v idx) s' `FS.equal` FS.insert (US.v idx) (ptrs_in (US.v hd) s))
  )
  =
  lemma_insert_spec pred s hd idx v;
  let s' = insert_spec pred s hd idx v in
  let l = ptrs_in_list (US.v hd) s in
  let l' = ptrs_in_list (US.v idx) s' in
  let tl' = if hd = null_ptr then idx else tl in
  if hd = null_ptr
  then ()
  else (
    assert (Cons? l);
    assert (l' == (US.v idx)::l);
    L.lemma_append_last [US.v idx] l;
    assert (L.last l == US.v tl);
    assert (US.v tl < Seq.length s);
    // prove idx <> tl, as L.mem tl l <> L.mem idx l
    last_mem_lemma l ;
    assert (L.mem (US.v tl) l);
    ptrs_in_equal_ptrs_in_list (US.v hd) s;
    SU.list_to_set_equivmem l (US.v tl);
    lemma_mem_ptrs_in (US.v hd) s (US.v tl);
    assert (idx <> tl)
  )
#pop-options

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
  : Lemma
  (requires
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
    ptrs_in_list' hd' s' visited
    == SU.list_remove idx (ptrs_in_list' hd s visited) /\
    ptrs_in' hd' s' visited
    `FS.equal` FS.remove idx (ptrs_in' hd s visited)
  ))
  (decreases (Seq.length s - FS.cardinality visited))

#push-options "--z3rlimit 50"
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
  : Lemma
  (requires is_dlist pred hd s /\ mem idx hd s)
  (ensures (
    let c = Seq.index s idx in
    let hd' = if hd = idx then US.v c.next else hd in
    let s' = remove_spec pred hd s null idx FS.emptyset in
    is_dlist pred hd' s' /\
    ptrs_in_list hd' s'
    == SU.list_remove idx (ptrs_in_list hd s) /\
    ptrs_in hd' s'
    == FS.remove idx (ptrs_in hd s)
  ))

let lemma_remove_spec #a pred hd s idx = lemma_remove_spec' pred hd s null idx FS.emptyset

/// Removing an element from a list does not impact a disjoint list
val lemma_remove_spec_frame (#a:Type)
  (pred pred': a -> prop)
  (hd hd':nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Lemma
  (requires
    is_dlist pred hd s /\ mem idx hd s /\
    is_dlist pred' hd' s /\ disjoint s hd hd')
  (ensures (
    let s' = remove_spec pred hd s null idx FS.emptyset in
    is_dlist pred' hd' s' /\
    ptrs_in_list hd' s' == ptrs_in_list hd' s /\
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

let lemma_remove_spec_frame2 (#a:Type)
  (pred pred': a -> prop)
  (hd hd5 tl5:nat)
  (s:Seq.seq (cell a))
  (idx:nat{idx < Seq.length s})
  : Lemma
  (requires
    is_dlist pred hd s /\
    mem idx hd s /\
    is_dlist2 pred' hd5 tl5 s /\
    disjoint s hd hd5)
  (ensures (
    let s' = remove_spec pred hd s null idx FS.emptyset in
    is_dlist2 pred' hd5 tl5 s' /\
    ptrs_in_list hd5 s' == ptrs_in_list hd5 s /\
    ptrs_in hd5 s' == ptrs_in hd5 s
  ))
  =
  lemma_remove_spec_frame pred pred' hd hd5 s idx;
  if hd5 <> null then (
    let l = ptrs_in_list hd5 s in
    last_mem_lemma l;
    assert (L.mem tl5 l);
    ptrs_in_equal_ptrs_in_list hd5 s;
    SU.list_to_set_equivmem l tl5;
    lemma_mem_ptrs_in hd5 s tl5;
    assert (mem tl5 hd5 s);
    assert (tl5 <> hd);
    assert (hd5 <> hd);
    let cell = Seq.index s idx in
    if cell.next <> null_ptr then (
      lemma_mem_valid_or_null_next_prev pred hd s idx;
      assert (mem (US.v cell.next) hd s);
      lemma_mem_ptrs_in hd s (US.v cell.next);
      assert (US.v cell.next <> tl5);
      assert (US.v cell.next <> hd5)
    );
    if cell.prev <> null_ptr then (
      lemma_mem_valid_or_null_next_prev pred hd s idx;
      assert (mem (US.v cell.prev) hd s);
      lemma_mem_ptrs_in hd s (US.v cell.prev);
      assert (US.v cell.prev <> tl5);
      assert (US.v cell.prev <> hd5)
    )
  ) else (
    assert (tl5 = null)
  )

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
#pop-options

#restart-solver

#push-options "--z3rlimit 30"
let lemma_remove_spec2_mem_new_tl (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd tl: (v:US.t{US.v v < Seq.length s}))
  : Lemma
  (requires
    is_dlist2 pred (US.v hd) (US.v tl) s /\
    mem (US.v tl) (US.v hd) s /\
    hd <> tl
  )
  (ensures (
    let s' = remove_spec pred (US.v hd) s null (US.v tl) FS.emptyset in
    let cell = Seq.index s (US.v tl) in
    let tl' = cell.prev in
    mem (US.v tl') (US.v hd) s'
  ))
  =
  let s' = remove_spec pred (US.v hd) s null (US.v tl) FS.emptyset in
  let cell = Seq.index s (US.v tl) in
  lemma_mem_ptrs_in (US.v hd) s (US.v tl);
  null_or_mem_prev
    (US.v hd) pred s (US.v hd) null (US.v tl) (US.v cell.prev) FS.emptyset;
  mem_and_not_head_implies_prev_not_null
    (US.v hd) pred s (US.v tl) (US.v cell.prev);
  assert (US.v cell.prev <> US.v tl);
  lemma_remove_spec pred (US.v hd) s (US.v tl);
  lemma_mem_ptrs_in (US.v hd) s' (US.v cell.prev);
  assert (mem (US.v cell.prev) (US.v hd) s')

let lemma_remove_spec2 (#a:Type)
  (pred: a -> prop)
  (s:Seq.seq (cell a))
  (hd tl: (v:US.t{US.v v < Seq.length s}))
  : Lemma
  (requires
    is_dlist2 pred (US.v hd) (US.v tl) s /\
    mem (US.v tl) (US.v hd) s
  )
  (ensures (
    let s' = remove_spec pred (US.v hd) s null (US.v tl) FS.emptyset in
    let cell = Seq.index s (US.v tl) in
    let tl' = cell.prev in
    let hd' = if hd = tl then cell.next else hd in
    is_dlist2 pred (US.v hd') (US.v tl') s'
  ))
  =
  lemma_remove_spec pred (US.v hd) s (US.v tl);
  let s' = remove_spec pred (US.v hd) s null (US.v tl) FS.emptyset in
  let cell = Seq.index s (US.v tl) in
  let tl' = cell.prev in
  let hd' = if hd = tl then cell.next else hd in
  let l' = ptrs_in_list (US.v hd') s' in
  let l = ptrs_in_list (US.v hd) s in
  assert (l' = SU.list_remove (US.v tl) l);
  if hd = tl
  then ()
  else (
    assert (Cons? l);
    assert (L.length l >= 2);
    assert (Cons? l');
    mem_and_not_head_implies_prev_not_null (US.v hd) pred s (US.v tl) (US.v tl');
    assert (US.v tl' < Seq.length s);
    assert (hd' = hd);
    lemma_remove_spec2_mem_new_tl pred s hd tl;
    assert (mem (US.v tl') (US.v hd) s');
    next_null_is_last (US.v hd') pred s' (US.v tl')
  )

/// AF: The regular noop does not seem to pick the equality of selectors, not sure why
val noop (#opened:inames) (#p:vprop) (_:unit)
  : SteelGhostF unit opened p (fun _ -> p) (requires fun _ -> True) (ensures fun h0 _ h1 -> h0 p == h1 p)
let noop () = noop ()

/// Create an arraylist with
let intro_arraylist_nil #a #opened
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  intro_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5
      (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))

let lemma_head_not_null_mem
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  noop ()

let lemma_head1_in_bounds
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  noop ()

let lemma_head2_in_bounds
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  noop ()

let lemma_head5_in_bounds
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  noop ()

let lemma_tail5_in_bounds
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  noop ()

let lemma_size5_not_null_implies_bounds
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  noop ()

#push-options "--fuel 1 --ifuel 1"
let lemma_head1_implies_pred1
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  noop ()

let lemma_head2_implies_pred2
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  = noop ()

let lemma_head5_implies_pred5
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  = noop ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_tail5_implies_pred5
  #a #_
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  let gs0 = gget (varraylist pred1 pred2 pred3 pred4 pred5 r
    (US.v hd1) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
  let dl5_as_list = ptrs_in_list #a (US.v hd5) gs0 in
  assert (Cons? dl5_as_list);
  assert (US.v tl5 = L.last dl5_as_list);
  last_mem_lemma #nat dl5_as_list;
  assert (L.mem (US.v tl5) dl5_as_list);
  let dl5_as_set = ptrs_in #a (US.v hd5) gs0 in
  ptrs_in_equal_ptrs_in_list #a (US.v hd5) gs0;
  assert (dl5_as_set == SU.list_to_set dl5_as_list);
  SU.list_to_set_equivmem dl5_as_list (US.v tl5);
  assert (FS.mem (US.v tl5) dl5_as_set);
  lemma_mem_ptrs_in #a (US.v hd5) gs0 (US.v tl5);
  lemma_mem_implies_pred pred5 (US.v hd5) gs0 (US.v tl5)
#pop-options

let permute12
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  elim_vrefine _ _;
  intro_vrefine _ _

let permute13
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  elim_vrefine _ _;
  intro_vrefine _ _

let permute14
  pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5
  =
  elim_vrefine _ _;
  intro_vrefine _ _

//let permute15 pred1 pred2 pred3 pred4 pred5 r hd1 hd2 hd3 hd4 hd5 =
//  elim_vrefine _ _;
//  intro_vrefine _ _

/// Reads at index [idx] in the array.
let read_in_place
  #a #pred1 #pred2 #pred3 #pred4 #pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5 idx
  =
  (**) elim_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 hd5 tl5 sz5);
  let res = A.index r idx in
  (**) intro_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 hd5 tl5 sz5);
  (**) return res.data

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
let remove
  #a #pred1 #pred2 #pred3 #pred4 #pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5 idx
  =
  (**) elim_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5  (US.v hd1) hd2 hd3 hd4 hd5 tl5 sz5);
  (**) let gs0 = gget (A.varray r) in

  // Derive that idx is not in the two other lists, through disjointness and belonging to
  // the first list
  (**) lemma_mem_ptrs_in (US.v hd1) gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd2 gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd3 gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd4 gs0 (US.v idx);
  (**) lemma_mem_ptrs_in hd5 gs0 (US.v idx);

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
  (**) lemma_remove_spec_frame pred1 pred4 (US.v hd1) hd4 gs0 (US.v idx);
  (**) lemma_remove_spec_frame2 pred1 pred5 (US.v hd1) hd5 tl5 gs0 (US.v idx);

  (**) lemma_remove_spec_dataify pred1 (US.v hd1) gs0 (US.v idx);

  (**) intro_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 (US.v hd') hd2 hd3 hd4 hd5 tl5 sz5);
  return hd'

let insert
  #a #pred1 #pred2 #pred3 #pred4 #pred5 r
  hd hd2 hd3 hd4 hd5 tl5 sz5 idx v
  =
  lemma_head1_in_bounds pred1 pred2 pred3 pred4 pred5 r (US.v hd) hd2 hd3 hd4 hd5 tl5 sz5;
  (**) elim_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 (US.v hd) hd2 hd3 hd4 hd5 tl5 sz5);
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
  (**) lemma_insert_spec_frame pred1 pred4 gs0 hd idx hd4 v;
  (**) lemma_insert_spec_frame2 pred1 pred5 gs0 hd idx hd5 tl5 v;

  (**) lemma_insert_spec_dataify pred1 gs0 hd idx v;

  (**) intro_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 (US.v idx) hd2 hd3 hd4 hd5 tl5 sz5)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 75"
let dequeue
  #a #pred1 #pred2 #pred3 #pred4 #pred5 r
  hd5 tl5 sz5 hd1 hd2 hd3 hd4
  =
  (**) elim_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5));
  (**) let gs0 = gget (A.varray r) in

  // Derive that idx is not in the two other lists, through disjointness and belonging to
  // the first list
  (**) lemma_mem_ptrs_in hd1 gs0 (US.v tl5);
  (**) lemma_mem_ptrs_in hd2 gs0 (US.v tl5);
  (**) lemma_mem_ptrs_in hd3 gs0 (US.v tl5);
  (**) lemma_mem_ptrs_in hd4 gs0 (US.v tl5);
  (**) lemma_mem_ptrs_in (US.v hd5) gs0 (US.v tl5);
  ptrs_in_equal_ptrs_in_list (US.v hd5) gs0;
  SU.list_to_set_equivmem (ptrs_in_list (US.v hd5) gs0) (US.v tl5);
  last_mem_lemma (ptrs_in_list (US.v hd5) gs0);

  let cell = A.index r tl5 in
  assert (mem (US.v tl5) (US.v hd5) gs0);
  (**) lemma_mem_valid_or_null_next_prev pred5 (US.v hd5) gs0 (US.v tl5);

  // TODO: edit is_dlist2 accordingly/add corresponding lemma
  // dead code : tl5 is the last cell
  if cell.next <> null_ptr then
    // Next is not null, we need to update it
    let next = A.index r cell.next in
    let next = {next with prev = cell.prev} in
    A.upd r cell.next next
  else noop ();

  let tl' = cell.prev in
  if cell.prev <> null_ptr then
    // Prev is not null, we need to update it
    let prev = A.index r cell.prev in
    let prev = {prev with next = cell.next} in
    A.upd r cell.prev prev
  else noop ();

  (**) let gs1 = gget (A.varray r) in
  assert (gs1 `Seq.equal` remove_spec pred5 (US.v hd5) gs0 null (US.v tl5) FS.emptyset);

  let hd' = if hd5 = tl5 then cell.next else hd5 in
  assert ((hd5 = tl5 /\ tl5 <> null_ptr) ==>
    US.v cell.next = null
  );
  (**) lemma_remove_spec_frame pred5 pred1 (US.v hd5) hd1 gs0 (US.v tl5);
  (**) lemma_remove_spec_frame pred5 pred2 (US.v hd5) hd2 gs0 (US.v tl5);
  (**) lemma_remove_spec_frame pred5 pred3 (US.v hd5) hd3 gs0 (US.v tl5);
  (**) lemma_remove_spec_frame pred5 pred4 (US.v hd5) hd4 gs0 (US.v tl5);
  (**) lemma_remove_spec_dataify pred5 (US.v hd5) gs0 (US.v tl5);

  assert (ptrs_in hd1 gs1 == ptrs_in hd1 gs0);
  assert (ptrs_in hd2 gs1 == ptrs_in hd2 gs0);
  assert (ptrs_in hd3 gs1 == ptrs_in hd3 gs0);
  assert (ptrs_in hd4 gs1 == ptrs_in hd4 gs0);
  assert (dataify gs1 == dataify gs0);

  (**) lemma_remove_spec pred5 (US.v hd5) gs0 (US.v tl5);
  (**) lemma_remove_spec2 pred5 gs0 hd5 tl5;

  let sz' = US.sub sz5 1sz in
  let result : tuple3 = { x = hd'; y = tl'; z = sz' } in
  assert (is_dlist pred5 (US.v hd') gs1);
  assert (hd' = null_ptr ==> tl' = null_ptr);
  assert (hd' <> null_ptr ==> Cons? (ptrs_in_list (US.v hd') gs1));
  assert (is_dlist2 pred5 (US.v hd') (US.v tl') gs1);

  (**) intro_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 (US.v result.x) (US.v result.y) (US.v result.z));
  return result

let enqueue
  #a #pred1 #pred2 #pred3 #pred4 #pred5 r
  hd5 tl5 sz5 hd1 hd2 hd3 hd4 idx v
  =
  //lemma_head1_in_bounds pred1 pred2 pred3 pred4 pred5 r hd1 hd2 hd3 hd4 hd5 tl5 sz5;
  (**) elim_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5));
  (**) let gs0 = gget (A.varray r) in

  let cell = {data = v; prev = null_ptr; next = hd5} in
  A.upd r idx cell;
  if hd5 <> null_ptr then
    let cell = A.index r hd5 in
    let cell = {cell with prev = idx} in
    A.upd r hd5 cell
  else noop ();

  let gs1 = gget (A.varray r) in
  let tl' = if hd5 = null_ptr then idx else tl5 in

  (**) lemma_mem_ptrs_in (US.v hd5) gs0 (US.v idx);
  (**) lemma_insert_spec2 pred5 gs0 hd5 tl5 idx v;
  (**) lemma_insert_spec_frame pred5 pred1 gs0 hd5 idx hd1 v;
  (**) lemma_insert_spec_frame pred5 pred2 gs0 hd5 idx hd2 v;
  (**) lemma_insert_spec_frame pred5 pred3 gs0 hd5 idx hd3 v;
  (**) lemma_insert_spec_frame pred5 pred4 gs0 hd5 idx hd4 v;

  (**) lemma_insert_spec_dataify pred5 gs0 hd5 idx v;

  assert (is_dlist pred5 (US.v idx) gs1);
  assert (idx <> null_ptr);
  assert (idx = null_ptr ==> tl' = null_ptr);
  assert (is_dlist2 pred5 (US.v idx) (US.v tl') gs1);
  let sz' = US.add sz5 1sz in
  (**) intro_vrefine
    (A.varray r)
    (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 (US.v idx) (US.v tl') (US.v sz'));
  let r : tuple2 = { x = tl'; y = sz' } in
  return r
#pop-options

// Part II : extend

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
        ptrs_in_list' hd s visited == ptrs_in_list' hd s' visited /\
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
        ptrs_in_list hd s == ptrs_in_list hd s' /\
        ptrs_in hd s == ptrs_in hd s'
      )
  = lemma_extend_dlist' pred hd s null FS.emptyset s' n

let rec lemma_extend_dlist_notmem' (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev: nat)
  (visited: FS.set nat{Seq.length s >= FS.cardinality visited})
  (n:nat{n >= Seq.length s})
  : Lemma
      (requires
        is_dlist' pred hd s prev visited)
      (ensures
        ~ (mem n hd s)
      )
      (decreases (Seq.length s - FS.cardinality visited))
  =
  if hd = null then ()
  else if FS.cardinality visited = Seq.length s ||
     FS.mem hd visited ||
     // If the prev pointer is not null, it should be in the visited set
     not (prev = null || FS.mem prev visited) ||
     hd >= Seq.length s then ()
  else
    let cur = Seq.index s hd in
    let next = US.v cur.next in
    lemma_extend_dlist_notmem' pred next s hd (FS.insert hd visited) n

let lemma_extend_dlist_notmem (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (n:nat{n >= Seq.length s})
  : Lemma
      (requires
        is_dlist pred hd s)
      (ensures
        ~ (mem n hd s)
      )
  = lemma_extend_dlist_notmem' pred hd s null FS.emptyset n

#restart-solver

let lemma_extend_dlist_notmem_all (#a:Type0)
  (pred1 pred2 pred3 pred4 pred5: a -> prop)
  (hd1 hd2 hd3 hd4 hd5:nat)
  (s:Seq.seq (cell a))
  (l:nat)
  (n:nat)
  : Lemma
      (requires
        is_dlist pred1 hd1 s /\
        is_dlist pred2 hd2 s /\
        is_dlist pred3 hd3 s /\
        is_dlist pred4 hd4 s /\
        is_dlist pred5 hd5 s /\
        Seq.length s == l)
      (ensures
        ~ (mem_all (l + n) hd1 hd2 hd3 hd4 hd5 s)
      )
  =
  let n = l + n in
  lemma_mem_ptrs_in hd1 s n;
  lemma_mem_ptrs_in hd2 s n;
  lemma_mem_ptrs_in hd3 s n;
  lemma_mem_ptrs_in hd4 s n;
  lemma_mem_ptrs_in hd5 s n;
  lemma_extend_dlist_notmem pred1 hd1 s n;
  lemma_extend_dlist_notmem pred2 hd2 s n;
  lemma_extend_dlist_notmem pred3 hd3 s n;
  lemma_extend_dlist_notmem pred4 hd4 s n;
  lemma_extend_dlist_notmem pred5 hd5 s n

let rec lemma_extend_dlist_subset_slice' (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (prev: nat)
  (n:nat{n <= Seq.length s})
  (visited: FS.set nat{n >= FS.cardinality visited})
  : Lemma
      (requires
        is_dlist' pred hd s prev visited)
      (ensures
        FS.subset
          (ptrs_in' hd (Seq.slice s 0 n) visited)
          (ptrs_in' hd s visited)
      )
      (decreases (Seq.length s - FS.cardinality visited))
  =
  if Seq.length s = n then ()
  else
    // no need to go further
    if n = FS.cardinality visited then ()
    else
      if hd = null then ()
      else if FS.cardinality visited = Seq.length s ||
         FS.mem hd visited ||
         // If the prev pointer is not null, it should be in the visited set
         not (prev = null || FS.mem prev visited) ||
         hd >= Seq.length s then ()
      else
        let cur = Seq.index s hd in
        let next = US.v cur.next in
        lemma_extend_dlist_subset_slice' pred next s hd n
          (FS.insert hd visited)

let lemma_extend_dlist_subset_slice (#a:Type0)
  (pred: a -> prop)
  (hd:nat)
  (s:Seq.seq (cell a))
  (n:nat{n <= Seq.length s})
  : Lemma
      (requires
        is_dlist pred hd s)
      (ensures
        FS.subset
          (ptrs_in hd (Seq.slice s 0 n))
          (ptrs_in hd s)
      )
  =
  lemma_extend_dlist_subset_slice' pred hd s null n FS.emptyset

let lemma_extend_dlist_subset_slice_all (#a:Type0)
  (pred1 pred2 pred3 pred4 pred5: a -> prop)
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq (cell a))
  (n:nat)
  : Lemma
      (requires
        is_dlist pred1 hd1 s /\
        is_dlist pred2 hd2 s /\
        is_dlist pred3 hd3 s /\
        is_dlist pred4 hd4 s /\
        is_dlist pred5 hd5 s /\
        n <= Seq.length s)
      (ensures
        ptrs_all hd1 hd2 hd3 hd4 hd5 (Seq.slice s 0 n)
        `FS.subset`
        ptrs_all hd1 hd2 hd3 hd4 hd5 s
      )
  =
  lemma_extend_dlist_subset_slice pred1 hd1 s n;
  lemma_extend_dlist_subset_slice pred2 hd2 s n;
  lemma_extend_dlist_subset_slice pred3 hd3 s n;
  lemma_extend_dlist_subset_slice pred4 hd4 s n;
  lemma_extend_dlist_subset_slice pred5 hd5 s n

// OK

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50 --compat_pre_typed_indexed_effects"
let extend_aux (#a:Type) (#opened:_)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n: US.t)
  (r:A.array (cell a))
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (k:US.t{US.v k + US.v n <= A.length r /\ US.fits (US.v k + US.v n)})
  (v:a)
  : SteelGhost unit opened
  (
    varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r k)
      hd1 hd2 hd3 hd4 hd5 tl5 sz5 `star`
    A.varray (A.split_l (A.split_r r k) n)
  )
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n))
    hd1 hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun _ -> k <> null_ptr /\ pred1 v)
  (ensures fun h0 _ h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 (A.split_l r k) hd1 hd2 hd3 hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 (A.split_l r (k `US.add` n)) hd1 hd2 hd3 hd4 hd5 tl5 sz5) in
    ptrs_in hd1 gs1 == ptrs_in hd1 gs0 /\
    ptrs_in hd2 gs1 == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs1 == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs1 == ptrs_in hd4 gs0 /\
    ptrs_in hd5 gs1 == ptrs_in hd5 gs0 /\
    (forall (j:nat{0 <= j /\ j < US.v n}).
      ~ (mem_all (US.v k + j) hd1 hd2 hd3 hd4 hd5 gs1)
    ) /\
    Seq.slice gs1 0 (US.v k)
    ==
    gs0
  )
  =
  (**) let s0 = gget (varraylist pred1 pred2 pred3 pred4 pred5 (A.split_l r k) hd1 hd2 hd3 hd4 hd5 tl5 sz5) in

  (**) elim_vrefine (A.varray (A.split_l r k)) (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 hd5 tl5 sz5);
  (**) let gs0 = gget (A.varray (A.split_l r k)) in
  (**) let gs0' = gget (A.varray (A.split_l (A.split_r r k) n)) in

  (**) A.ghost_join (A.split_l r k) (A.split_l (A.split_r r k) n) ();
  (**) change_equal_slprop
         (A.varray (A.merge (A.split_l r k) (A.split_l (A.split_r r k) n)))
         (A.varray (A.split_l r (k `US.add` n)));

  (**) let gs1 = gget (A.varray (A.split_l r (k `US.add` n))) in
  assert (gs1 `Seq.equal` Seq.append gs0 gs0');
  Seq.lemma_split gs0 (US.v k);
  assert (G.reveal gs0 `Seq.equal` Seq.slice (G.reveal gs1) 0 (US.v k));

  //Seq.slice_slice
  (**) lemma_extend_dlist pred1 hd1 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) lemma_extend_dlist pred2 hd2 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) lemma_extend_dlist pred3 hd3 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) lemma_extend_dlist pred4 hd4 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) lemma_extend_dlist pred5 hd5 (Ghost.reveal gs0) (Ghost.reveal gs1) (US.v k);
  (**) assert (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 hd5 tl5 sz5 (Ghost.reveal gs1));

  (**) lemma_mem_ptrs_in hd1 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd2 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd3 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd4 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd5 (Ghost.reveal gs0) (US.v k);
  (**) lemma_mem_ptrs_in hd1 (Ghost.reveal gs1) (US.v k);
  (**) lemma_mem_ptrs_in hd2 (Ghost.reveal gs1) (US.v k);
  (**) lemma_mem_ptrs_in hd3 (Ghost.reveal gs1) (US.v k);
  (**) lemma_mem_ptrs_in hd4 (Ghost.reveal gs1) (US.v k);
  (**) lemma_mem_ptrs_in hd5 (Ghost.reveal gs1) (US.v k);
  (**) assert (~ (mem_all (US.v k) hd1 hd2 hd3 hd4 hd5 gs1));

  (**) intro_vrefine (A.varray (A.split_l r (k `US.add` n))) (varraylist_refine pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 hd5 tl5 sz5);

  (**) let s1 = gget (varraylist pred1 pred2 pred3 pred4 pred5 (A.split_l r (k `US.add` n)) hd1 hd2 hd3 hd4 hd5 tl5 sz5) in
  // Derived from the postcondition of join
  (**) assert (Ghost.reveal s0 `Seq.equal` Seq.slice #(cell a) (Ghost.reveal s1) 0 (US.v k));
  Classical.forall_intro (Classical.move_requires (
    lemma_extend_dlist_notmem_all pred1 pred2 pred3 pred4 pred5 hd1 hd2 hd3 hd4 hd5 s0 (US.v k)
  ));
  assert (
    forall (j:nat{0 <= j /\ j < US.v n}).
      ~ (mem_all #a (US.v k + j) hd1 hd2 hd3 hd4 hd5 (Seq.slice #(cell a) (G.reveal s1) 0 (US.v k)))
  )
  //// Move the slice out of dataify
  //(**) dataify_slice #a (Ghost.reveal s1) (US.v k)
#pop-options

#restart-solver

//set_aux bound1 bound2 i
//retourne l'ensemble [bound1, i[

let rec set_aux (bound1 bound2: nat) (i: nat)
  : Pure (G.erased (FS.set nat))
  (requires bound1 <= bound2 /\ bound1 <= i /\ i <= bound2)
  (ensures fun r ->
    forall (k:nat{bound1 <= k /\ k < i}). FS.mem k r
  )
  (decreases (i - bound1))
  = match (i - bound1) with
  | 0 -> FS.emptyset
  | _ ->
      let s' = set_aux bound1 bound2 (i-1) in
      FS.insert (i-1) s'

let set (bound1 bound2: nat)
  : Pure (G.erased (FS.set nat))
  (requires bound1 <= bound2)
  (ensures fun r ->
    forall (k:nat{bound1 <= k /\ k < bound2}). FS.mem k r
  )
  = set_aux bound1 bound2 bound2

open Steel.Loops

#restart-solver

open Utils2


#restart-solver

//#reset-options "--fuel 1 --ifuel 1"

open Config

#restart-solver

#push-options "--compat_pre_typed_indexed_effects --query_stats --z3rlimit 50"
inline_for_extraction noextract
let extend_insert_aux (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (r: A.array (cell a))
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (i: US.t{0 <= US.v i /\ US.v i < US.v n2})
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (v1: a)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    //(US.v i + 1) hd2 hd3 hd4)
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5) in
    pred1 v1 /\
    A.length r <= US.v metadata_max /\
    (forall (j:nat{US.v i + 1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i) hd2 hd3 hd4 hd5 gs0))
  )
  (ensures fun h0 _ h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5) in
    ptrs_in (US.v k + US.v i + 1) gs1 ==
      FS.insert (US.v k + US.v i + 1) (ptrs_in (US.v k + US.v i) gs0) /\
    ptrs_in hd2 gs1 == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs1 == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs1 == ptrs_in hd4 gs0 /\
    ptrs_in hd5 gs1 == ptrs_in hd5 gs0 /\
    dataify gs1 == Seq.upd (dataify gs0) (US.v k + US.v i + 1) v1 /\
    (forall (j:nat{US.v i + 1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i) hd2 hd3 hd4 hd5 gs0)) /\
    (forall (j:nat{US.v i + 1 < j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 gs1))
  )
  =
  let gs0 = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5) in
  assert (US.v i + 1 >= US.v i + 1);
  assert (US.v i + 1 < US.v n1);
  assert (~ (mem_all #a (US.v k + (US.v i + 1)) (US.v k + US.v i) hd2 hd3 hd4 hd5 (G.reveal gs0)));
  change_slprop_rel
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5)
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v (US.add k i)) hd2 hd3 hd4 hd5 tl5 sz5)
    (fun x y -> x == y)
    (fun _ -> assert (US.v (US.add k i) == US.v k + US.v i));
  let gs0' = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v (US.add k i)) hd2 hd3 hd4 hd5 tl5 sz5) in
  assert (Seq.equal #a (dataify gs0) (dataify gs0'));
  insert #a #pred1 #pred2 #pred3 #pred4 #pred5
    (A.split_l r (k `US.add` n1))
    (US.add k i) hd2 hd3 hd4 hd5 tl5 sz5 (US.add (US.add k i) 1sz) v1;
  let gs1 = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v (US.add (US.add k i) 1sz)) hd2 hd3 hd4 hd5 tl5 sz5) in
  change_slprop_rel
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v (US.add (US.add k i) 1sz)) hd2 hd3 hd4 hd5 tl5 sz5)
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5)
    (fun x y -> x == y)
    (fun _ -> assert (US.v (US.add (US.add k i) 1sz) == US.v k + US.v i + 1));
  let gs1' = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5) in
  assert (Seq.equal #a (dataify gs1) (dataify gs1'));
  return ()

#restart-solver

let rec set_aux_lemma (bound bound1 bound2: nat) (i: nat)
  : Lemma
  (requires bound <= i /\ i <= bound1 /\ bound1 <= bound2)
  (ensures
    set_aux bound bound1 i == set_aux bound bound2 i
  )
  = match (i - bound) with
  | 0 -> ()
  | _ -> set_aux_lemma bound bound1 bound2 (i-1)

let lemma_union_set
  (k i: nat)
  (s0 s1 s2: FS.set nat)
  : Lemma
  (requires
    s1 `FS.equal` FS.union (set k (k+i+1)) s0 /\
    s2 `FS.equal` FS.insert (k+i+1) s1)
  (ensures
    s2 `FS.equal` FS.union (set k (k+i+2)) s0)
  =
  set_aux_lemma k (k+i+1) (k+i+2) (k+i+1)

//TODO: move to SeqUtils
let lemma_index_create (#a:Type) (n:nat) (v:a) (i:nat{i < n})
  : Lemma
  (requires True)
  (ensures (Seq.index (Seq.create n v) i == v))
  = Seq.lemma_index_create n v i

//TODO: move to SeqUtils
let lemma_create_append (#a: Type)
  (k1 k2: nat)
  (v: a)
  : Lemma
  (Seq.append (Seq.create k1 v) (Seq.create k2 v)
  == Seq.create (k1+k2) v)
  =
  Classical.forall_intro (lemma_index_create k1 v);
  Classical.forall_intro (lemma_index_create k2 v);
  Classical.forall_intro (lemma_index_create (k1+k2) v);
  Seq.lemma_split (Seq.create (k1+k2) v) k1;
  Seq.lemma_eq_intro
    (Seq.append (Seq.create k1 v) (Seq.create k2 v))
    (Seq.create (k1+k2) v)

let lemma_upd_is_append (#a: Type0)
  (k i: nat)
  (s0 s1 s2: Seq.seq a)
  (v1: a)
  : Lemma
  (requires
    Seq.length s1 == Seq.length s0 /\
    Seq.length s2 == Seq.length s0 /\
    k + i + 1 < Seq.length s0 /\
    Seq.slice s1 0 (k + i + 1)
    == Seq.append (Seq.slice s0 0 (k+1)) (Seq.create i v1) /\
    s2 == Seq.upd s1 (k + i + 1) v1
  )
  (ensures
    Seq.slice s2 0 (k + i + 2)
    == Seq.append (Seq.slice s0 0 (k+1)) (Seq.create (i+1) v1)
  )
  =
  // #1 Seq.slice s1 0 (k+i+1)
  // decomposition as slices [0, k+1[ + [k+1, k+i[
  Seq.slice_slice s1 0 (k+i+1) 0 k;
  Seq.slice_slice s1 0 (k+i+1) k (k+i+1);
  Seq.lemma_split (Seq.slice s1 0 (k+i+1)) (k+1);
  assert (Seq.slice s1 0 (k+i+1) == Seq.append
    (Seq.slice s1 0 (k+1))
    (Seq.slice s1 (k+1) (k+i+1))
  );
  Seq.lemma_append_inj
    (Seq.slice s1 0 (k+1))
    (Seq.slice s1 (k+1) (k+i+1))
    (Seq.slice s0 0 (k+1))
    (Seq.create i v1);
  assert (Seq.slice s1 0 (k+1) == Seq.slice s0 0 (k+1));
  assert (Seq.slice s1 (k+1) (k+i+1) == Seq.create i v1);

  // #2 Seq.slice s2 0 (k+i)
  // decomposition as slices [0, k+1[ + [k+1, k+i[
  assert (Seq.slice s2 0 (k+i+1) == Seq.slice s1 0 (k+i+1));
  Seq.slice_slice s2 0 (k+i+1) 0 (k+1);
  assert (Seq.slice s2 0 (k+1) == Seq.slice s0 0 (k+1));
  Seq.slice_slice s2 0 (k+i+1) (k+1) (k+i+1);
  assert (Seq.slice s2 (k+1) (k+i+1) == Seq.create i v1);

  // last step
  assert (Seq.index s2 (k+i+1) == v1);
  Seq.lemma_index_slice s2 (k+1) (k+i+2) i;
  assert (Seq.index (Seq.slice s2 (k+1) (k+i+2)) i == v1);
  Seq.slice_slice s2 (k+1) (k+i+2) i (i+1);
  Seq.lemma_eq_intro
    (Seq.slice (Seq.slice s2 (k+1) (k+i+2)) i (i+1))
    (Seq.create 1 v1);
  assert (Seq.slice (Seq.slice s2 (k+1) (k+i+2)) i (i+1) == Seq.create 1 v1);
  Seq.lemma_split (Seq.slice s2 (k+1) (k+i+2)) i;
  assert (Seq.slice s2 (k+1) (k+i+2) == Seq.append
    (Seq.create i v1)
    (Seq.create 1 v1));
  lemma_create_append i 1 v1;
  assert (Seq.slice s2 (k+1) (k+i+2) == Seq.create (i+1) v1);
  Seq.lemma_split (Seq.slice s2 0 (k+i+2)) (k+1);
  ()

inline_for_extraction noextract
let extend_insert_aux2 (#a: Type0)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (r: A.array (cell a){A.length r <= US.v metadata_max})
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (i: US.t{0 <= US.v i /\ US.v i < US.v n2})
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (v1: a{pred1 v1})
  (gs0: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun h ->
    let gs = h (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5) in
    ptrs_in #a (US.v k + US.v i) gs
      == FS.union
        (set (US.v k) (US.v k + US.v i + 1))
        (ptrs_in #a (US.v k) gs0) /\
    ptrs_in hd2 gs == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs == ptrs_in hd4 gs0 /\
    ptrs_in hd5 gs == ptrs_in hd5 gs0 /\
    Seq.slice (dataify gs) 0 (US.v k + US.v i + 1)
    == Seq.append
      (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v i) v1) /\
    (forall (j:nat{US.v i + 1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i) hd2 hd3 hd4 hd5 gs))
  )
  (ensures fun h0 _ h1 ->
    let old_gs = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5) in
    let gs = h1 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5) in
    ptrs_in #a (US.v k + US.v i + 1) gs
      == FS.union
        (set (US.v k) (US.v k + US.v i + 2))
        (ptrs_in #a (US.v k) gs0) /\
    ptrs_in hd2 gs == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs == ptrs_in hd4 gs0 /\
    ptrs_in hd5 gs == ptrs_in hd5 gs0 /\
    ptrs_in #a (US.v k + US.v i + 1) gs
      == FS.insert
        (US.v k + US.v i + 1)
        (ptrs_in #a (US.v k + US.v i) old_gs) /\
    ptrs_in hd2 gs == ptrs_in hd2 old_gs /\
    ptrs_in hd3 gs == ptrs_in hd3 old_gs /\
    ptrs_in hd4 gs == ptrs_in hd4 old_gs /\
    ptrs_in hd5 gs == ptrs_in hd5 old_gs /\
    (forall (j:nat{US.v i + 1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i) hd2 hd3 hd4 hd5 old_gs)) /\
    (forall (j:nat{US.v i + 2 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 gs)) /\
    Seq.slice (dataify old_gs) 0 (US.v k + US.v i + 1)
    == Seq.append
      (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v i) v1) /\
    dataify gs == Seq.upd (dataify old_gs) (US.v k + US.v i + 1) v1 /\
    Seq.slice (dataify gs) 0 (US.v k + US.v i + 2)
    == Seq.append
      (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v i + 1) v1) /\
    True
  )
  =
  let gs1 = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5) in
  extend_insert_aux #a #pred1 #pred2 #pred3 #pred4 #pred5
    r n1 n2 k i hd2 hd3 hd4 hd5 tl5 sz5 v1;
  let gs2 = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5) in
  assert (ptrs_in #a (US.v k + US.v i + 1) gs2 `FS.equal`
       FS.insert (US.v k + US.v i + 1)
         (ptrs_in #a (US.v k + US.v i) gs1));
  lemma_union_set (US.v k) (US.v i)
    (ptrs_in #a (US.v k) gs0)
    (ptrs_in #a (US.v k + US.v i) gs1)
    (ptrs_in #a (US.v k + US.v i + 1) gs2);
  lemma_upd_is_append (US.v k) (US.v i)
    (dataify gs0)
    (dataify gs1)
    (dataify gs2)
    v1;
  ()

inline_for_extraction noextract
let extend_insert_aux3 (#a: Type0)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (r: A.array (cell a){A.length r <= US.v metadata_max})
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (i: US.t{0 <= US.v i /\ US.v i < US.v n2})
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (v1: a{pred1 v1})
  (gs0: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun h ->
    let gs = h (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i) hd2 hd3 hd4 hd5 tl5 sz5) in
    ptrs_in #a (US.v k + US.v i) gs
      == FS.union
        (set (US.v k) (US.v k + US.v i + 1))
        (ptrs_in #a (US.v k) gs0) /\
    ptrs_in hd2 gs == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs == ptrs_in hd4 gs0 /\
    ptrs_in hd5 gs == ptrs_in hd5 gs0 /\
    Seq.slice (dataify gs) 0 (US.v k + US.v i + 1)
    == Seq.append
      (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v i) v1) /\
    (forall (j:nat{US.v i + 1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i) hd2 hd3 hd4 hd5 gs))
  )
  (ensures fun _ _ h1 ->
    let gs = h1 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5) in
    ptrs_in #a (US.v k + US.v i + 1) gs
      == FS.union
        (set (US.v k) (US.v k + US.v i + 2))
        (ptrs_in #a (US.v k) gs0) /\
    ptrs_in hd2 gs == ptrs_in hd2 gs0 /\
    ptrs_in hd3 gs == ptrs_in hd3 gs0 /\
    ptrs_in hd4 gs == ptrs_in hd4 gs0 /\
    ptrs_in hd5 gs == ptrs_in hd5 gs0 /\
    Seq.slice (dataify gs) 0 (US.v k + US.v i + 2)
    == Seq.append
      (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v i + 1) v1) /\
    (forall (j:nat{US.v i + 2 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 gs)) /\
    True
  )
  =
  extend_insert_aux2 #a #pred1 #pred2 #pred3 #pred4 #pred5
    r n1 n2 k i hd2 hd3 hd4 hd5 tl5 sz5 v1 gs0

let slpred
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (i: nat{0 <= i /\ i <= US.v n2})
  : vprop
  =
  varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5

let varraylist_type (#a:Type) (pred1 pred2 pred3 pred4 pred5: a -> prop) (r:A.array (cell a)) (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  : Lemma
  (t_of (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 hd5 tl5 sz5)
  == (x:Seq.lseq (cell a) (A.length r){
    varraylist_refine pred1 pred2 pred3 pred4 pred5
      hd1 hd2 hd3 hd4 hd5 tl5 sz5 x
  }))
  =
  assert_norm (t_of (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 hd5 tl5 sz5)
  == (x:Seq.lseq (cell a) (A.length r){
    varraylist_refine pred1 pred2 pred3 pred4 pred5
      hd1 hd2 hd3 hd4 hd5 tl5 sz5 x
  }))

let slpred_type
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (i: nat{0 <= i /\ i <= US.v n2})
  : Lemma
  (t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i)
  == (x:Seq.lseq (cell a)
    (US.v (k `US.add` n1))
    {
    varraylist_refine pred1 pred2 pred3 pred4 pred5 (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5 x
  }))
  =
  assert (t_of (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5)
  ==
  t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i));
  varraylist_type #a pred1 pred2 pred3 pred4 pred5 (A.split_l r (k `US.add` n1)) (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5;
  assert (A.length (A.split_l r (k `US.add` n1)) == US.v (k `US.add` n1));
  assert_norm (
    (x:Seq.lseq (cell a) (US.v (k `US.add` n1)){
      varraylist_refine pred1 pred2 pred3 pred4 pred5 (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5 x
    })
    ==
    (x:Seq.lseq (cell a) (A.length (A.split_l r (k `US.add` n1))){
      varraylist_refine pred1 pred2 pred3 pred4 pred5 (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5 x
    })
  )

module SM = Steel.Memory

let varraylist_to_varraylist_lemma
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (r: A.array (cell a))
  (x1 x2 x3 x4 x5 x6 x7: G.erased nat)
  (y1 y2 y3 y4 y5 y6 y7: G.erased nat)
  (m: SM.mem)
  : Lemma
  (requires
    x1 == y1 /\
    x2 == y2 /\
    x3 == y3 /\
    x4 == y4 /\
    x5 == y5 /\
    x6 == y6 /\
    x7 == y7 /\
    SM.interp (hp_of (
      varraylist pred1 pred2 pred3 pred4 pred5 r
        x1 x2 x3 x4 x5 x6 x7
    )) m
  )
  (ensures
    SM.interp (hp_of (
      varraylist pred1 pred2 pred3 pred4 pred5 r
        y1 y2 y3 y4 y5 y6 y7
    )) m /\
    sel_of (
      varraylist pred1 pred2 pred3 pred4 pred5 r
        y1 y2 y3 y4 y5 y6 y7
    ) m
    ==
    sel_of (
      varraylist pred1 pred2 pred3 pred4 pred5 r
        x1 x2 x3 x4 x5 x6 x7
    ) m
  )
  = ()

let varraylist_to_slpred_lemma
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (i: nat{0 <= i /\ i <= US.v n2})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      varraylist pred1 pred2 pred3 pred4 pred5
        (A.split_l r (k `US.add` n1))
        (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5
    )) m
  )
  (ensures
    SM.interp (hp_of (
      slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i
    )) m /\
    sel_of (
      slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i
    ) m
    ==
    sel_of (
      varraylist pred1 pred2 pred3 pred4 pred5
        (A.split_l r (k `US.add` n1))
        (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5
    ) m
  )
  = ()

let slpred_to_varraylist_lemma
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (i: nat{0 <= i /\ i <= US.v n2})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i
    )) m
  )
  (ensures
    SM.interp (hp_of (
      varraylist pred1 pred2 pred3 pred4 pred5
        (A.split_l r (k `US.add` n1))
        (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5
    )) m /\
    sel_of (
      slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i
    ) m
    ==
    sel_of (
      varraylist pred1 pred2 pred3 pred4 pred5
        (A.split_l r (k `US.add` n1))
        (US.v k + i) hd2 hd3 hd4 hd5 tl5 sz5
    ) m
  )
  = ()

let selpred
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (v1: a{pred1 v1})
  (gs0: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  (i: nat{0 <= i /\ i <= US.v n2})
  //(gs: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  (gs: t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i))
  : prop
  =
  ptrs_in #a (US.v k + i) gs
    == FS.union
      (set (US.v k) (US.v k + i + 1))
      (ptrs_in #a (US.v k) gs0) /\
  ptrs_in #a hd2 gs == ptrs_in #a hd2 gs0 /\
  ptrs_in #a hd3 gs == ptrs_in #a hd3 gs0 /\
  ptrs_in #a hd4 gs == ptrs_in #a hd4 gs0 /\
  ptrs_in #a hd5 gs == ptrs_in #a hd5 gs0 /\
  Seq.slice (dataify gs) 0 (US.v k + i + 1)
  == Seq.append
    (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
    (Seq.create i v1) /\
  (forall (j:nat{i + 1 <= j /\ j < US.v n1}).
    ~ (mem_all #a (US.v k + j) (US.v k + i) hd2 hd3 hd4 hd5 gs))

let selpred2
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (v1: a{pred1 v1})
  (gs0: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  (i: nat{0 <= i /\ i <= US.v n2})
  (gs: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  : prop
  =
  ptrs_in #a (US.v k + i) gs
    == FS.union
      (set (US.v k) (US.v k + i + 1))
      (ptrs_in #a (US.v k) gs0) /\
  ptrs_in #a hd2 gs == ptrs_in #a hd2 gs0 /\
  ptrs_in #a hd3 gs == ptrs_in #a hd3 gs0 /\
  ptrs_in #a hd4 gs == ptrs_in #a hd4 gs0 /\
  ptrs_in #a hd5 gs == ptrs_in #a hd5 gs0 /\
  Seq.slice (dataify gs) 0 (US.v k + i + 1)
  == Seq.append
    (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
    (Seq.create i v1) /\
  (forall (j:nat{i + 1 <= j /\ j < US.v n1}).
    ~ (mem_all #a (US.v k + j) (US.v k + i) hd2 hd3 hd4 hd5 gs))

#restart-solver

let selpred_equiv_selpred2
  (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (v1: a{pred1 v1})
  (gs0: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  (i: nat{0 <= i /\ i <= US.v n2})
  (gs1: t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k i))
  (gs2: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  : Lemma
  (requires G.reveal gs2 == gs1)
  (ensures
  selpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k v1 gs0 i gs1
  <==>
  selpred2 #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k v1 gs0 i gs2)
  =
  ()

#restart-solver

inline_for_extraction noextract
let extend_insert_aux4_aux (#a: Type) (#opened: _)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (r: A.array (cell a){A.length r <= US.v metadata_max})
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (v1: a{pred1 v1})
  (gs0: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  (i: US.t{0 <= US.v i /\ US.v i < US.v n2})
  : SteelGhost unit opened
  (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5)
  (fun _ -> slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    let x = h0 ((varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5)) in
    let y = h1 (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1)) in
    slpred_type #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1);
    let x : t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1)) = x in
    x == y
  )
  =
  change_slprop_rel
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5)
    (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1))
    (fun x y ->
      ///let x : Seq.lseq (cell a) (US.v (k `US.add` n1)) = x in
      slpred_type #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1);
      let x : t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1)) = x in
      x == y)
    (fun m ->
      varraylist_to_slpred_lemma #a
      #pred1 #pred2 #pred3 #pred4 #pred5
      n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5
      k (US.v i + 1) m
    )

#restart-solver

inline_for_extraction noextract
val extend_insert_aux4 (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (r: A.array (cell a){A.length r <= US.v metadata_max})
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1)})
  (hd2 hd3 hd4 hd5 tl5 sz5: G.erased nat)
  (v1: a{pred1 v1})
  (gs0: G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1))))
  (i: US.t{0 <= US.v i /\ US.v i < US.v n2})
  : Steel unit
  (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i))
  (fun _ -> slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1))
  (requires fun h ->
    selpred #a #pred1 #pred2 #pred3 #pred4 #pred5
      n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k
      v1 gs0
      (US.v i)
      (h (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i)))
  )
  (ensures fun h0 _ h1 ->
    selpred #a #pred1 #pred2 #pred3 #pred4 #pred5
      n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k
      v1 gs0
      (US.v i)
      (h0 (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i)))
    /\
    selpred #a #pred1 #pred2 #pred3 #pred4 #pred5
      n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k
      v1 gs0
      (US.v i + 1)
      (h1 (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1)))
  )

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 400 --fuel 2 --ifuel 2"
let extend_insert_aux4 #a
  #pred1 #pred2 #pred3 #pred4 #pred5
  r n1 n2 k hd2 hd3 hd4 hd5 tl5 sz5 v1 gs0 i
  =
  let gs1 = gget (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i)) in
  assert (selpred #a #pred1 #pred2 #pred3 #pred4 #pred5
      n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k
      v1 gs0
      (US.v i)
      (G.reveal gs1));
  extend_insert_aux3 #a #pred1 #pred2 #pred3 #pred4 #pred5
    r n1 n2 k i hd2 hd3 hd4 hd5 tl5 sz5 v1 gs0;
  varraylist_type pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5;
  slpred_type #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1);
  let gs2
  : G.erased (t_of (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5))
  = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v i + 1) hd2 hd3 hd4 hd5 tl5 sz5) in
  let gs21
  : G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1)))
  = G.hide (G.reveal gs2 <: Seq.lseq (cell a) (US.v (k `US.add` n1))) in
  let gs22
  : G.erased (t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1)))
  = G.hide (G.reveal gs21 <: t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1))) in
  selpred_equiv_selpred2 #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k v1 gs0 (US.v i + 1) (G.reveal gs22) gs21;
  assert (selpred #a #pred1 #pred2 #pred3 #pred4 #pred5
    n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k
    v1 gs0
    (US.v i + 1)
    (G.reveal gs22));
  extend_insert_aux4_aux r n1 n2 k hd2 hd3 hd4 hd5 tl5 sz5 v1 gs0 i;
  let gs3
  : G.erased (t_of (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1)))
  = gget (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k (US.v i + 1)) in
  assert (selpred #a #pred1 #pred2 #pred3 #pred4 #pred5
    n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k
    v1 gs0
    (US.v i + 1)
    (G.reveal gs22));
  assert (G.reveal gs22 == G.reveal gs3);
  assert (selpred #a #pred1 #pred2 #pred3 #pred4 #pred5
    n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k
    v1 gs0
    (US.v i + 1)
    (G.reveal gs3));
  ()
#pop-options

#restart-solver

//TODO: move to SeqUtils
let append_null_is_eq (#a: Type)
  (s: Seq.seq a)
  : Lemma
  (s == Seq.append s Seq.empty)
  =
  Seq.lemma_split s (Seq.length s)

//TODO: dedicated set lib?
let lemma_set_singleton
  (k: nat)
  : Lemma
  (G.reveal (set k (k+1)) == FS.singleton k)
  =
  assert (set k (k+1) == set_aux k (k+1) (k+1));
  let s' = set_aux k (k+1) k in
  assert (s' `FS.equal` FS.emptyset);
  let s = FS.insert k s' in
  assert (s `FS.equal` FS.singleton k);
  assert (set_aux k (k+1) (k+1) == G.hide s)

//TODO: dedicated set lib
let lemma_set_union
  (#a: eqtype)
  (s: FS.set a)
  (v: a)
  : Lemma
  (requires FS.mem v s)
  (ensures FS.union (FS.singleton v) s == s)
  =
  assert (s `FS.equal` FS.union (FS.singleton v) s)

#push-options "--compat_pre_typed_indexed_effects --fuel 1 --ifuel 1"
let extend_insert (#a: Type)
  (#pred1 #pred2 #pred3 #pred4 #pred5: a -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array (cell a))
  (hd2 hd3 hd4 hd5 tl5 sz5: US.t)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1) /\ k <> null_ptr})
  (v1: a)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
    pred1 v1 /\
    A.length r <= US.v metadata_max /\
    (forall (j:nat{1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) gs0))
  )
  (ensures fun h0 _ h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
    //False /\
    ptrs_in (US.v k + US.v n2) gs1
    == FS.union
      (set (US.v k) (US.v k + US.v n2 + 1))
      (ptrs_in (US.v k) gs0) /\
    ptrs_in (US.v hd2) gs1 == ptrs_in (US.v hd2) gs0 /\
    ptrs_in (US.v hd3) gs1 == ptrs_in (US.v hd3) gs0 /\
    ptrs_in (US.v hd4) gs1 == ptrs_in (US.v hd4) gs0 /\
    ptrs_in (US.v hd5) gs1 == ptrs_in (US.v hd5) gs0 /\
    Seq.slice (dataify gs1) 0 (US.v k + US.v n2 + 1)
    == Seq.append
      (Seq.slice (G.reveal (dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v n2) v1) /\
    (forall (j:nat{US.v n2 + 1 <= j /\ j < US.v n1}).
      ~ (mem_all (US.v k + j) (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) gs1)) /\
    True
  )
  =
  lemma_head_not_null_mem #a pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    k hd2 hd3 hd4 hd5 tl5 sz5;
  change_slprop_rel
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + 0) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
    (fun x y -> x == y)
    (fun m ->
      varraylist_to_varraylist_lemma #a
        #pred1 #pred2 #pred3 #pred4 #pred5
        (A.split_l r (k `US.add` n1))
        (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)
        (US.v k + 0) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)
        m
    );
  varraylist_type pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + 0) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5);
  let gs0
  : G.erased (t_of (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + 0) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)))
  = gget (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + 0) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
  let gs0
  : G.erased (Seq.lseq (cell a) (US.v (k `US.add` n1)))
  = G.hide (G.reveal gs0 <: Seq.lseq (cell a) (US.v (k `US.add` n1))) in
  Seq.lemma_empty (Seq.create 0 v1);
  append_null_is_eq #a (Seq.slice (dataify gs0) 0 (US.v k + 1));
  assert (Seq.slice (dataify gs0) 0 (US.v k + 1)
  == Seq.append
    (Seq.slice (dataify gs0) 0 (US.v k + 1))
    (Seq.create 0 v1));
  lemma_set_singleton (US.v k);
  lemma_mem_ptrs_in #a (US.v k) (G.reveal gs0) (US.v k);
  assert (FS.mem (US.v k) (ptrs_in #a (US.v k) gs0));
  lemma_set_union (ptrs_in #a (US.v k) gs0) (US.v k);
  assert (ptrs_in #a (US.v k) gs0
    == FS.union
      (set (US.v k) (US.v k + 1))
      (ptrs_in #a (US.v k) gs0));
  assert (selpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5) k v1 (G.reveal gs0) 0 (G.reveal gs0));
  change_slprop_rel
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + 0) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
    (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5) k 0)
    (fun x y -> x == y)
    (fun m ->
      varraylist_to_slpred_lemma #a
      #pred1 #pred2 #pred3 #pred4 #pred5
      n1 n2 r (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)
      k 0 m
    );
  for_loop_full
    0sz n2
    (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5) k)
    (selpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5) k v1 (G.reveal gs0))
    (extend_insert_aux4 #a #pred1 #pred2 #pred3 #pred4 #pred5 r n1 n2 k (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5) v1 gs0);
  change_slprop_rel
    (slpred #a #pred1 #pred2 #pred3 #pred4 #pred5 n1 n2 r (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5) k (US.v n2))
    (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
    (fun x y -> x == y)
    (fun m ->
      slpred_to_varraylist_lemma #a
      #pred1 #pred2 #pred3 #pred4 #pred5
      n1 n2 r (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)
      k (US.v n2) m
    )
