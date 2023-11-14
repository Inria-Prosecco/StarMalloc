module SetUtils

module L = FStar.List.Tot
module FS = FStar.FiniteSet.Base
open FStar.FiniteSet.Ambient

(* List to Set *)

let rec list_to_set (#a: eqtype)
  (l: list a{FS.list_nonrepeating l})
  : FS.set a
  = match l with
  | [] -> FS.emptyset
  | x::t -> FS.insert x (list_to_set t)

let rec list_to_set_union (#a: eqtype)
  (l1 l2: (l:list a{FS.list_nonrepeating l}))
  : Lemma
  (requires
    FS.list_nonrepeating (l1@l2)
  )
  (ensures
    list_to_set (l1@l2) == FS.union (list_to_set l1) (list_to_set l2)
  )
  (decreases %[L.length l1 ; L.length l2])
  =
  let s1 = list_to_set l1 in
  let s2 = list_to_set l2 in
  match l1 with
  | [] ->
      assert (l1@l2 == l2);
      assert (s1 `FS.equal` FS.emptyset #a);
      assert (FS.union s1 s2 `FS.equal` s2)
  | [x] ->
      assert (l1@l2 == x::l2);
      assert (s1 `FS.equal` FS.singleton x);
      assert (FS.union s1 s2 `FS.equal` FS.insert x s2)
  | x::t ->
      list_to_set_union t l2;
      list_to_set_union [x] (t@l2);
      assert (list_to_set (l1@l2) `FS.equal` (FS.union (list_to_set l1) (list_to_set l2)))

let lift_or (b1 b2 b3: bool)
  : Lemma
  (requires b1 <==> b2 \/ b3)
  (ensures b1 = b2 || b3)
  = ()

let rec list_to_set_equivmem (#a: eqtype)
  (l: list a{FS.list_nonrepeating l})
  (e: a)
  : Lemma
  (ensures L.mem e l = FS.mem e (list_to_set l))
  (decreases L.length l)
  = match l with
  | [] -> ()
  | [x] -> ()
  | x::t ->
      list_to_set_union [x] t;
      lift_or
        (FS.mem e (list_to_set l))
        (FS.mem e (list_to_set [x]))
        (FS.mem e (list_to_set t));
      assert (FS.mem e (list_to_set l) = FS.mem e (list_to_set [x]) || FS.mem e (list_to_set t));
      list_to_set_equivmem t e;
      list_to_set_equivmem [x] e;
      assert (FS.mem e (list_to_set l) = L.mem e [x] || L.mem e t)

let rec list_to_set_card (#a: eqtype)
  (l: list a{FS.list_nonrepeating l})
  : Lemma
  (L.length l = FS.cardinality (list_to_set l))
  = match l with
  | [] -> ()
  | x::t ->
      let s1 = list_to_set [x] in
      let s2 = list_to_set t in
      list_to_set_union [x] t;
      assert (list_to_set l == FS.union s1 s2);
      assert (not (L.mem x t));
      list_to_set_equivmem t x;
      assert (not (FS.mem x s2));
      list_to_set_card t

let list_to_set_empty (#a: eqtype)
  : Lemma
  (list_to_set [] == FS.emptyset #a)
  = ()

let list_to_set_singleton (#a: eqtype) (x: a)
  : Lemma
  (list_to_set [x] == FS.singleton x)
  =
  assert (FS.insert x FS.emptyset `FS.equal` FS.singleton x)

(* Seq to List *)

module S = FStar.Seq

let _seq_to_list_append (#a: eqtype) (s1 s2: Seq.seq a)
  : Lemma
  (
  Seq.seq_to_list (Seq.append s1 s2)
  ==
  L.append (Seq.seq_to_list s1) (Seq.seq_to_list s2)
  )
  = SeqUtils.lemma_seq_to_list_append s1 s2

let seq_to_list_append (#a: eqtype) (s: Seq.seq a) (v: a)
  : Lemma
  (Seq.seq_to_list (Seq.append s (Seq.create 1 v))
  ==
  (Seq.seq_to_list s)@[v])
  =
  _seq_to_list_append
    s
    (Seq.create 1 v)

let seq_to_list_remove (#a: eqtype) (s: Seq.seq a) (v: a)
  : Lemma
  (requires Seq.length s > 0)
  (ensures
    Seq.seq_to_list (Seq.append (Seq.create 1 v) s)
    ==
    v::(Seq.seq_to_list s)
  )
  =
  _seq_to_list_append
    (Seq.create 1 v)
    s

let seq_nonrepeating (#a: eqtype) (s: Seq.seq a) : bool
  = FS.list_nonrepeating (Seq.seq_to_list s)

(* Seq to Set *)

let seq_to_set (#a: eqtype) (s: Seq.seq a{seq_nonrepeating s})
  : FS.set a
  =
  list_to_set (Seq.seq_to_list s)

let seq_to_set_union (#a: eqtype) (s1 s2: Seq.seq a)
  : Lemma
  (requires
    seq_nonrepeating s1 /\
    seq_nonrepeating s2 /\
    seq_nonrepeating (Seq.append s1 s2)
  )
  (ensures
    seq_to_set (Seq.append s1 s2)
    == FS.union (seq_to_set s1) (seq_to_set s2)
  )
  =
  let set0 = seq_to_set (Seq.append s1 s2) in
  let set1 = seq_to_set s1 in
  let set2 = seq_to_set s2 in
  let list0 = Seq.seq_to_list (Seq.append s1 s2) in
  let list1 = Seq.seq_to_list s1 in
  let list2 = Seq.seq_to_list s2 in
  _seq_to_list_append s1 s2;
  assert (list0 == list1@list2);
  list_to_set_union list1 list2

let seq_to_set_card (#a: eqtype)
  (s: Seq.seq a{seq_nonrepeating s})
  : Lemma
  (Seq.length s = FS.cardinality (seq_to_set s))
  =
  list_to_set_card (Seq.seq_to_list s)

let seq_to_set_equivmem (#a: eqtype)
  (s: Seq.seq a{seq_nonrepeating s})
  (e: a)
  : Lemma
  (Seq.mem e s = FS.mem e (seq_to_set s))
  =
  admit ();
  list_to_set_equivmem (Seq.seq_to_list s) e

let seq_to_set_empty (#a: eqtype)
  : Lemma
  (seq_to_set Seq.empty == FS.emptyset #a)
  =
  list_to_set_empty #a

let seq_to_set_singleton (#a: eqtype) (x: a)
  : Lemma
  (seq_to_set (Seq.create 1 x) == FS.singleton x)
  =
  list_to_set_singleton x
