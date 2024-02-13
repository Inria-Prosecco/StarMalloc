module SetUtils

open FStar.List.Tot
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

let rec list_to_set_append (#a: eqtype)
  (l1 l2: (l:list a{FS.list_nonrepeating l}))
  : Lemma
  (requires
    FS.list_nonrepeating (l1 @ l2)
  )
  (ensures
    list_to_set (l1 @ l2) == FS.union (list_to_set l1) (list_to_set l2)
  )
  (decreases %[L.length l1 ; L.length l2])
  =
  let s1 = list_to_set l1 in
  let s2 = list_to_set l2 in
  match l1 with
  | [] ->
      assert (l1 @ l2 == l2);
      assert (s1 `FS.equal` FS.emptyset #a);
      assert (FS.union s1 s2 `FS.equal` s2)
  | [x] ->
      assert (l1 @ l2 == x::l2);
      assert (s1 `FS.equal` FS.singleton x);
      assert (FS.union s1 s2 `FS.equal` FS.insert x s2)
  | x::t ->
      list_to_set_append t l2;
      list_to_set_append [x] (t @ l2);
      assert (list_to_set (l1 @ l2) `FS.equal` (FS.union (list_to_set l1) (list_to_set l2)))

let list_to_set_cons (#a: eqtype)
  (x: a)
  (l:list a{FS.list_nonrepeating l})
  : Lemma
  (requires
    FS.list_nonrepeating (x::l)
  )
  (ensures
    list_to_set (x::l) == FS.insert x (list_to_set l)
  )
  =
  list_to_set_append [x] l;
  assert (FS.insert x (list_to_set l) `FS.equal` FS.union (list_to_set [x]) (list_to_set l))

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
      list_to_set_append [x] t;
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
      list_to_set_append [x] t;
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

let rec list_remove (#a: eqtype)
  (x: a)
  (l: list a)
  : Pure (list a)
  (requires FS.list_nonrepeating l)
  (ensures fun l' ->
    FS.list_nonrepeating l' /\
    not (L.mem x l') /\
    (forall (y:a{y <> x}). L.mem y l' = L.mem y l) /\
    l' == L.filter (fun y -> y <> x) l /\
    (not (L.mem x l) ==> l' == l)
  )
  = match l with
  | [] -> []
  | hd::tl ->
    if hd <> x
    then hd::(list_remove x tl)
    else list_remove x tl

let rec list_to_set_remove (#a: eqtype)
  (x: a)
  (l: list a{FS.list_nonrepeating l})
  : Lemma
  (list_to_set (list_remove x l)
  == FS.remove x (list_to_set l))
  = match l with
  | [] ->
    list_to_set_empty #a;
    assert (FS.emptyset `FS.equal` FS.remove x FS.emptyset)
  | hd::tl ->
    if hd <> x
    then (
      assert (list_remove x l == hd::(list_remove x tl));
      list_to_set_cons hd (list_remove x tl);
      assert (list_to_set (hd::list_remove x tl)
      `FS.equal` FS.insert hd (list_to_set (list_remove x tl)));
      list_to_set_remove x tl;
      assert (list_to_set (list_remove x tl)
      `FS.equal` FS.remove x (list_to_set tl));
      assert (FS.insert hd (FS.remove x (list_to_set tl))
      `FS.equal` FS.remove x (FS.insert hd (list_to_set tl)))
    ) else (
      assert (list_remove x l == list_remove x tl);
      list_to_set_remove x tl;
      assert (list_to_set (list_remove x tl)
      `FS.equal` FS.remove x (list_to_set tl));
      assert (not (L.mem x tl));
      assert (list_remove x tl == tl)
    )
