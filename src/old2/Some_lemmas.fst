module Some_lemmas

open FStar.List.Tot

unfold let id (x: bool) = x

let rec list_to_pairs (#a: Type0) (l: list a) : list (a & a)
= match l with
| [] -> []
| [x] -> []
| x::y::l' -> (x, y) :: (list_to_pairs (y::l'))

let rec ltp_concat (#a: Type0) (l1 l2: list a)
: Lemma
(requires
  Cons? l1 /\ Cons? l2
)
(ensures
   list_to_pairs (l1 @ l2)
== list_to_pairs l1 @ [(last l1, hd l2)] @ list_to_pairs l2
)
= match l1 with
| [x] -> ()
| _::l' -> ltp_concat l' l2

let rec fold_f (#a: Type0) (f: a -> a -> bool) (l: list a) : bool
= match l with
| [] -> true
| [x] -> true
| x::y::l' -> (f x y) && (fold_f f (y::l'))

let fold = for_all id

let rec fold_concat (x: bool) (l1: list bool)
: Lemma
(fold (l1 @ [x]) = fold (x::l1))
= match l1 with
| [] -> ()
| y::l' ->
    fold_concat x l'

let rec fold_refl (l: list bool)
: Lemma
(fold (rev l) = fold l)
= match l with
| [] -> ()
| x::l' ->
    fold_refl l';
    assert (fold (rev l') = fold l');
    assert (for_all id l <==> id x /\ for_all id l');
    assert (for_all id l <==> id x /\ for_all id (rev l'));
    rev_append [x] l';
    assert (rev l == (rev l') @ [x]);
    fold_concat x (rev l');
    assert (for_all id (rev l) <==> id x /\ for_all id (rev l'));
    ()

let f21 (#a: Type0) (f: a -> a -> bool)
: (a & a) -> bool
= fun (x, y) -> f x y

let f12 (#a: Type0) (f: (a & a) -> bool)
: a -> a -> bool
= fun x y -> f (x, y)

let rec fold_is_foldf (#a: Type0) (f: a -> a -> bool) (l: list a)
: Lemma
(fold (map (f21 f) (list_to_pairs l)) = fold_f f l)
= match l with
| [] -> ()
| [x] -> ()
| x::y::l' -> fold_is_foldf f (y::l')

let rec swap_map_rev (#a #b: Type0)
(f: a -> b)
(l: list a)
: Lemma
(map f (rev l) == rev (map f l))
= match l with
| [] -> ()
| x::l' ->
    assert (map f l == f x::map f l');
    rev_append [x] l';
    assert (map f (rev l) == map f ((rev l')@[x]));
    map_append f (rev l') [x];
    assert (map f (rev l) == (map f (rev l') @ (map f [x])));
    assert (map f (rev l) == (map f (rev l') @ [f x]));
    swap_map_rev f l';
    assert (map f (rev l) == (rev (map f l') @ [f x]));
    rev_append [(f x)] (map f l')

unfold let ts = fun (x, y) -> (y, x)

let rec rev_list_to_pairs (#a: Type0)
(l: list a)
: Lemma
(ensures
list_to_pairs (rev l)
==
rev (map ts (list_to_pairs l))
)
(decreases length l)
= match l with
| [] -> ()
| [x] -> ()
| x::y::l' ->
    // init
    let l1 = y::l' in
    let l1r = (rev l') @ [y] in
    rev_append [y] l';
    assert (l1r == rev l1);
    let l2r = [x] in
    rev_append [x] (y::l');
    assert (l2r == rev l2r);
    assert (rev l == l1r @ l2r);
    // split
    init_last_def (rev l') y;
    assert (y == last l1r);
    assert (x == hd l2r);
    ltp_concat l1r l2r;
    assert (list_to_pairs (rev l)
    == (list_to_pairs l1r) @ [(y, x)]);
    // IH
    append_length [x] (l1);
    assert (length l1 < length l);
    rev_length l1;
    assert (length l1 = length l1r);
    rev_involutive l1;
    assert (rev l1r == l1);
    assert (rev l1 == l1r);
    rev_list_to_pairs l1;
    assert (list_to_pairs l1r
    == rev (map ts (list_to_pairs l1))
    );
    // à la Fubini
    swap_map_rev ts (list_to_pairs l1);
    assert (list_to_pairs l1r
    == map ts (rev (list_to_pairs l1)));
    assert ([(y, x)] == map ts (rev [(x, y)]));
    // factoring under map
    map_append ts (rev (list_to_pairs l1)) [(x, y)];
    assert ((list_to_pairs l1r) @ [(y, x)]
    == map ts ( (rev (list_to_pairs l1)) @ [(x, y)]));
    // factoring under list
    rev_involutive (list_to_pairs l1);
    rev_append [(x, y)] (list_to_pairs l1);
    assert (rev ((x, y) :: list_to_pairs l1)
    == (rev (list_to_pairs l1)) @ [(x, y)]);
    // factoring under list_to_pairs
    assert ((x, y) :: list_to_pairs l1 == list_to_pairs l);
    // à la Fubini
    swap_map_rev ts (list_to_pairs l);
    ()

let rec map_ts_invariant (#a: Type0)
(f: (a & a) -> bool)
(l: list (a & a))
: Lemma
(requires
  forall x y. f (x, y) = f (y, x)
)
(ensures
  map f (map ts l) = map f l
)
= match l with
| [] -> ()
| a::tl -> map_ts_invariant f tl


let rev_foldf (#a: Type0) (f: a -> a -> bool) (l: list a)
: Lemma
(requires
  forall x y. f x y = f y x
)
(ensures
  fold_f f (rev l) = fold_f f l
)
=
// (1) : on applique le lemma de base d'un côté...
fold_is_foldf f l;
assert (fold_f f l =
fold (map (f21 f) (list_to_pairs l)));
// (2) : ...puis de l'autre
fold_is_foldf f (rev l);
assert (fold_f f (rev l)
= fold (map (f21 f) (list_to_pairs (rev l))));
// (3) : on décompose et on sort le rev
rev_list_to_pairs l;
assert (list_to_pairs (rev l)
== rev (map ts (list_to_pairs l)));
// (4) : on prépare la simplification de la transposition
let l1 = map ts (list_to_pairs l) in
swap_map_rev (f21 f) l1;
assert (map (f21 f) (rev l1) = rev (map (f21 f) l1));
// (5) : on simplifie la transposition
map_ts_invariant (f21 f) (list_to_pairs l);
assert (map (f21 f) l1 == map (f21 f) (list_to_pairs l));
// (6) : on remonte
assert (map (f21 f) (list_to_pairs (rev l))
== rev (map (f21 f) (list_to_pairs l)));
// (7) : reste à montrer que fold (rev l) = fold l
fold_refl (map (f21 f) (list_to_pairs l));
()

