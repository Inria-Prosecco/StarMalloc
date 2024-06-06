module MiscList

module L = FStar.List.Tot

let rec last_rev_hd_lemma (#a: Type)
  (l: list a{Cons? l})
  : Lemma
  (ensures (
    L.rev_length l;
    L.last l == L.hd (L.rev l)
  ))
  (decreases L.length l)
  = match l with
  | [] -> ()
  | [x] -> ()
  | x::l' ->
      assert (Cons? l');
      L.rev_length l';
      assert (Cons? (L.rev l'));
      assert (L.last l == L.last l');
      last_rev_hd_lemma l';
      L.rev_append [x] l';
      assert (L.rev l == (L.rev l')@[x]);
      assert (L.hd (L.rev l) == L.hd (L.rev l'))

let last_mem_lemma (#a: eqtype)
  (l: list a{Cons? l})
  : Lemma
  (L.mem (L.last l) l)
  =
  let x = L.last l in
  L.rev_length l;
  last_rev_hd_lemma l;
  assert (x == L.hd (L.rev l));
  assert (L.mem x (L.rev l));
  L.rev_mem l x;
  assert (L.mem x l)

noextract
let rec init' (n:nat) (k:nat)
  : Pure (list nat)
  (requires True)
  (ensures fun r ->
    L.length r = n
  )
  =
  if n = 0
  then []
  else k::(init' (n-1) (k+1))

noextract
let init (n:nat)
  : list nat
  = init' n 0

let rec init_index' (n:nat) (k:nat) (i:nat{i < n})
  : Lemma
  (L.index (init' n k) i == i + k)
  =
  if n = 0 || i = 0
  then ()
  else init_index' (n-1) (k+1) (i-1)

let init_index (n: nat) (i:nat{i < n})
  : Lemma
  (L.index (init n) i == i)
  = init_index' n 0 i

noextract
let test (_:unit)
  =
  assert (init 0 == []);
  assert (init 1 = [0]);
  assert (init 2 = [0; 1])

let rec map_index
  (#a #b: Type)
  (f: a -> b)
  (l: list a)
  (i: nat{i < L.length l})
  : Lemma
  (L.index (L.map f l) i == f (L.index l i))
  = match l with
  | [] -> ()
  | x::tl -> if i = 0 then () else (
      assert (L.length tl = L.length l - 1);
      map_index f tl (i-1)
    )

let map_eq_to_index_eq
  (#a #b #c: Type)
  (f1: a -> c)
  (f2: b -> c)
  (init1: list a)
  (init2: list b)
  (i: nat{i < L.length init1})
  : Lemma
  (requires
    L.map f1 init1 == L.map f2 init2
  )
  (ensures
    f1 (L.index init1 i) == f2 (L.index init2 i)
  )
  =
  map_index f1 init1 i;
  map_index f2 init2 i
