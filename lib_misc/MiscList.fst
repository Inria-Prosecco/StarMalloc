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

let lemma_init_index (n: nat) (i:nat{i < n})
  : Lemma
  (L.index (init n) i == i)
  = init_index' n 0 i

noextract
let test (_:unit)
  =
  assert (init 0 == []);
  assert (init 1 = [0]);
  assert (init 2 = [0; 1])

let rec lemma_map_index
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
      lemma_map_index f tl (i-1)
    )

let lemma_map_eq_to_index_eq
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
  lemma_map_index f1 init1 i;
  lemma_map_index f2 init2 i

let rec lemma_index_append1
  (#a: Type)
  (l1 l2: list a)
  (k:nat{k < L.length l1})
  : Lemma
  (let l = L.append l1 l2 in
  L.append_length l1 l2;
  L.index l1 k == L.index l k
  )
  =
  let l = L.append l1 l2 in
  L.append_length l1 l2;
  if k = 0
  then ()
  else lemma_index_append1 (L.tl l1) l2 (k - 1)

let rec lemma_index_append2
  (#a: Type)
  (l1 l2: list a)
  (k:nat{k < L.length l2})
  : Lemma
  (let l = L.append l1 l2 in
  L.append_length l1 l2;
  L.index l2 k == L.index l (L.length l1 + k)
  )
  = match l1 with
  | [] -> ()
  | x::tl ->
      L.append_length l1 l2;
      lemma_index_append2 tl l2 k

let lemma_index_slice
  (#a: Type)
  (l1 l2: list a)
  (k:nat{k < L.length l1 + L.length l2})
  : Lemma
  (let l = L.append l1 l2 in
  L.append_length l1 l2;
  if k < L.length l1
  then L.index l k == L.index l1 k
  else L.index l k == L.index l2 (k - L.length l1)
  )
  =
  if k < L.length l1
  then lemma_index_append1 l1 l2 k
  else lemma_index_append2 l1 l2 (k - L.length l1)

open FStar.Mul

module FML = FStar.Math.Lemmas

let lemma_div_bounds_to_eq
  (i k multiple: nat)
  : Lemma
  (requires
    multiple > 0 /\
    i >= k * multiple /\
    i < (k+1) * multiple)
  (ensures
    i / multiple = k
  )
  =
  let r = i - k * multiple in
  FML.lemma_div_plus r k multiple

let lemma_append_repeat'
  (#a: Type)
  (i:nat)
  (basis: list a)
  (l_basis: nat)
  (acc: list a)
  (k:nat)
  : Lemma
  (requires
    k < (i+1) * l_basis /\
    l_basis > 0 /\
    L.length basis = l_basis /\
    L.length acc = i * l_basis /\
    (forall (k:nat{k < L.length acc}).
      L.index acc k == L.index basis (k % l_basis)
    )
  )
  (ensures (
    let l = acc `L.append` basis in
    L.append_length acc basis;
    L.index l k == L.index basis (k % l_basis)
  ))
  = match i with
  | 0 -> ()
  | _ ->
      let l = acc `L.append` basis in
      L.append_length acc basis;
      if k < i * l_basis
      then lemma_index_append1 acc basis k
      else (
        lemma_index_append2 acc basis (k - i * l_basis);
        lemma_div_bounds_to_eq k i l_basis;
        FML.euclidean_division_definition k l_basis
      )

let lemma_append_repeat
  (#a: Type)
  (i:nat)
  (basis: list a)
  (l_basis: nat)
  (acc: list a)
  : Lemma
  (requires
    l_basis > 0 /\
    L.length basis = l_basis /\
    L.length acc = i * l_basis /\
    (forall (k:nat{k < L.length acc}).
      L.index acc k == L.index basis (k % l_basis)
    )
  )
  (ensures (
    let l = acc `L.append` basis in
    (forall (k:nat{k < L.length l}).
      L.index l k == L.index basis (k % l_basis)
    )
  ))
  =
  let l = acc `L.append` basis in
  L.append_length acc basis;
  assert (L.length l = (i+1) * l_basis);
  Classical.forall_intro (Classical.move_requires (
    fun (k:nat{k < L.length (acc `L.append` basis)}) ->
      lemma_append_repeat' #a i basis l_basis acc k
  ))
