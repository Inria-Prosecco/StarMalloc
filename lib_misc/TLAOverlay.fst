module TLAOverlay

friend Steel.TLArray

let rec spec_split (#a: Type) (l: list a) (n: nat)
  : Pure (list a & list a)
  (requires n < L.length l)
  (ensures fun (l1, l2) ->
    l == L.append l1 l2 /\
    L.length l1 == n /\
    L.length l2 == L.length l - n
  )
  = match l with
  | [x] ->
      assert (n = 0);
      ([], l)
  | hd::tl ->
      if n = 0
      then ([], l)
      else (
        let l1, l2 = spec_split tl (n-1) in
        hd::l1, l2
      )

let split x n
  = spec_split x n

let merge x1 x2
  = L.append x1 x2

let rec spec_split_lemma1 (#a: Type)
  (l l1 l2: list a)
  (n i: nat)
  : Lemma
  (requires
    L.length l1 == n /\
    l == L.append l1 l2 /\
    i < L.length l /\
    i < n)
  (ensures
    L.index l1 i == L.index l i)
  = match i with
  | 0 -> ()
  | _ -> spec_split_lemma1 (L.tl l) (L.tl l1) l2 (n-1) (i-1)

let split_lemma1 x n i
  =
  let (x1, x2) = split x (US.v n) in
  spec_split_lemma1 (TLA.v x) (TLA.v x1) (TLA.v x2) (US.v n) (US.v i)

let rec spec_split_lemma2 (#a: Type)
  (l l1 l2: list a)
  (n i: nat)
  : Lemma
  (requires
    L.length l1 == n /\
    l == L.append l1 l2 /\
    i < L.length l /\
    i >= n)
  (ensures
    L.length l2 == L.length l - n /\
    L.index l2 (i - n) == L.index l i)
  = match l1 with
  | [] -> ()
  | _ -> spec_split_lemma2 (L.tl l) (L.tl l1) l2 (n-1) (i-1)

let split_lemma2 x n i
  =
  let (x1, x2) = split x (US.v n) in
  spec_split_lemma2 (TLA.v x) (TLA.v x1) (TLA.v x2) (US.v n) (US.v i)
