module Seq2

friend FStar.Seq.Base

let rec map_seq2 #a #b #c f s1 s2
  : Tot (Seq.seq c) (decreases Seq.length s1) =
  if Seq.length s1 = 0
  then Seq.empty
  else let hd1, tl1 = Seq.head s1, Seq.tail s1 in
       let hd2, tl2 = Seq.head s2, Seq.tail s2 in
       Seq.cons (f hd1 hd2) (map_seq2 f tl1 tl2)

let rec map_seq2_len #a #b #c f s1 s2
  : Lemma
  (ensures Seq.length (map_seq2 f s1 s2) == Seq.length s1)
  (decreases Seq.length s1)
  = if Seq.length s1 = 0
    then ()
    else map_seq2_len f (Seq.tail s1) (Seq.tail s2)

let rec map_seq2_index #a #b #c f s1 s2 i
  : Lemma
  (ensures (
    map_seq2_len f s1 s2;
    Seq.index (map_seq2 f s1 s2) i
    == f (Seq.index s1 i) (Seq.index s2 i)
  ))
  (decreases Seq.length s1)
  =
  map_seq2_len f s1 s2;
  if Seq.length s1 = 0
  then ()
  else if i = 0
  then ()
  else map_seq2_index f (Seq.tail s1) (Seq.tail s2) (i-1)

let map_seq2_append #a #b #c f s1 s2 s3 s4
  =
  map_seq2_len f s1 s2;
  map_seq2_len f s3 s4;
  map_seq2_len f (Seq.append s1 s3) (Seq.append s2 s4);
  Classical.forall_intro (map_seq2_index f s1 s2);
  Classical.forall_intro (map_seq2_index f s3 s4);
  Classical.forall_intro (map_seq2_index f
    (Seq.append s1 s3) (Seq.append s2 s4));
  assert (Seq.equal
    (map_seq2 f (Seq.append s1 s3) (Seq.append s2 s4))
    (Seq.append (map_seq2 f s1 s2) (map_seq2 f s3 s4)))

let rec map_seq2_comm #a #c f s1 s2
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    (forall (i:nat{i < Seq.length s1}).
      f (Seq.index s1 i) (Seq.index s2 i)
   == f (Seq.index s2 i) (Seq.index s1 i)))
  (ensures map_seq2 f s1 s2 == map_seq2 f s2 s1)
  (decreases Seq.length s1)
  =
  if Seq.length s1 = 0
  then ()
  else map_seq2_comm f (Seq.tail s1) (Seq.tail s2)

//#push-options "--z3rlimit 30"
let rec map_seq2_assoc #a f s1 s2 s3
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    Seq.length s2 == Seq.length s3 /\
    (forall (i:nat{i < Seq.length s1}).
      f (f (Seq.index s1 i) (Seq.index s2 i)) (Seq.index s3 i)
   == f (Seq.index s1 i) (f (Seq.index s2 i) (Seq.index s3 i))))
  (ensures (
    map_seq2_len f s1 s2;
    map_seq2_len f s2 s3;
    map_seq2 f (map_seq2 f s1 s2) s3
 == map_seq2 f s1 (map_seq2 f s2 s3)
  ))
  (decreases Seq.length s1)
  =
  if Seq.length s1 = 0
  then ()
  else begin
    map_seq2_len f s1 s2;
    map_seq2_len f s2 s3;
    map_seq2_assoc f (Seq.tail s1) (Seq.tail s2) (Seq.tail s3)
  end

let rec unzip #a #b s
  : Tot (Seq.seq a & Seq.seq b)
  (decreases Seq.length s) =
  if Seq.length s = 0
  then Seq.empty, Seq.empty
  else let hd, tl = Seq.head s, Seq.tail s in
       let s1, s2 = unzip tl in
       Seq.cons (fst hd) s1, Seq.cons (snd hd) s2

let rec unzip_len #a #b s
  : Lemma
  (ensures Seq.length (fst (unzip s)) == Seq.length (snd (unzip s)) /\
  Seq.length (fst (unzip s)) == Seq.length s)
  (decreases Seq.length s)
  = if Seq.length s = 0
    then ()
    else unzip_len (Seq.tail s)

let rec unzip_index #a #b s i
  : Lemma
  (ensures (
    unzip_len s;
    Seq.index s i
== (Seq.index (fst (unzip s)) i, Seq.index (snd (unzip s)) i)
  ))
  (decreases i)
  =
  unzip_len s;
  if Seq.length s = 0
  then ()
  else begin
    if i = 0
    then ()
    else unzip_index (Seq.tail s) (i-1)
  end

let zip #a #b s1 s2
  = map_seq2 #a #b #(a & b) (fun x y -> (x, y)) s1 s2
let zip_len #a #b s1 s2
  = map_seq2_len (fun x y -> (x, y)) s1 s2
let zip_index #a #b s1 s2 i
  = map_seq2_index (fun x y -> (x, y)) s1 s2 i

let unzip_zip_id #a #b s1 s2 =
  zip_len s1 s2;
  unzip_len (zip s1 s2);
  Classical.forall_intro (zip_index s1 s2);
  Classical.forall_intro (unzip_index (zip s1 s2));
  let s1', s2' = unzip (zip s1 s2) in
  Seq.lemma_eq_intro s1 s1';
  Seq.lemma_eq_intro s2 s2';
  Seq.lemma_eq_elim s1 s1';
  Seq.lemma_eq_elim s2 s2'

let zip_unzip_id #a #b s =
  unzip_len s;
  zip_len (fst (unzip s)) (snd (unzip s));
  Classical.forall_intro (unzip_index s);
  Classical.forall_intro (
    zip_index (fst (unzip s)) (snd (unzip s))
  );
  let s' = zip (fst (unzip s)) (snd (unzip s)) in
  Seq.lemma_eq_intro s s'

let from_some'
  (#a: Type)
  (#n: nat)
  (s: Seq.lseq (x: option a{Some? x}) n)
  : Pure (Seq.lseq a n)
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i)
  )
  (ensures fun s' -> forall (i: nat{i < n}).
    Seq.index s' i == Some?.v (Seq.index s i))
  =
  let f : x: option a{Some? x} -> a = fun x -> Some?.v x in
  Seq.map_seq_len f s;
  Classical.forall_intro (Seq.map_seq_index f s);
  Seq.map_seq f s

let to_some'
  (#a: Type)
  (#n: nat)
  (s: Seq.lseq a n)
  : Pure (Seq.lseq (x: option a{Some? x}) n)
  (requires True)
  (ensures fun s' -> forall (i: nat{i < n}).
    Some? (Seq.index s' i) /\
    Seq.index s' i == Some (Seq.index s i)
  )
  =
  let f : a -> x: option a{Some? x} = fun x -> Some x in
  Seq.map_seq_len f s;
  Classical.forall_intro (Seq.map_seq_index f s);
  Seq.map_seq f s

let with_some_aux
  (#a: Type)
  (#n: nat)
  (s: Seq.lseq (option a) n)
  (i:nat{i < n}) (elem: option a)
  : Pure (x:option a{Some? x})
  (requires
    elem == Seq.index s i /\
    (forall (i:nat{i < n}). Some? (Seq.index s i)))
  (ensures fun x -> x == Seq.index s i /\ x == elem)
  = elem

let with_some
  (#a: Type)
  (#n: nat)
  (s: Seq.lseq (option a) n)
  : Pure (Seq.lseq (x: option a{Some? x}) n)
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i))
  (ensures fun s' -> forall (i: nat{i < n}).
    Some? (Seq.index s' i) /\
    Seq.index s' i == Seq.index s i)
  =
  Seq.lemma_init_len n (fun i -> i);
  let indexes = Seq.init n (fun i -> i) in
  assert (Seq.length indexes = n);
  let f = (fun i -> with_some_aux s i (Seq.index s i)) in
  Seq.map_seq_len f indexes;
  let s' = Seq.map_seq f indexes in
  Classical.forall_intro (Seq.map_seq_index f indexes);
  s'

let without_some
  (#a: Type)
  (#n: nat)
  (s: Seq.lseq (x: option a{Some? x}) n)
  : Pure (Seq.lseq (option a) n)
  (requires True)
  (ensures fun s' -> forall (i: nat{i < n}).
    Some? (Seq.index s' i) /\
    Seq.index s' i == Seq.index s i)
  =
  let f : x: option a{Some? x} -> option a = fun x -> x in
  Seq.map_seq_len f s;
  Classical.forall_intro (Seq.map_seq_index f s);
  Seq.map_seq f s

let invert_to_some (#a: Type) (#n: nat)
  (s: Seq.lseq a n)
  : Lemma
  (from_some' (to_some' s) == s)
  =
  let s1 = to_some' s in
  let s2 = from_some' s1 in
  Seq.lemma_eq_intro s2 s


let eq_without_with_some_bij (#a: Type) (#n: nat)
  (s: Seq.lseq (option a) n)
  : Lemma
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i))
  (ensures
    without_some (with_some s) == s)
  =
  Seq.lemma_eq_intro (without_some (with_some s)) s

let eq_with_without_some_bij (#a: Type) (#n: nat)
  (s: Seq.lseq (x: option a{Some? x}) n)
  : Lemma
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i))
  (ensures
    with_some (without_some s) == s)
  =
  Seq.lemma_eq_intro (with_some (without_some s)) s

let eq_bazar_some (#a: Type) (#n: nat)
  (s: Seq.lseq a n)
  : Lemma
  (requires True)
  (ensures
    from_some' (with_some (without_some (to_some' s))) == s)
  =
  eq_with_without_some_bij (to_some' s);
  invert_to_some s
