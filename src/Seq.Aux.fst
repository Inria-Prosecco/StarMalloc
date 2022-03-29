module Seq.Aux

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
