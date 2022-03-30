module Seq.Aux

val map_seq2 (#a #b #c: Type) (f:a -> b -> Tot c)
  (s1:Seq.seq a) (s2:Seq.seq b{Seq.length s1 = Seq.length s2})
  : Tot (Seq.seq c)

val map_seq2_len (#a #b #c: Type) (f:a -> b -> Tot c)
  (s1:Seq.seq a) (s2:Seq.seq b{Seq.length s1 = Seq.length s2})
  : Lemma
  (ensures Seq.length (map_seq2 f s1 s2) == Seq.length s1)

val map_seq2_index (#a #b #c: Type) (f: a -> b -> Tot c)
  (s1:Seq.seq a) (s2:Seq.seq b{Seq.length s1 = Seq.length s2})
  (i: nat{i < Seq.length s1})
  : Lemma
  (ensures (
    map_seq2_len f s1 s2;
    Seq.index (map_seq2 f s1 s2) i
    == f (Seq.index s1 i) (Seq.index s2 i)
  ))

val map_seq2_append (#a #b #c: Type) (f: a -> b -> Tot c)
  (s1:Seq.seq a) (s2:Seq.seq b{Seq.length s1 = Seq.length s2})
  (s3:Seq.seq a) (s4:Seq.seq b{Seq.length s3 = Seq.length s4})
  : Lemma (
    map_seq2 f (Seq.append s1 s3) (Seq.append s2 s4)
    == Seq.append (map_seq2 f s1 s2) (map_seq2 f s3 s4)
  )


val map_seq2_comm (#a #c: Type)
  (f:a -> a -> Tot c)
  (s1:Seq.seq a) (s2:Seq.seq a{Seq.length s1 = Seq.length s2})
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    (forall (i:nat{i < Seq.length s1}).
      f (Seq.index s1 i) (Seq.index s2 i)
   == f (Seq.index s2 i) (Seq.index s1 i)))
  (ensures map_seq2 f s1 s2 == map_seq2 f s2 s1)

val map_seq2_assoc (#a: Type)
  (f:a -> a -> Tot a) (s1 s2 s3:Seq.seq a)
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    Seq.length s2 == Seq.length s3 /\
    (forall (i:nat{i < Seq.length s1}).
      f (f (Seq.index s1 i) (Seq.index s2 i)) (Seq.index s3 i)
   == f (Seq.index s1 i) (f (Seq.index s2 i) (Seq.index s3 i)))
  )
  (ensures (
    map_seq2_len f s1 s2;
    map_seq2_len f s2 s3;
    map_seq2 f (map_seq2 f s1 s2) s3
 == map_seq2 f s1 (map_seq2 f s2 s3)
  ))

val unzip (#a #b: Type) (s: Seq.seq (a & b))
  : Tot (Seq.seq a & Seq.seq b)
val unzip_len (#a #b: Type) (s: Seq.seq (a & b))
  : Lemma
  (ensures Seq.length (fst (unzip s)) == Seq.length (snd (unzip s)) /\
  Seq.length (fst (unzip s)) == Seq.length s)
val unzip_index (#a #b: Type) (s: Seq.seq (a & b))
  (i: nat{i < Seq.length s})
  : Lemma
  (ensures (
    unzip_len s;
    let s1, s2 = unzip s in
    Seq.index s i
    == (Seq.index s1 i, Seq.index s2 i)
  ))

val zip (#a #b: Type)
  (s1: Seq.seq a) (s2: Seq.seq b{Seq.length s1 = Seq.length s2})
  : Tot (Seq.seq (a & b))
val zip_len (#a #b: Type)
  (s1: Seq.seq a) (s2: Seq.seq b{Seq.length s1 = Seq.length s2})
  : Lemma
  (ensures Seq.length (zip s1 s2) == Seq.length s1 /\
  Seq.length (zip s1 s2) == Seq.length s2)
val zip_index (#a #b: Type)
  (s1:Seq.seq a) (s2:Seq.seq b{Seq.length s1 = Seq.length s2})
  (i: nat{i < Seq.length s1})
  : Lemma
  (ensures (
    zip_len s1 s2;
    Seq.index (zip s1 s2) i
    == (Seq.index s1 i, Seq.index s2 i)
  ))
