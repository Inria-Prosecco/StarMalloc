module Seq2

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

val unzip_zip_id (#a #b: Type)
  (s1:Seq.seq a) (s2:Seq.seq b{Seq.length s1 = Seq.length s2})
  : Lemma
  (ensures (
    zip_len s1 s2;
    fst (unzip (zip s1 s2)) == s1 /\
    snd (unzip (zip s1 s2)) == s2
  ))
val zip_unzip_id (#a #b: Type)
  (s: Seq.seq (a & b))
  : Lemma
  (ensures (
    unzip_len s;
    zip (fst (unzip s)) (snd (unzip s)) == s
  ))

val from_some' (#a: Type) (#n: nat)
  (s: Seq.lseq (x: option a{Some? x}) n)
  : Pure (Seq.lseq a n)
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i)
  )
  (ensures fun s' -> forall (i: nat{i < n}).
    Seq.index s' i == Some?.v (Seq.index s i))

val to_some' (#a: Type) (#n: nat)
  (s: Seq.lseq a n)
  : Pure (Seq.lseq (x: option a{Some? x}) n)
  (requires True)
  (ensures fun s' -> forall (i: nat{i < n}).
    Some? (Seq.index s' i) /\
    Seq.index s' i == Some (Seq.index s i)
  )

val with_some (#a: Type) (#n: nat)
  (s: Seq.lseq (option a) n)
  : Pure (Seq.lseq (x: option a{Some? x}) n)
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i))
  (ensures fun s' -> forall (i: nat{i < n}).
    Some? (Seq.index s' i) /\
    Seq.index s' i == Seq.index s i)

val without_some (#a: Type) (#n: nat)
  (s: Seq.lseq (x: option a{Some? x}) n)
  : Pure (Seq.lseq (option a) n)
  (requires True)
  (ensures fun s' -> forall (i: nat{i < n}).
    Some? (Seq.index s' i) /\
    Seq.index s' i == Seq.index s i)

val invert_to_some (#a: Type) (#n: nat)
  (s: Seq.lseq a n)
  : Lemma
  (from_some' (to_some' s) == s)

val eq_without_with_some_bij (#a: Type) (#n: nat)
  (s: Seq.lseq (option a) n)
  : Lemma
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i))
  (ensures
    without_some (with_some s) == s)

val eq_with_without_some_bij (#a: Type) (#n: nat)
  (s: Seq.lseq (x: option a{Some? x}) n)
  : Lemma
  (requires forall (i: nat{i < n}).
    Some? (Seq.index s i))
  (ensures
    with_some (without_some s) == s)

val eq_bazar_some (#a: Type) (#n: nat)
  (s: Seq.lseq a n)
  : Lemma
  (requires True)
  (ensures
    from_some' (with_some (without_some (to_some' s))) == s)

val append_upd1 (#a: Type)
  (s1 s2: Seq.seq a)
  (k: nat)
  (v: a)
  : Lemma
  (requires k < Seq.length s2)
  (ensures
    Seq.append s1 (Seq.upd s2 k v)
    ==
    Seq.upd (Seq.append s1 s2) (Seq.length s1 + k) v
  )

val append_upd2 (#a: Type)
  (s1 s2: Seq.seq a)
  (k: nat)
  (v: a)
  : Lemma
  (requires k < Seq.length s1)
  (ensures
    Seq.append (Seq.upd s1 k v) s2
    ==
    Seq.upd (Seq.append s1 s2) k v
  )

