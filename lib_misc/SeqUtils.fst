module SeqUtils

module L = FStar.List.Tot
module U32 = FStar.UInt32

let rec lemma_seq_to_list_append (#a:Type) (s1 s2: Seq.seq a)
  : Lemma
  (ensures
    Seq.seq_to_list (Seq.append s1 s2) == L.append (Seq.seq_to_list s1) (Seq.seq_to_list s2))
  (decreases Seq.length s1)
  =
  match Seq.length s1 with
  | 0 -> assert (Seq.append s1 s2 `Seq.equal` s2)
  | 1 ->
      let x = Seq.index s1 0 in
      assert (Seq.append s1 s2 `Seq.equal` Seq.cons x s2);
      Seq.lemma_index_is_nth s1 0;
      assert (Seq.seq_to_list s1 == [x]);
      Seq.lemma_seq_to_list_cons x s2
  | _ ->
      let x = Seq.index s1 0 in
      let s12 = Seq.append s1 s2 in
      let s1_hd, s1_tl = Seq.split s1 1 in
      Seq.lemma_index_is_nth s1_hd 0;
      assert (s1_hd `Seq.equal` Seq.create 1 x);
      assert (Seq.seq_to_list s1_hd == [x]);
      Seq.lemma_split s1 1;
      assert (s1 == Seq.append s1_hd s1_tl);
      assert (Seq.append s1 s2 `Seq.equal` Seq.append s1_hd (Seq.append s1_tl s2));
      assert (Seq.append s1 s2 `Seq.equal` Seq.append (Seq.append s1_hd s1_tl) s2);
      lemma_seq_to_list_append s1_tl s2;
      lemma_seq_to_list_append s1_hd (Seq.append s1_tl s2);
      lemma_seq_to_list_append s1_hd s1_tl;
      Seq.append_assoc s1_hd s1_tl s2

// remove SMTPat
let lemma_index_slice (#a:Type) (s:Seq.seq a)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length s})
  (k:nat{k < j - i})
  : Lemma
  (requires True)
  (ensures (Seq.index (Seq.slice s i j) k == Seq.index s (k + i)))
  =
  Seq.lemma_index_slice s i j k

let lemma_upd_bij (#a:Type)
  (s1 s2:Seq.seq a)
  (n:nat{n < Seq.length s1})
  (v: a)
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    s2 == Seq.upd s1 n v)
  (ensures
    s1 == Seq.upd s2 n (Seq.index s1 n)
  )
  =
  Seq.lemma_eq_intro s1 (Seq.upd s2 n (Seq.index s1 n))

noextract
let init_nat (len: nat)
  : Seq.lseq (k:nat{k < len}) len
  = Seq.init len (fun k -> k)

let init_nat_index (len: nat) (i:nat{i < len})
  : Lemma
  (Seq.index (init_nat len) i = i)
  = ()

let init_nat_len (len: nat)
  : Lemma
  (Seq.length (init_nat len) = len)
  = ()

//noextract
//let init_nat_refined (len: nat) (len2: nat)
//  : Pure (Seq.lseq (k:nat{k < len2}) len)
//  (requires len <= len2)
//  (ensures fun _ -> True)
//  =
//  let s : Seq.lseq (k:nat{k < len}) len
//    = Seq.init len (fun k -> k) in
//  let f : (k:nat{k < len}) -> (k':nat{k' < len2})
//    = fun k -> k in
//  Seq.map_seq_len f s;
//  let s' : Seq.lseq (k:nat{k < len2}) len
//    = Seq.map_seq f s in
//  s'

noextract
let init_u32_refined (len: nat)
  : Pure (Seq.lseq (k:U32.t{U32.v k < len}) len)
  (requires FStar.UInt.size len U32.n)
  (ensures fun r -> Seq.length r = len)
  =
  let s : Seq.lseq (k:nat{k < len}) len
    = Seq.init len (fun k -> k) in
  let f : (k:nat{k < len}) -> (k':U32.t{U32.v k' < len})
    = fun k -> U32.uint_to_t k in
  Seq.map_seq_len f s;
  let s' : Seq.lseq (k:U32.t{U32.v k < len}) len
    = Seq.map_seq f s in
  s'

module US = FStar.SizeT

noextract
let init_us_refined (len: nat)
  : Pure (Seq.lseq (k:US.t{US.v k < len}) len)
  (requires US.fits len)
  (ensures fun r -> Seq.length r = len)
  =
  let s : Seq.lseq (k:nat{k < len}) len
    = Seq.init len (fun k -> k) in
  let f : (k:nat{k < len}) -> (k':US.t{US.v k' < len})
    = fun k -> US.uint_to_t k in
  Seq.map_seq_len f s;
  let s' : Seq.lseq (k:US.t{US.v k < len}) len
    = Seq.map_seq f s in
  s'

let init_u32_refined_index (len: nat) (i:nat{i < len})
  : Lemma
  (requires FStar.UInt.size len U32.n)
  (ensures Seq.index (init_u32_refined len) i = U32.uint_to_t i)
  =
  let s : Seq.lseq (k:nat{k < len}) len
    = Seq.init len (fun k -> k) in
  let f : (k:nat{k < len}) -> (k':U32.t{U32.v k' < len})
    = fun k -> U32.uint_to_t k in
  Seq.map_seq_len f s;
  Seq.map_seq_index f s i

let init_us_refined_index (len: nat) (i:nat{i < len})
  : Lemma
  (requires US.fits len)
  (ensures Seq.index (init_us_refined len) i = US.uint_to_t i)
  =
  let s : Seq.lseq (k:nat{k < len}) len
    = Seq.init len (fun k -> k) in
  let f : (k:nat{k < len}) -> (k':US.t{US.v k' < len})
    = fun k -> US.uint_to_t k in
  Seq.map_seq_len f s;
  Seq.map_seq_index f s i



let map_seq_slice_aux (#a #b:Type)
  (f: a -> Tot b)
  (s:Seq.seq a)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length s})
  (k:nat{k < j - i})
  : Lemma
  (
  Seq.map_seq_len f s;
  Seq.map_seq_len f (Seq.slice s i j);
  Seq.index (Seq.map_seq f (Seq.slice s i j)) k
  ==
  Seq.index (Seq.slice (Seq.map_seq f s) i j) k
  )
  =
  Seq.map_seq_len f s;
  Seq.map_seq_len f (Seq.slice s i j);
  let v1 = Seq.index (Seq.map_seq f (Seq.slice s i j)) k in
  let v2 = Seq.index (Seq.slice (Seq.map_seq f s) i j) k in
  lemma_index_slice (Seq.map_seq f s) i j k;
  assert (v2 == Seq.index (Seq.map_seq f s) (i + k));
  Seq.map_seq_index f s (i + k);
  assert (v2 == f (Seq.index s (i + k)));
  Seq.map_seq_index f (Seq.slice s i j) k;
  assert (v1 == f (Seq.index (Seq.slice s i j) k));
  lemma_index_slice s i j k;
  assert (v1 == v2)

let map_seq_slice (#a #b:Type)
  (f: a -> Tot b)
  (s:Seq.seq a)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length s})
  : Lemma
  (
  Seq.map_seq_len f s;
  Seq.map_seq f (Seq.slice s i j)
  ==
  Seq.slice (Seq.map_seq f s) i j)
  =
  Seq.map_seq_len f s;
  Seq.map_seq_len f (Seq.slice s i j);
  Classical.forall_intro (map_seq_slice_aux f s i j);
  Seq.lemma_eq_intro
    (Seq.map_seq f (Seq.slice s i j))
    (Seq.slice (Seq.map_seq f s) i j)

let map_seq_weakening (#a1 #a2 #b:Type)
  (f1: a1 -> Tot b)
  (f2: a2 -> Tot b)
  (s1:Seq.seq a1)
  (s2:Seq.seq a2)
  : Lemma
  (requires
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k))
  )
  (ensures
    Seq.map_seq f1 s1 == Seq.map_seq f2 s2
  )
  =
  Seq.map_seq_len f1 s1;
  Seq.map_seq_len f2 s2;
  Classical.forall_intro (Seq.map_seq_index f1 s1);
  Classical.forall_intro (Seq.map_seq_index f2 s2);
  Seq.lemma_eq_intro
    (Seq.map_seq f1 s1)
    (Seq.map_seq f2 s2)

let lemma_slice_index (#a:Type)
  (s1 s2:Seq.seq a)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length s1})
  (k:nat{i <= k /\ k < j})
  : Lemma
  (requires
    Seq.length s1 = Seq.length s2 /\
    Seq.slice s1 i j == Seq.slice s2 i j)
  (ensures
    Seq.index s1 k == Seq.index s2 k)
  =
  lemma_index_slice s1 i j (k-i);
  lemma_index_slice s1 i j (k-i)

let slice_append (#a: Type)
  (s:Seq.seq a)
  (i j:nat)
  (k:nat{i <= j /\ j <= k /\ k <= Seq.length s})
  : Lemma
  (Seq.slice s i k == Seq.append (Seq.slice s i j) (Seq.slice s j k))
  =
  Seq.lemma_split (Seq.slice s i k) (j - i)
