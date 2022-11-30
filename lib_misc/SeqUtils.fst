module SeqUtils

module L = FStar.List.Tot
module U32 = FStar.UInt32

let rec lemma_seq_to_list_append (#a:Type) (s1 s2: Seq.seq a)
  : Lemma
  (ensures
    Seq.seq_to_list (Seq.append s1 s2) == L.append (Seq.seq_to_list s1) (Seq.seq_to_list s2))
  (decreases Seq.length s1)
  = if Seq.length s1 = 0 then (assert (Seq.append s1 s2 `Seq.equal` s2))
    else (
      let s1' = Seq.slice s1 1 (Seq.length s1) in
      let s12 = Seq.append s1 s2 in
      let s12' = Seq.slice s12 1 (Seq.length s12) in
      lemma_seq_to_list_append s1' s2;
      assert (s12' `Seq.equal` Seq.append s1' s2)
    )

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

noextract
let init_nat (len: nat)
  : Seq.lseq (k:nat{k < len}) len
  = Seq.init len (fun k -> k)

let init_nat_index (len: nat) (i:nat{i < len})
  : Lemma
  (Seq.index (init_nat len) i = i)
  = ()

noextract
let init_nat_refined (len: nat) (len2: nat)
  : Pure (Seq.lseq (k:nat{k < len2}) len)
  (requires len <= len2)
  (ensures fun _ -> True)
  =
  let s : Seq.lseq (k:nat{k < len}) len
    = Seq.init len (fun k -> k) in
  let f : (k:nat{k < len}) -> (k':nat{k' < len2})
    = fun k -> k in
  Seq.map_seq_len f s;
  let s' : Seq.lseq (k:nat{k < len2}) len
    = Seq.map_seq f s in
  s'

noextract
let init_u32_refined (len: nat)
  : Pure (Seq.lseq (k:U32.t{U32.v k < len}) len)
  (requires FStar.UInt.size len U32.n)
  (ensures fun _ -> True)
  =
  let s : Seq.lseq (k:nat{k < len}) len
    = Seq.init len (fun k -> k) in
  let f : (k:nat{k < len}) -> (k':U32.t{U32.v k' < len})
    = fun k -> U32.uint_to_t k in
  Seq.map_seq_len f s;
  let s' : Seq.lseq (k:U32.t{U32.v k < len}) len
    = Seq.map_seq f s in
  s'

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
  admit ()
