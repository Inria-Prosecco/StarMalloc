module SeqUtils

module U32 = FStar.UInt32

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

