module Bitmap4

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Seq = FStar.Seq
module FBV = FStar.BitVector

open FStar.UInt
open FStar.Mul

let rec array_to_bv_aux
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (k: nat{k <= n})
  : FBV.bv_t (U64.n * k)
  = match k with
  | 0 -> Seq.empty
  | _ ->
      assert (k > 0);
      let idx = n - k in
      assert (0 <= idx /\ idx < n);
      let x = Seq.index s idx in
      let x : FBV.bv_t U64.n = to_vec #U64.n (U64.v x) in
      let s : FBV.bv_t (U64.n * (k - 1)) = array_to_bv_aux s (k - 1) in
      Seq.append x s

let array_to_bv
  (#n: nat)
  (s: Seq.lseq U64.t n)
  : FBV.bv_t (U64.n * n)
  = array_to_bv_aux #n s n

#push-options "--z3rlimit 50"
let rec array_to_bv_aux_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (k: nat{k <= n})
  (i:nat)
  : Lemma
  (requires i < U64.n * k)
  (ensures
    Seq.index (array_to_bv_aux s k) i
    =
    nth (U64.v (Seq.index s ((n-k)+i/U64.n))) (i%U64.n)
  )
  = match k with
  | 0 -> ()
  | _ ->
      assert (k > 0);
      let idx = n - k in
      assert (0 <= idx /\ idx < n);
      let x = Seq.index s idx in
      let s1 = to_vec #U64.n (U64.v x) in
      let s2 = array_to_bv_aux s (k - 1) in
      let r = Seq.append s1 s2 in
      Seq.lemma_split r U64.n;
      let idx1 = i/64*U64.n in
      let idx2 = (i/64+1)*U64.n in
      let idx3 = i%U64.n in
      assert (i = idx1 + idx3);
      Seq.lemma_index_slice r idx1 idx2 idx3;
      if i < U64.n
      then ()
      else begin
        array_to_bv_aux_lemma #n s (k-1) (i-U64.n);
        Seq.lemma_index_slice r U64.n (U64.n * k) (i-U64.n)
      end
#pop-options

let array_to_bv_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires i < U64.n * n)
  (ensures
    Seq.index (array_to_bv s) i
    =
    nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n)
  )
  =
  array_to_bv_aux_lemma #n s n i

let get
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : bool
  =
  let i1 = U32.div i 64ul in
  let i2 = U32.rem i 64ul in
  let x = Seq.index s (U32.v i1) in
  Bitmap3.get x i2

let get_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (get s i = nth
    (U64.v (Seq.index s (U32.v i / U64.n)))
    (U64.n - (U32.v i % U64.n) - 1))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  Bitmap3.bv_get_lemma x i2

let set
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Seq.lseq U64.t n
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  let x' = Bitmap3.set x i2 in
  Seq.upd s (U32.v i1) x'

let set_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (requires
    nth (U64.v (Seq.index s (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = false)
  (ensures (
    let s' = set s i in
    nth (U64.v (Seq.index s' (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = true))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  Bitmap3.bv_set_lemma x i2

let unset
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Seq.lseq U64.t n
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  let x' = Bitmap3.unset x i2 in
  Seq.upd s (U32.v i1) x'

let unset_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (requires
    nth (U64.v (Seq.index s (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = true)
  (ensures (
    let s' = unset s i in
    nth (U64.v (Seq.index s' (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = false))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  Bitmap3.bv_unset_lemma x i2
