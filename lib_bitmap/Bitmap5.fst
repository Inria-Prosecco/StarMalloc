module Bitmap5


module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Seq = FStar.Seq
module FBV = FStar.BitVector

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

let array = Steel.ST.Array.array

module FU = FStar.UInt
open FStar.Mul

module G =  FStar.Ghost

// spec is done
// lets define the Steel implementation

noextract
unfold
let f_aux (k: nat{k < U64.n})
  : r:nat{r < U64.n}
  = U64.n - k - 1

noextract
unfold
let f (#n: nat)
  (k:nat{k < n * U64.n})
  : r:nat{r < n * U64.n}
  =
  let k1 = k/U64.n in
  let k2 = k%U64.n in
  k1*U64.n + (f_aux k2)

let f_lemma (#n: nat) (k:nat{k < n * U64.n})
  : Lemma
  (k / U64.n = (f #n k ) / U64.n)
  = ()

noextract
let bm_get_aux
  (#n: nat)
  (arr: array U64.t{A.length arr = n})
  (k: U32.t{U32.v k < U64.n * n})
  : Steel bool
  (A.varray arr)
  (fun _ -> A.varray arr)
  (requires fun _ -> True)
  (ensures fun h0 b h1 ->
    b = Bitmap4.get (A.asel arr h0) k /\
    A.asel arr h1 == A.asel arr h0
  )
  =
  let k1 = U32.div k 64ul in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k1 in
  let r = Bitmap3.get x k2 in
  return r

#push-options "--z3rlimit 50"
let bm_get
  (#n: nat)
  (arr: array U64.t{A.length arr = G.reveal n})
  (k: U32.t{U32.v k < U64.n * n})
  : Steel bool
  (A.varray arr)
  (fun _ -> A.varray arr)
  (requires fun _ -> True)
  (ensures fun h0 b h1 ->
    let bm = Bitmap4.array_to_bv2 (A.asel arr h0) in
    let idx = f #n (U32.v k) in
    b = Bitmap4.get (A.asel arr h0) k /\
    b = Seq.index bm idx /\
    A.asel arr h1 == A.asel arr h0
  )
  =
  let h = get () in
  let s : G.erased (Seq.lseq U64.t n) = A.asel arr h in
  let k' = G.hide (f #n (U32.v k)) in

  let k1 = U32.div k 64ul in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k1 in
  let r = Bitmap3.get x k2 in
  Bitmap3.bv_get_lemma x k2;
  assert (r = FU.nth (U64.v (Seq.index s (U32.v k1))) (f_aux (U32.v k2)));
  Bitmap4.array_to_bv_lemma s k';
  assert (r = Seq.index (Bitmap4.array_to_bv s) k');
  Bitmap4.array_to_bv2_lemma s;
  return r
#pop-options

noextract
let bm_set_aux
  (#n: nat)
  (arr: array U64.t{A.length arr = n})
  (k: U32.t{U32.v k < U64.n * n})
  : Steel unit
  (A.varray arr)
  (fun _ -> A.varray arr)
  (requires fun _ -> True)
  (ensures fun h0 b h1 ->
    A.asel arr h1 == Bitmap4.set (A.asel arr h0) k
  )
  =
  let k1 = U32.div k 64ul in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k1 in
  let r = Bitmap3.set x k2 in
  A.upd arr k1 r

#push-options "--z3rlimit 50"
let bm_set
  (#n: nat)
  (arr: array U64.t{A.length arr = n})
  (k: U32.t{U32.v k < U64.n * n})
  : Steel unit
  (A.varray arr)
  (fun _ -> A.varray arr)
  (requires fun h0 ->
    let bm0 = Bitmap4.array_to_bv2 (A.asel arr h0) in
    let idx = f #n (U32.v k) in
    Seq.index bm0 idx = false
  )
  (ensures fun h0 b h1 ->
    let bm0 = Bitmap4.array_to_bv2 (A.asel arr h0) in
    let bm1 = Bitmap4.array_to_bv2 (A.asel arr h1) in
    let idx = f #n (U32.v k) in
    A.asel arr h1 == Bitmap4.set (A.asel arr h0) k /\
    Seq.index bm1 idx = true /\
    bm1 == Seq.upd bm0 idx true
  )
  =
  let h0 = get () in
  let s0 : G.erased (Seq.lseq U64.t n) = A.asel arr h0 in
  Bitmap4.array_to_bv2_lemma s0;
  let k' = G.hide (f #n (U32.v k)) in
  let k1 = U32.div k 64ul in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k1 in
  Bitmap4.array_to_bv_lemma s0 k';
  assert (Seq.index (Bitmap4.array_to_bv s0) k' = false);
  assert (U32.v k1 = U32.v k / 64);
  f_lemma #n (U32.v k);
  assert (k' / U64.n = U32.v k1);
  let r = Bitmap3.set x k2 in
  Bitmap3.bv_set_lemma x k2;
  A.upd arr k1 r;

  let h1 = get () in
  let s1 : G.erased (Seq.lseq U64.t n) = A.asel arr h1 in
  Bitmap4.array_to_bv2_lemma s1;
  Bitmap4.array_to_bv_lemma s1 k';
  assert (Seq.index (Bitmap4.array_to_bv s1) k' = true);
  assert (G.reveal s1 == Seq.upd s0 (U32.v k1) r);
  let bm0 = G.hide (Bitmap4.array_to_bv s0) in
  let bm1 = G.hide (Bitmap4.array_to_bv s1) in
  Bitmap4.array_to_bv_lemma_upd_set s0 s1 (U32.v k);
  Seq.lemma_eq_intro bm1 (Seq.upd bm0 k' true)
#pop-options

noextract
let bm_unset_aux
  (#n: nat)
  (arr: array U64.t{A.length arr = n})
  (k: U32.t{U32.v k < U64.n * n})
  : Steel unit
  (A.varray arr)
  (fun _ -> A.varray arr)
  (requires fun _ -> True)
  (ensures fun h0 b h1 ->
    A.asel arr h1 == Bitmap4.unset (A.asel arr h0) k
  )
  =
  let k1 = U32.div k 64ul in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k1 in
  let r = Bitmap3.unset x k2 in
  A.upd arr k1 r

#push-options "--z3rlimit 50"
let bm_unset
  (#n: nat)
  (arr: array U64.t{A.length arr = n})
  (k: U32.t{U32.v k < U64.n * n})
  : Steel unit
  (A.varray arr)
  (fun _ -> A.varray arr)
  (requires fun h0 ->
    let bm0 = Bitmap4.array_to_bv2 (A.asel arr h0) in
    let idx = f #n (U32.v k) in
    Seq.index bm0 idx = true
  )
  (ensures fun h0 b h1 ->
    let bm0 = Bitmap4.array_to_bv2 (A.asel arr h0) in
    let bm1 = Bitmap4.array_to_bv2 (A.asel arr h1) in
    let idx = f #n (U32.v k) in
    A.asel arr h1 == Bitmap4.unset (A.asel arr h0) k /\
    Seq.index bm1 idx = false /\
    bm1 == Seq.upd bm0 idx false
  )
  =
  let h0 = get () in
  let s0 : G.erased (Seq.lseq U64.t n) = A.asel arr h0 in
  Bitmap4.array_to_bv2_lemma s0;
  let k' = G.hide (f #n (U32.v k)) in
  let k1 = U32.div k 64ul in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k1 in
  Bitmap4.array_to_bv_lemma s0 k';
  assert (Seq.index (Bitmap4.array_to_bv s0) k' = true);
  assert (U32.v k1 = U32.v k / 64);
  f_lemma #n (U32.v k);
  assert (k' / U64.n = U32.v k1);
  let r = Bitmap3.unset x k2 in
  Bitmap3.bv_unset_lemma x k2;
  A.upd arr k1 r;

  let h1 = get () in
  let s1 : G.erased (Seq.lseq U64.t n) = A.asel arr h1 in
  Bitmap4.array_to_bv2_lemma s1;
  Bitmap4.array_to_bv_lemma s1 k';
  assert (Seq.index (Bitmap4.array_to_bv s1) k' = false);
  assert (G.reveal s1 == Seq.upd s0 (U32.v k1) r);
  let bm0 = G.hide (Bitmap4.array_to_bv s0) in
  let bm1 = G.hide (Bitmap4.array_to_bv s1) in
  Bitmap4.array_to_bv_lemma_upd_unset s0 s1 (U32.v k);
  Seq.lemma_eq_intro bm1 (Seq.upd bm0 k' false)
#pop-options
