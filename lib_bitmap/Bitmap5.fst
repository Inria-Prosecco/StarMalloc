module Bitmap5

module FI = FStar.Int
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16

module Seq = FStar.Seq
module FBV = FStar.BitVector

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

let array (a: Type) = Steel.ST.Array.array a

module FU = FStar.UInt
open FStar.Mul
module G =  FStar.Ghost

open Prelude

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
  (#n: G.erased nat{n < FI.max_int U16.n})
  (arr: array U64.t{A.length arr = G.reveal n})
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
  let k_index = US.uint32_to_sizet k1 in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k_index in
  let r = Bitmap3.get x k2 in
  return r

let bm_get
  (#n: G.erased nat{n < FI.max_int U16.n})
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
  let k_index = US.uint32_to_sizet k1 in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k_index in
  let r = Bitmap3.get x k2 in
  Bitmap4.get_lemma2 s k;
  return r

noextract
let bm_set_aux
  (#n: G.erased nat{n < FI.max_int U16.n})
  (arr: array U64.t{A.length arr = G.reveal n})
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
  let k_index = US.uint32_to_sizet k1 in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k_index in
  let r = Bitmap3.set x k2 in
  A.upd arr k_index r

let bm_set
  (#n: G.erased nat{n < FI.max_int U16.n})
  (arr: array U64.t{A.length arr = G.reveal n})
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
  let k1 = U32.div k 64ul in
  let k_index = US.uint32_to_sizet k1 in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k_index in
  let r = Bitmap3.set x k2 in
  Bitmap4.set_lemma2 s0 k;
  A.upd arr k_index r

noextract
let bm_unset_aux
  (#n: nat{n < FI.max_int U16.n})
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
  let k_index = US.uint32_to_sizet k1 in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k_index in
  let r = Bitmap3.unset x k2 in
  A.upd arr k_index r

let bm_unset
  (#n: G.erased nat{n < FI.max_int U16.n})
  (arr: array U64.t{A.length arr = G.reveal n})
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
  let k1 = U32.div k 64ul in
  let k_index = US.uint32_to_sizet k1 in
  let k2 = U32.rem k 64ul in
  let x = A.index arr k_index in
  let r = Bitmap3.unset x k2 in
  Bitmap4.unset_lemma2 s0 k;
  A.upd arr k_index r
