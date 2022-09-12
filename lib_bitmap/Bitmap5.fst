module Bitmap5


module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Seq = FStar.Seq
module FBV = FStar.BitVector

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

let array = Steel.ST.Array.array

open FStar.UInt
open FStar.Mul

// spec is done
// lets define the Steel implementation

let bm_get
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

let bm_set
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

let bm_unset
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

// additional versions with refined spec
// use get/set/unset_lemma
// use array_to_bv
