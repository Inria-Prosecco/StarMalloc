module Utils

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8 = FStar.UInt8

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module FU = FStar.UInt
module L = FStar.List.Tot

open FStar.Mul

let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr


unfold let same_base_array (#a: Type) (arr1 arr2: array a)
  =
  A.base (A.ptr_of arr1) == A.base (A.ptr_of arr2)

// 1) ptr_diff_t
assume val ptrdiff (arr1 arr2: array U8.t)
  : Steel I32.t
  (A.varray arr1 `star` A.varray arr2)
  (fun _ -> A.varray arr1 `star` A.varray arr2)
  (requires fun h0 ->
    same_base_array arr1 arr2)
  (ensures fun h0 r h1 ->
    let ptr1 = A.ptr_of arr1 in
    let ptr2 = A.ptr_of arr2 in
    A.asel arr1 h1 == A.asel arr1 h0 /\
    A.asel arr2 h1 == A.asel arr2 h0 /\
    I32.v r == A.offset ptr2 - A.offset ptr1
  )

// 2) ffs64/ffz64
open Bitmap5
assume val ffs64 (x: U64.t)
  : Pure US.t
  (requires U64.v x > 0)
  (ensures fun r ->
    US.v r < 64 /\
    FStar.UInt.nth (U64.v x) (U64.n - US.v r - 1) = false
  )

let array_to_bv_slice
  (#n: nat)
  (s0: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires
    i < n
  )
  (ensures (
    let bm0 = Bitmap4.array_to_bv2 s0 in
    let x = Seq.index s0 i in
    Seq.slice bm0 (i*64) ((i+1)*64)
    =
    FU.to_vec #64 (U64.v x)))
  =
  Bitmap4.array_to_bv_lemma_upd_set_aux4 s0 (i*64)

let lemma_div (x y z: nat)
  : Lemma
  (requires
    x = y * z /\
    z > 0
  )
  (ensures
    x / z = y
  )
  =
  FStar.Math.Lemmas.lemma_mod_plus 0 y z;
  assert ((y * z) % z = 0)

