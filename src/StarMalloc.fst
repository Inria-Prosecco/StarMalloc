module StarMalloc

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

open FStar.Mul
open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module R = Steel.Reference
module SAA = Steel.ArrayArith

open Prelude
open Utils2

// slab allocator
open Main
// AVL+mmap allocator
open LargeAlloc


assume
val sizet_to_uint64 (x:US.t) : Pure U64.t
  (requires True)
  (ensures fun y -> U64.v y == US.v x % pow2 64)

val malloc (size: US.t)
  : Steel (array U8.t)
  emp
  (fun r -> if A.is_null r then emp else A.varray r)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

//TODO: remove casts
let malloc size =
  if US.lte size (US.uint32_to_sizet page_size)
  then slab_malloc (US.sizet_to_uint32 size)
  else large_malloc (sizet_to_uint64 size)

val free (ptr: array U8.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  //TODO: remove this precondition
  (requires fun _ -> A.is_full_array ptr)
  (ensures fun _ _ _ -> True)

let free ptr =
  let b = slab_free ptr in
  if b then (
    return b
  ) else (
    change_equal_slprop
      (if b then emp else A.varray ptr)
      (A.varray ptr);
    let b = large_free ptr in
    return b
  )
