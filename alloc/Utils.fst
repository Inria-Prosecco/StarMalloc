module Utils

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8 = FStar.UInt8

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr

// 1) ptr_diff_t
assume val ptrdiff (arr1 arr2: array U8.t)
  : Steel I32.t
  (A.varray arr1 `star` A.varray arr2)
  (fun _ -> A.varray arr1 `star` A.varray arr2)
  (requires fun h0 ->
    let ptr1 = A.ptr_of arr1 in
    let ptr2 = A.ptr_of arr2 in
    A.base ptr1 == A.base ptr2)
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
  : Pure U32.t
  (requires U64.v x > 0)
  (ensures fun r ->
    U32.v r < 64 /\
    FStar.UInt.nth (U64.v x) (U64.n - U32.v r - 1) = false
  )

let slab_region_len : U64.t = 16777216UL

let slab_region = r:array U8.t{A.length r = U64.v slab_region_len}

// C binding, no top-level Steel initialization
assume val get_slab_region (_:unit)
  : slab_region

let slab_metadata = r:array U64.t{A.length r = 4}

// C binding, no top-level Steel initialization
assume val get_slab_metadata (_:unit)
  : slab_metadata
