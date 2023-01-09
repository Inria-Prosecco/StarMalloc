module SteelPtrdiff

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module U32 = FStar.UInt32
module US = FStar.SizeT
module UP = FStar.PtrdiffT

// same_base_array
open Utils2

// add hypothesis about whether the returned value actually fits on ptrdiff_t
// that is, explicit the fact that the implemented allocator relies on the ">= 32-bit" assumption
//assume val ptrdiff' (#a: Type) (arr1 arr2: array a)
//  : Pure UP.t
//  (requires same_base_array arr1 arr2)
//  (ensures fun r ->
//    UP.v r == A.offset (A.ptr_of arr1) - A.offset (A.ptr_of arr2)
//  )

assume val ptrdiff (#a: Type) (arr1 arr2: array a)
  : Steel UP.t
  (A.varray arr1 `star` A.varray arr2)
  (fun _ -> A.varray arr1 `star` A.varray arr2)
  (requires fun _ -> same_base_array arr1 arr2)
  (ensures fun h0 r h1 ->
    A.asel arr1 h1 == A.asel arr1 h0 /\
    A.asel arr2 h1 == A.asel arr2 h0 /\
    UP.v r == A.offset (A.ptr_of arr1) - A.offset (A.ptr_of arr2)
  )

assume val within_bounds (#a: Type) (arr1 p arr2: array a) : prop

assume val within_bounds_intro (#a: Type)
  (arr1 p arr2: array a)
  : Steel bool
  (A.varray arr1 `star` A.varray p `star` A.varray arr2)
  (fun _ -> A.varray arr1 `star` A.varray p `star` A.varray arr2)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    if r then within_bounds arr1 p arr2 else True /\
    A.asel arr1 h1 == A.asel arr1 h0 /\
    A.asel p h1 ==  A.asel p h0 /\
    A.asel arr2 h1 == A.asel arr2 h0
  )

assume val within_bounds_elim (#a: Type)
  (arr1 arr2 p: array a)
  : Lemma
  (requires
    same_base_array arr1 arr2 /\
    within_bounds arr1 p arr2)
  (ensures
    same_base_array arr1 p /\
    same_base_array arr2 p /\
    A.offset (A.ptr_of p) - A.offset (A.ptr_of arr1) >= 0 /\
    A.offset (A.ptr_of arr2) - A.offset (A.ptr_of p) >= 0
  )
