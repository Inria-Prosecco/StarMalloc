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
// TODO: convert back to UP
assume val ptrdiff' (#a: Type) (arr1 arr2: array a)
  : Pure UP.t
  (requires same_base_array arr1 arr2)
  (ensures fun r ->
    UP.v r == A.offset (A.ptr_of arr1) - A.offset (A.ptr_of arr2)
  )

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

// uintptr_t modelization
assume val t : Type0

assume val to_uintptr (#a: Type) (arr: array a) : t
//not needed, likely risky
//assume val uintptr_to_arr (#a: Type) (v: t) : array a
//assume val uintptr_bij (#a: Type) (arr: array a) : Lemma
assume val lt (a b: t) : bool
assume val lte (a b: t) : bool

assume val within_bounds (#a: Type)
  (arr1 arr2 p: array a)
  : Lemma
  (requires
    same_base_array arr1 arr2 /\
    lte (to_uintptr arr1) (to_uintptr p) /\
    lt (to_uintptr p) (to_uintptr arr2))
  (ensures
    same_base_array arr1 p /\
    same_base_array arr2 p
    //TODO: add properties about offset
  )
