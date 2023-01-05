module SteelPtrdiff

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module US = FStar.SizeT
module UP = FStar.PtrdiffT

// same_base_array
open Utils2

// add hypothesis about whether the returned value actually fits on ptrdiff_t
// that is, explicit the fact that the implemented allocator relies on the ">= 32-bit" assumption
// TODO: convert back to UP
assume val ptrdiff (#a: Type) (ptr1 ptr2: A.ptr a)
  : Pure US.t
  (requires A.base ptr1 == A.base ptr2)
  (ensures fun r ->
    US.v r == A.offset ptr1 - A.offset ptr2
  )

assume val fits_lte (x y: nat) : Lemma
  (requires (x <= y /\ UP.fits y))
  (ensures (UP.fits x))
  [SMTPat (UP.fits x); SMTPat (UP.fits y)]

let mod_spec (a:nat{UP.fits a}) (b:nat{UP.fits b /\ b <> 0}) : GTot (n:nat{UP.fits n}) =
  let open FStar.Mul in
  let res = a - ((a/b) * b) in
  fits_lte res a;
  res

// TODO: check why SizeT uses mod_spec
assume val rem (a: UP.t) (b: UP.t{UP.v b <> 0}) : Pure UP.t
  (requires True)
  (ensures (fun c -> admit (); mod_spec (UP.v a) (UP.v b) == UP.v c))


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
  )
