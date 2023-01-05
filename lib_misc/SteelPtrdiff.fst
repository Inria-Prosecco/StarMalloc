module SteelPtrdiff

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module UP = FStar.PtrdiffT

// same_base_array
open Utils2

// add hypothesis about whether the returned value actually fits on ptrdiff_t
// that is, explicit the fact that the implemented allocator relies on the ">= 32-bit" assumption
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

assume val fits_lte (x y: nat) : Lemma
  (requires (x <= y /\ UP.fits y))
  (ensures (UP.fits x))
  [SMTPat (UP.fits x); SMTPat (UP.fits y)]

let mod_spec (a:nat{UP.fits a}) (b:nat{UP.fits b /\ b <> 0}) : GTot (n:nat{UP.fits n}) =
  let open FStar.Mul in
  let res = a - ((a/b) * b) in
  fits_lte res a;
  res

// TODO: check why no SizeT.eq, no PtrdiffT.eq
assume val eq (a: UP.t) (b: UP.t) : Pure bool
  (requires True)
  (ensures (fun c -> (UP.v a) = (UP.v b)))

// TODO: check why SizeT uses mod_spec
assume val rem (a: UP.t) (b: UP.t{UP.v b <> 0}) : Pure UP.t
  (requires True)
  (ensures (fun c -> admit (); mod_spec (UP.v a) (UP.v b) == UP.v c))
