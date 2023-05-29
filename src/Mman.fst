module Mman

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U8 = FStar.UInt8
module US = FStar.SizeT

let array = Steel.ST.Array.array

//noextract
assume val mmap_s
  (size: US.t)
  : Steel (array U8.t)
    emp
    (fun a -> A.varray a)
    (requires fun _ -> True)
    (ensures fun _ a h1 ->
      A.length a == US.v size /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v size) U8.zero
    )

//noextract
assume val munmap (ptr: array U8.t) (size: US.t)
  : Steel bool
    (A.varray ptr)
    (fun b -> if b then A.varray ptr else emp)
    (requires fun _ ->
      A.length ptr == US.v size /\
      A.is_full_array ptr
    )
    (ensures fun _ _ _ -> True)
