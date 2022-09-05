module Mman

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8 = FStar.UInt8

let array = Steel.ST.Array.array


noextract
assume val mmap
  (addr: U64.t)
  (len: U64.t)
  (prot: I32.t)
  (flags: I32.t)
  (fildes: I32.t)
  (off: U32.t)
  : Steel (array U8.t)
    emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == U64.v len /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (U64.v len) U8.zero
    )

noextract
assume val munmap (a: array U8.t) (size_t: U64.t)
  : Steel unit
    (A.varray a)
    (fun _ -> emp)
    (fun _ ->
      A.length a == U64.v size_t /\
      A.is_full_array a
    )
    (fun _ _ _ -> True)
