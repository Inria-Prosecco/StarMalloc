module Mman

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

//module U64 = FStar.UInt64
//module U32 = FStar.UInt32
//module I32 = FStar.Int32
module U8 = FStar.UInt8
module US = FStar.SizeT
//module UP = FStar.PtrdiffT

let array = Steel.ST.Array.array


noextract
assume val mmap
  //(addr: U64.t)//TODO: implicit cast
  (size: US.t)
  //(prot: I32.t)
  //(flags: I32.t)
  //(fd: I32.t)
  //(off: U32.t)
  : Steel (array U8.t)
    emp
    (fun a -> A.varray a)
    (requires fun _ -> True)
    (ensures fun _ a h1 ->
      A.length a == US.v size /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v size) U8.zero
    )

noextract
assume val munmap (ptr: array U8.t) (size: US.t)
  : Steel bool
    (A.varray ptr)
    (fun b -> if b then emp else A.varray ptr)
    (requires fun _ ->
      //A.length a == U64.v size_t /\
      A.is_full_array ptr
    )
    (ensures fun _ _ _ -> True)
