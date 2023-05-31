module Mman

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U8 = FStar.UInt8
module US = FStar.SizeT

let array = Steel.ST.Array.array

//noextract
assume val mmap_init
  (size: US.t)
  : Steel (array U8.t)
    emp
    (fun r -> A.varray r)
    (requires fun _ -> True)
    (ensures fun _ ptr h1 ->
      A.length ptr == US.v size /\
      A.is_full_array ptr /\
      A.asel ptr h1 == Seq.create (US.v size) U8.zero
    )

open NullOrVarray

open Utils2

//noextract
assume val mmap_noinit
  (size: US.t)
  : Steel (array U8.t)
    emp
    (fun ptr -> null_or_varray ptr)
    (requires fun _ -> True)
    (ensures fun _ ptr h1 ->
      let s : t_of (null_or_varray ptr)
        = h1 (null_or_varray ptr) in
      not (A.is_null ptr) ==> (
        A.length ptr == US.v size /\
        A.is_full_array ptr /\
        zf_u8 s
      )
    )

//noextract
assume val munmap_u8 (ptr: array U8.t) (size: US.t)
  : Steel bool
    (A.varray ptr)
    (fun b -> if b then A.varray ptr else emp)
    (requires fun _ ->
      A.length ptr == US.v size /\
      A.is_full_array ptr
    )
    (ensures fun _ _ _ -> True)
