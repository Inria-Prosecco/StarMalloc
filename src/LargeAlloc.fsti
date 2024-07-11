module LargeAlloc

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module US = FStar.SizeT
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open Constants
open Utils2
open NullOrVarray

inline_for_extraction noextract
let mmap_actual_size = PtrdiffWrapper.mmap_actual_size

val large_malloc (size: US.t)
  : Steel (array U8.t)
  emp
  (fun ptr -> null_or_varray ptr)
  (requires fun _ ->
    US.v size > 0 /\
    US.v size > U32.v page_size /\
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun _ ptr h1 ->
    let s : (t_of (null_or_varray ptr))
      = h1 (null_or_varray ptr) in
    not (A.is_null ptr) ==> (
      US.fits (US.v size + U32.v page_size) /\
      (let size' = mmap_actual_size size in
      A.length ptr == US.v size' /\
      A.is_full_array ptr /\
      array_u8_alignment ptr page_size /\
      zf_u8 s
    ))
  )

val large_free (ptr: array U8.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

val large_getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr) (fun _ -> A.varray ptr)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    (US.v r > 0 ==>
      A.length ptr == US.v r /\
      US.v r > U32.v page_size
    )
  )
