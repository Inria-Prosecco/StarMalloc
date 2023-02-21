module StarMalloc

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

open FStar.Mul
open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module R = Steel.Reference
module SAA = Steel.ArrayArith

open Prelude
open Utils2

// slab allocator
open Main
// AVL+mmap allocator
open LargeAlloc

val malloc (size: US.t)
  : Steel (array U8.t)
  emp
  (fun r -> if A.is_null r then emp else A.varray r)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let malloc size =
  if US.lte size (US.uint32_to_sizet page_size)
  then slab_malloc (US.sizet_to_uint32 size)
  else large_malloc size

val free (ptr: array U8.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  //TODO: remove this precondition
  (requires fun _ -> A.is_full_array ptr)
  (ensures fun _ _ _ -> True)

let free ptr =
  let b = slab_free ptr in
  if b then (
    return b
  ) else (
    change_equal_slprop
      (if b then emp else A.varray ptr)
      (A.varray ptr);
    let b = large_free ptr in
    return b
  )

let getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr) (fun _ -> A.varray ptr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel ptr h1 == A.asel ptr h0
  )
  =
  let s1 = slab_getsize ptr in
  if s1 = 0sz then (
    let s2 = large_getsize ptr in
    return s2
  ) else (
    return s1
  )

assume
val memcpy (dest src: array U8.t) (n: US.t)
  : SteelT (array U8.t)
  (A.varray dest `star` A.varray src)
  (fun _ -> A.varray dest `star` A.varray src)

module G = FStar.Ghost

let realloc (ptr: array U8.t) (new_size: US.t)
  : Steel (G.erased bool & array U8.t)
  (A.varray ptr)
  (fun r -> A.varray (snd r))
  (requires fun _ -> A.is_full_array ptr)
  (ensures fun _ _ _ -> True)
  =
  let old_size = getsize ptr in
  if old_size = 0sz then (
    return (G.hide false, ptr)
  ) else (
    let new_ptr = malloc new_size in
    if (A.is_null new_ptr) then (
      sladmit ();
      return (G.hide false, A.null #U8.t)
    ) else (
      change_equal_slprop
        (if A.is_null new_ptr then emp else A.varray new_ptr)
        (A.varray new_ptr);
      let new_size  = if US.lte new_size old_size then old_size else new_size in
      let _ = memcpy ptr new_ptr new_size in
      let b = free ptr in
      if b then (
        sladmit ();
        return (G.hide true, new_ptr)
      ) else (
        sladmit ();
        return (G.hide false, A.null #U8.t)
      )
    )
  )
