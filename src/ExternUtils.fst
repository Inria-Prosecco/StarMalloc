module ExternUtils

module G = FStar.Ghost
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

open Config
open Utils2

assume val ffs64 (x: U64.t) (bound: G.erased U32.t)
  : Pure U32.t
  (requires
    U32.v (G.reveal bound) <= 64 /\
    (exists (k:nat{k < U32.v (G.reveal bound)}). nth_is_zero x (U32.uint_to_t k)))
  (ensures fun r ->
    U32.v r < U32.v (G.reveal bound) /\
    nth_is_zero x r /\
    (forall (k:nat{k < U64.n /\ nth_is_zero x (U32.uint_to_t k)}).
      U32.v r <= k
    )
  )

assume val apply_zeroing_u8
  (ptr: array U8.t)
  (n: US.t)
  : Steel unit
  (A.varray ptr)
  (fun _ -> A.varray ptr)
  (requires fun h0 ->
    A.length ptr >= US.v n
  )
  (ensures fun h0 _ h1 ->
    A.length ptr >= US.v n /\
    zf_u8 (Seq.slice (A.asel ptr h1) 0 (US.v n))
  )

let apply_zeroing_u8_cond
  (ptr: array U8.t)
  (n: US.t)
  : Steel unit
  (A.varray ptr)
  (fun _ -> A.varray ptr)
  (requires fun h0 ->
    A.length ptr >= US.v n
  )
  (ensures fun h0 _ h1 ->
    A.length ptr >= US.v n /\
    (not enable_zeroing_free ==>
      A.asel ptr h1 == A.asel ptr h0
    ) /\
    (enable_zeroing_free ==>
      zf_u8 (Seq.slice (A.asel ptr h1) 0 (US.v n))
    )
  )
  =
  if enable_zeroing_free then (
    apply_zeroing_u8 ptr n
  ) else (
    return ()
  )

assume val check_zeroing_u8
  (ptr: array U8.t)
  (n: US.t)
  : Steel bool
  (A.varray ptr)
  (fun _ -> A.varray ptr)
  (requires fun _ ->
    A.length ptr >= US.v n
  )
  (ensures fun h0 b h1 ->
    A.length ptr >= US.v n /\
    (b ==> zf_u8 (Seq.slice (A.asel ptr h1) 0 (US.v n)))
  )

assume val memcpy_u8
  (dest src: array U8.t) (n: US.t)
  : Steel (array U8.t)
  (A.varray dest `star` A.varray src)
  (fun _ -> A.varray dest `star` A.varray src)
  (requires fun _ ->
    A.length dest >= US.v n /\
    A.length src >= US.v n
  )
  (ensures fun h0 r h1 ->
    A.length dest >= US.v n /\
    A.length src >= US.v n /\
    Seq.slice (A.asel dest h1) 0 (US.v n)
    ==
    Seq.slice (A.asel src h0) 0 (US.v n) /\
    A.asel src h1 == A.asel src h0
  )

open FStar.Mul

assume val builtin_mul_overflow(x y: US.t)
  : Pure US.t
  (requires True)
  (ensures fun r ->
    US.fits (US.v x * US.v y) /\
    US.v r == US.v x * US.v y
  )
