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

open Utils2

/// src/ExternUtils.fst contains axiomatizations of various compiler builtins or basic C code.
///
let check (_:unit)
  =
  assert (not (nth_is_zero U64.one (U32.uint_to_t 0)));
  assert (nth_is_zero U64.one (U32.uint_to_t 1));
  ()

// bitwise-operations compiler builtin
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

// count leading zeroes,
// returns r, the number of rightmost bits set to zero
// bitwise-operations compiler builtin
assume val clz (x: U64.t)
  : Pure U32.t
  (requires U64.v x > 0)
  (ensures fun r ->
    U32.v r < 64 /\
    (forall (k:nat{0 <= k /\ k < U32.v r}). nth_is_zero x (U32.uint_to_t (63 - k))) /\
    not (nth_is_zero x (U32.uint_to_t (63 - U32.v r)))
  )

open FStar.Mul

// compiler builtin
assume val builtin_mul_overflow(x y: US.t)
  : Pure US.t
  (requires True)
  (ensures fun r ->
    US.fits (US.v x * US.v y) /\
    US.v r == US.v x * US.v y
  )

// explicit_bzero zeroing function wrapper
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
    // n first bytes of ptr are zeroes after execution of the function
    zf_u8 (Seq.slice (A.asel ptr h1) 0 (US.v n))
  )

// check whether an array is zeroed
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

// memcpy function wrapper
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
