module Bitmap1

open FStar.UInt
open FStar.Mul

noextract
unfold let uint_of_bool (#n:nat{n <> 0}) (b: bool) : Tot (uint_t n)
  = if b then 1 else 0

noextract
unfold let bool_of_uint (#n:nat{n <> 0}) (b:uint_t n) : Tot bool
  = if b = 1 then true else false

val spec_bv_get (#n:pos{n <> 0}) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (let r1 = b / (pow2 m) % 2 in
  let r2 = bool_of_uint #n r1 in
  nth b (n - m - 1) = r2)

val spec_bv_set (#n:pos{n <> 0}) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    nth b (n - m - 1) = false)
  (ensures (
    let a = pow2_n m in
    let r = logor a b in
    r = a + b /\
    nth r (n - m - 1) = true))

val spec_bv_unset (#n:pos{n <> 0}) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    nth b (n - m - 1) = true)
  (ensures (
    let a = pow2_n m in
    let r = logand (lognot a) b in
    r = b - a /\
    nth r (n - m - 1) = false))
