module PtrdiffWrapper

module U32 = FStar.UInt32
module US = FStar.SizeT
module UP = FStar.PtrdiffT
module U64 = FStar.UInt64

open FStar.Mul
open Config

// conservative axiomatization, C23 changed guarantees about ptrdiff_t bit width
//TODO: add const qualifier/upstream it to FStar.PtrdiffT
//assume val ptrdiff_max: v:UP.t{
//  UP.v v >= pow2 16 - 1 /\
//  (exists (k:nat). UP.v v = pow2 k - 1)
//}

//TODO: remove this hardcoded constant
//currently equal to (PTRDIFF_MAX/2)+1,
//that is, 2^62 on x86_64-Linux

open MiscArith

let mmap_bound : v:US.t{
  US.fits (US.v v + 2) /\
  US.fits (US.v v + U32.v page_size) /\
  US.v v % U32.v page_size = 0
}
  =
  [@inline_let] let x = pow2 62 in
  assume (US.fits x);
  assume (US.fits (x + 2));
  assume (US.fits (x + U32.v page_size));
  pow2_mod 12 62;
  normalize_term (US.uint_to_t x)

//let mmap_bound : v:US.t{
//  US.fits (US.v v + 2) /\
//  US.fits (US.v v + U32.v page_size) /\
//  US.v v % U32.v page_size = 0
//}
//  =
//  let ptrdiff_max_as_sizet = UP.ptrdifft_to_sizet ptrdiff_max in
//  // US.fits(x) where x = 2^n-1
//  // y = x/2 = (2^n-1)/2 = 2^{n-1}-1
//  let r = US.add (US.div ptrdiff_max_as_sizet 2sz) 1sz in
//  eliminate exists (k:nat). UP.v ptrdiff_max = pow2 k - 1
//    returns (US.v r % U32.v page_size = 0)
//    with _. (
//      assert (UP.v ptrdiff_max == pow2 k - 1);
//      assert (US.v r == pow2 (k-1));
//      assert (U32.v page_size == pow2 12);
//      pow2_is_increasing 12 (k-1);
//      pow2_mod 12 (k-1);
//      ()
//  );
//  r

module FML = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
noextract
let nearest_multiple_upper_rounding
  (n: nat)
  (multiple: nat{multiple > 0})
  : Pure nat
  (requires True)
  (ensures fun r ->
    r >= 0 /\
    r % multiple == 0 /\
    r >= n /\
    r - n < multiple
  )
  =
  if n % multiple <> 0
  then (
    let r = n - (n % multiple) + multiple in
    FML.euclidean_division_definition n multiple;
    assert (n - (n % multiple) == (n/multiple)*multiple);
    lemma_mod_mul2 (n/multiple) multiple multiple;
    assert ((n - (n % multiple)) % multiple == 0);
    lemma_mod_plus2 (n - (n % multiple)) multiple multiple;
    r
  ) else n

let rec nearest_multiple_upper_rounding_lemma
  (n: nat)
  (multiple: nat{multiple > 0})
  (k: nat)
  : Lemma
  (requires k >= n /\ k % multiple == 0)
  (ensures
    k >= nearest_multiple_upper_rounding n multiple
  )
  (decreases k)
  =
  let n' = nearest_multiple_upper_rounding n multiple in
  assert (n' >= n /\ n' % multiple == 0);
  if k < n'
  then (
    assert (n' > n);
    assert (n % multiple <> 0);
    let diff = n' - k in
    assert (0 < diff);
    assert (n' % multiple == 0);
    assert (k % multiple == 0);
    lemma_mod_add_inv k multiple;
    assert ((-k) % multiple == 0);
    lemma_mod_plus2 (-k) n' multiple;
    assert (diff % multiple == 0);
    assert (diff >= multiple);
    if diff >= multiple
    then nearest_multiple_upper_rounding_lemma n multiple (k - multiple)
    else ()
 ) else ()

noextract
let spec_mmap_actual_size (size: nat)
  : Pure nat
  (requires True)
  (ensures fun r ->
    r >= 0 /\
    r % (U32.v page_size) == 0 /\
    r >= size /\
    r - size < (U32.v page_size)
  )
  =
  nearest_multiple_upper_rounding size (U32.v page_size)

let mmap_actual_size (size: US.t)
  : Pure US.t
  (requires
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun r ->
    US.v r == spec_mmap_actual_size (US.v size)
  )
  =
  let rem = US.rem size (u32_to_sz page_size) in
  if rem <> 0sz
  then US.add (US.sub size rem) (u32_to_sz page_size)
  else size
#pop-options
