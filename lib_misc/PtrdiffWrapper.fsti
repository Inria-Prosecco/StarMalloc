module PtrdiffWrapper

module U32 = FStar.UInt32
module US = FStar.SizeT
module UP = FStar.PtrdiffT
module U64 = FStar.UInt64

open FStar.Mul
open Constants
open Config

open MiscArith
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
