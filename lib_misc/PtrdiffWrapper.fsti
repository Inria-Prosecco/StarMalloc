module PtrdiffWrapper

module U32 = FStar.UInt32
module US = FStar.SizeT
module UP = FStar.PtrdiffT

open FStar.Mul
open Config

// conservative axiomatization, C23 changed guarantees about ptrdiff_t bit width
// this is an assume val
val ptrdiff_max: v:UP.t{
  UP.v v >= pow2 16 - 1 /\
  (exists (k:nat). UP.v v = pow2 k - 1)
}

open MiscArith

let mmap_bound : v:US.t{
  US.fits (US.v v + 2) /\
  US.fits (US.v v + U32.v page_size) /\
  US.v v % U32.v page_size = 0
}
  =
  let ptrdiff_max_as_sizet = UP.ptrdifft_to_sizet ptrdiff_max in
  // US.fits(x) where x = 2^n-1
  // y = x/2 = (2^n-1)/2 = 2^{n-1}-1
  let r = US.add (US.div ptrdiff_max_as_sizet 2sz) 1sz in
  eliminate exists (k:nat). UP.v ptrdiff_max = pow2 k - 1
    returns (US.v r % U32.v page_size = 0)
    with _. (
      assert (UP.v ptrdiff_max == pow2 k - 1);
      assert (US.v r == pow2 (k-1));
      assert (U32.v page_size == pow2 12);
      pow2_is_increasing 12 (k-1);
      pow2_mod 12 (k-1);
      ()
  );
  r
  //normalize_term r
