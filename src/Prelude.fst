module Prelude

module U32 = FStar.UInt32
module US = FStar.SizeT

open Steel.Effect
open Steel.Array

let _ : squash (US.fits_u32) = intro_fits_u32 ()

inline_for_extraction noextract
let u32_to_sz
  (x:U32.t)
  : Tot (y:US.t{US.v y == U32.v x})
  =
  US.uint32_to_sizet x
