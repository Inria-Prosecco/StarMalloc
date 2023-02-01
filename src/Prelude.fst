module Prelude

module US = FStar.SizeT

open Steel.Effect
open Steel.Array

let _ : squash (US.fits_u32) = intro_fits_u32 ()
