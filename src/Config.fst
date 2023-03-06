module Config

open Prelude

open FStar.Mul

inline_for_extraction noextract
let metadata_max' = 131072ul

let metadata_max =
  US.fits_u32_implies_fits (U32.v page_size * U32.v metadata_max');
  US.of_u32 metadata_max'

let alg_null = US.v metadata_max + 1

let alg_null_sizet = US.add metadata_max 1sz
