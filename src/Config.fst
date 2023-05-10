module Config

open FStar.Mul

let nb_size_classes = 9sz

inline_for_extraction noextract
let metadata_max' = 131072UL

module A = Steel.Array
let _ : squash (US.fits_u64) = A.intro_fits_u64 ()

let metadata_max =
  US.fits_u64_implies_fits (U32.v page_size * U64.v metadata_max' * US.v nb_size_classes);
  US.fits_u64_implies_fits (U64.v metadata_max');
  US.of_u64 metadata_max'

let alg_null = US.v metadata_max + 1

let alg_null_sizet = US.add metadata_max 1sz

let enable_guard_pages = true

let guard_pages_interval = 8sz
