module Config

open FStar.Mul

// required for metadata_max values
// such that nb_size_classes * page_size * metadata_max > max_int 32
module A = Steel.Array
let _ : squash (US.fits_u64)
  = A.intro_fits_u64 ()
let _ : squash (UP.fits (FStar.Int.max_int 64))
  = A.intro_fits_ptrdiff64 ()

inline_for_extraction noextract
let metadata_max' = 1048576UL

let metadata_max =
  US.fits_u64_implies_fits (U32.v page_size * U64.v metadata_max' * US.v nb_size_classes * US.v nb_arenas);
  US.fits_u64_implies_fits (U64.v metadata_max');
  US.of_u64 metadata_max'

let metadata_max_up_fits _ = ()

let alg_null = US.v metadata_max + 1

let alg_null_sizet = US.add metadata_max 1sz

// guard pages
let enable_guard_pages = true
let guard_pages_interval = 8sz

// quarantine
let enable_quarantine = true
let enable_quarantine_trap = true

// zeroing
let enable_zeroing = true

// slab canaries
let enable_slab_canaries = true

let slab_canaries_magic1 = 42uy
let slab_canaries_magic2 = 23uy
