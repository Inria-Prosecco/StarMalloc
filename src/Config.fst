module Config

open FStar.Mul

// required for metadata_max values
// such that nb_size_classes * page_size * metadata_max > max_int 32
module A = Steel.Array
let _ : squash (US.fits_u64)
  = A.intro_fits_u64 ()

let _ : squash (US.fits_u32)
  = A.intro_fits_u32 ()

let _ : squash (UP.fits (FStar.Int.max_int 64))
  = A.intro_fits_ptrdiff64 ()

let sc_list = [
    16ul; 32ul; 64ul;
    128ul; 256ul; 512ul;
    1024ul; 2048ul; 4096ul
  ]

module U16 = FStar.UInt16
module U32 = FStar.UInt32

//DO NOT EDIT, edit sc_list instead
let nb_size_classes
  =
  assert_norm (L.length sc_list < U32.n);
  [@inline_let] let l = normalize_term (L.length sc_list) in
  normalize_term_spec (L.length sc_list);
  assert (l == L.length sc_list);
  [@inline_let] let l_as_u32 = normalize_term (U32.uint_to_t l) in
  normalize_term_spec (U32.uint_to_t l);
  assert (U32.v l_as_u32 == L.length sc_list);
  // do not normalize cast to size_t,
  // as it is internally represented uint64_t
  // and yields a type mismatch
  US.of_u32 l_as_u32

let nb_arenas = 4sz

inline_for_extraction noextract
let metadata_max' = 1048576UL

//DO NOT EDIT, edit metadata_max' instead
let metadata_max =
  admit ();
  assert_norm (U32.v page_size * U64.v metadata_max' * US.v nb_size_classes * US.v nb_arenas < U64.n);
  US.fits_u64_implies_fits (U32.v page_size * U64.v metadata_max' * US.v nb_size_classes * US.v nb_arenas);
  US.fits_u64_implies_fits (U64.v metadata_max');
  US.of_u64 metadata_max'

//DO NOT EDIT
let metadata_max_up_fits _ = ()
//DO NOT EDIT
let alg_null = US.v metadata_max + 1
//DO NOT EDIT
let alg_null_sizet = US.add metadata_max 1sz

// guard pages
let enable_guard_pages = true
let guard_pages_interval = 2sz

// quarantine
let enable_quarantine = true
let enable_quarantine_trap = true
let enable_quarantine_strict_trap = true

// zeroing
let enable_zeroing_malloc = true
let enable_zeroing_free = true
let enable_zeroing_lemma () = ()

// slab canaries
let enable_slab_canaries_malloc = true
let enable_slab_canaries_free = true
let enable_slab_canaries_lemma () = ()
let slab_canaries_magic1 = 42uy
let slab_canaries_magic2 = 23uy
