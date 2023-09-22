module Config

open FStar.Mul
module A = Steel.Array

// the allocator uses a contiguous region
// formed by all arenas containing all size classes,
// of the following size:
// s = nb_arenas * nb_size_classes * metadata_max * page_size
// thus, these hypotheses are required for practical use
// note: when quarantine will be improved,
// it should be impossible to use the allocator even
// with smaller values of metadata_max
let _ : squash (US.fits_u64)
  = A.intro_fits_u64 ()
let _ : squash (UP.fits (FStar.Int.max_int 64))
  = A.intro_fits_ptrdiff64 ()

let sc_list = [
    16ul; 32ul; 64ul;
    128ul; 256ul; 512ul;
    1024ul; 2048ul; 4096ul
  ]

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
  // as FStar.SizeT.t is internally represented
  // as FStar.UInt64.t and yields a type mismatch
  // between uint64_t (result after this possible normalization)
  // and size_t (expected type)
  US.fits_u64_implies_fits_32 ();
  US.of_u32 l_as_u32

let nb_arenas = 4sz

inline_for_extraction noextract
let metadata_max' = 1048576UL

//DO NOT EDIT
let metadata_max_fits_lemma (_:unit)
  : Lemma
  (let x = U32.v page_size * U64.v metadata_max' * US.v nb_size_classes * US.v nb_arenas in
  x < FStar.UInt.max_int U64.n /\
  x < FStar.Int.max_int U64.n)
  =
  let l = normalize_term (L.length sc_list) in
  normalize_term_spec (L.length sc_list);
  assert (US.v nb_size_classes = l)

//DO NOT EDIT, edit metadata_max' instead
let metadata_max =
  metadata_max_fits_lemma ();
  US.fits_u64_implies_fits (U32.v page_size * U64.v metadata_max' * US.v nb_size_classes * US.v nb_arenas);
  US.fits_u64_implies_fits (U64.v metadata_max');
  US.of_u64 metadata_max'

//DO NOT EDIT
let metadata_max_up_fits _ =
  metadata_max_fits_lemma ()

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
