module Config

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module US = FStar.SizeT
module UP = FStar.PtrdiffT
module L =  FStar.List.Tot

open FStar.Mul
open Prelude

inline_for_extraction noextract
let u32_to_sz
  (x:U32.t)
  : Tot (y:US.t{US.v y == U32.v x})
  =
  US.uint32_to_sizet x

/// System page size is currently hardcoded to 4KB
inline_for_extraction
let page_size: U32.t = 4096ul

/// StarMalloc consists of three memory allocators:
/// - one for small allocations (fit on one page)
/// - one for medium allocations (fit on "a few" pages)
/// - one for large allocations (no restriction)

/// Size classes part of the small allocations allocator
noextract
let min_sc = 64
noextract
let max_sc = U32.v page_size
// TODO: this could be improved
// currently does not support size classes
// such that:
// - sc < 64, thus nb_slot sc > 64
// and
// - (nb_slots sc) % 64 <> 0
// this allows to only have a particular mechanism
// for the first u64 of the bitmap
// note: this mechanism does not rely on any loop!
type sc = x:U32.t{
  (
    U32.eq x 16ul \/
    U32.eq x 32ul \/
    (min_sc <= U32.v x /\ U32.v x <= max_sc)
  ) /\
  // https://www.intel.com/content/dam/develop/external/us/en/documents/mpx-linux64-abi.pdf
  // allocated arrays should have alignment of at least 16 bytes,
  // allowing use of SSE instructions
  (U32.v x % 16 == 0)
}

/// Size classes part of the medium allocations allocator
/// this controls the slab size, that is,
/// what the page size is to the small allocations allocator ;
/// slab size = 2 * max_sc_coef * page_size
/// max allocation size within a slab = max_sc_coef * page_size,
/// the other half of the slab is a guard region
inline_for_extraction
[@ CMacro ]
let max_sc_coef: v:US.t{
    1 <= US.v v /\
    US.fits (U32.v page_size * US.v v * 2)
  }
  =
  admit ();
  32sz

noextract
let max_sc_ex = U32.v page_size * US.v max_sc_coef

/// is to the medium allocations allocator
/// what the page_size is to the small allocations allocator
inline_for_extraction
let sc_ex_slab_size
  : v:US.t{US.v v > 0}
  = US.mul (u32_to_sz page_size) (US.mul max_sc_coef 2sz)

type sc_ex = x:U32.t{
  (max_sc <= U32.v x /\ U32.v x <= max_sc_ex) /\
  (U32.v x % U32.v page_size == 0)
  //// https://www.intel.com/content/dam/develop/external/us/en/documents/mpx-linux64-abi.pdf
  //// allocated arrays should have alignment of at least 16 bytes,
  //// allowing use of SSE instructions
  //(U32.v x % 16 == 0)
}

type sc_union =
  | Sc of sc
  | Sc_ex of sc_ex

inline_for_extraction
let get_sc (scu: sc_union{Sc? scu})
  : sc
  = match scu with
  | Sc v -> v
inline_for_extraction
let get_sc_ex (scu: sc_union{Sc_ex? scu})
  : sc_ex
  = match scu with
  | Sc_ex v -> v
inline_for_extraction
let get_u32 (scu: sc_union)
  : U32.t
  = match scu with
  | Sc v -> v
  | Sc_ex v -> v

/// List of size classes used in each arena
inline_for_extraction noextract
val sc_list : (l:list sc_union{Cons? l})

//TODO: remove strict bound?
/// Number of size classes per arena (extended or not)
inline_for_extraction
[@ CMacro ]
val nb_size_classes: v:US.t{
  0 < US.v v /\
  US.v v == L.length sc_list
}

/// Number of normal size classes per arena
inline_for_extraction
[@ CMacro ]
val nb_size_classes_sc: v:US.t{
  0 <= US.v v /\
  US.v v <= US.v nb_size_classes /\
  US.v v == L.length (L.filter (fun v -> Sc? v) sc_list)
}

/// Number of extended size classes per arena
inline_for_extraction
[@ CMacro ]
val nb_size_classes_sc_ex: v:US.t{
  0 <= US.v v /\
  US.v v <= US.v nb_size_classes /\
  US.v v == L.length (L.filter (fun v -> Sc? v) sc_list)
}

val nb_size_classes_lemma (_:unit)
  : Lemma
  (US.v nb_size_classes_sc + US.v nb_size_classes_sc_ex
  =
  US.v nb_size_classes)

/// Controls whether extended size classes
/// (size classes whose size is >= page size)
/// are enabled
inline_for_extraction
val enable_extended_size_classes: bool

val enable_extended_size_classes_check (_:unit)
  : Lemma
  (not enable_extended_size_classes ==> nb_size_classes_sc_ex = 0sz)

/// Number of arenas
inline_for_extraction
[@ CMacro ]
val nb_arenas: v:US.t{US.v v > 0}

/// Reserved memory
/// maximum space available per size class (even extended)
/// <= metadata_max * page_size
inline_for_extraction
val metadata_max: v:US.t{
  US.v v > 0 /\
  US.fits (US.v v * U32.v page_size * US.v nb_size_classes * US.v nb_arenas) /\
  US.fits (US.v v * U32.v page_size) /\
  (US.v v) % (US.v max_sc_coef * 2) == 0
}

val metadata_max_up_fits (_:unit)
  : Lemma
  (UP.fits ((US.v metadata_max * U32.v page_size) * US.v nb_size_classes * US.v nb_arenas))

noextract inline_for_extraction
val alg_null: v:nat{v = US.v metadata_max + 1}
noextract inline_for_extraction
val alg_null_sizet: v:US.t{US.v v = US.v metadata_max + 1}

// guard pages mechanism
// given the slab allocator memory layout,
// is required to avoid basic large buffer overflows
// TODO: actually, this flag controls whether guard pages are unmapped, should be renamed enable_guard_pages_trap
inline_for_extraction
val enable_guard_pages: bool
inline_for_extraction
val guard_pages_interval: v:US.t{2 <= US.v v /\ US.fits (US.v metadata_max + US.v v)}

// quarantine mechanism
// for now, basic quarantine:
// when a slab becomes empty (from partial/full),
// it is never used again
inline_for_extraction
val enable_quarantine: bool
// controls whether quarantined slabs are unmapped
inline_for_extraction
val enable_quarantine_trap: bool
// controls whether quarantined slabs are protected
inline_for_extraction
val enable_quarantine_strict_trap: bool
inline_for_extraction
val quarantine_queue_length: v:US.t{0 < US.v v /\ US.v v <= US.v metadata_max}
inline_for_extraction
val quarantine_queue_threshold: v:US.t{0 < US.v v /\ US.v v < US.v quarantine_queue_length}

// zeroing mechanism (slabs)
// controls whether zeroing is checked at allocation
inline_for_extraction
val enable_zeroing_malloc: bool
// controls whether allocations are zeroed at deallocation
inline_for_extraction
val enable_zeroing_free: bool
// required
val enable_zeroing_lemma (_:unit)
  : Lemma
  (enable_zeroing_malloc ==> enable_zeroing_free)

// TODO: controls whether zeroing is done at allocation time

// slab_canaries
// controls whether canaries are set at allocation
inline_for_extraction
val enable_slab_canaries_malloc: bool
// controls whether canaries are checked at deallocation
inline_for_extraction
val enable_slab_canaries_free: bool
// required
val enable_slab_canaries_lemma (_:unit)
  : Lemma
  (enable_slab_canaries_free ==> enable_slab_canaries_malloc)
// magic values for canaries
inline_for_extraction
val slab_canaries_magic1: U8.t
inline_for_extraction
val slab_canaries_magic2: U8.t
