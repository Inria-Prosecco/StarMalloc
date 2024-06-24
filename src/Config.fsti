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

open Constants

/// List of size classes used in each arena
inline_for_extraction noextract
val sc_list : (l:list sc{Cons? l /\ L.mem page_size l})

/// Number of size classes per arena
inline_for_extraction
[@ CMacro ]
val nb_size_classes: v:US.t{US.v v > 0 /\ US.v v == L.length sc_list}

noextract
unfold type sc_selection_f = (x:U32.t) -> Pure US.t
  (requires
    U32.v x <= max_sc)
  (ensures fun r ->
    US.v r < US.v nb_size_classes /\
    U32.v x <= U32.v (L.index sc_list (US.v r))
  )

/// Size class selection (fast path)
inline_for_extraction noextract
val sc_selection : sc_selection_f

// controls whether size class selection fast path is used
inline_for_extraction
val enable_sc_fast_selection: bool

/// Number of arenas
inline_for_extraction
[@ CMacro ]
val nb_arenas: v:US.t{US.v v > 0}

inline_for_extraction
val metadata_max: v:US.t{
  US.v v > 0 /\
  US.fits (US.v v * U32.v page_size * US.v nb_size_classes * US.v nb_arenas) /\
  US.fits (US.v v * U32.v page_size)
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
// TODO: actually, this flag controls whether guard pages are unmapped
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
