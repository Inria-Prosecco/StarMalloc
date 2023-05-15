module Config

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module US = FStar.SizeT
module UP = FStar.PtrdiffT

open FStar.Mul

// LATER: code could be improved so that this value is not hardcoded anymore
inline_for_extraction
let page_size: U32.t = 4096ul

inline_for_extraction
val nb_size_classes: v:US.t{
  US.v v > 0
}

inline_for_extraction
val metadata_max: v:US.t{
  US.v v > 0 /\
  US.fits (US.v v * U32.v page_size * US.v nb_size_classes) /\
  US.fits (US.v v * U32.v page_size)
}

val metadata_max_up_fits (_:unit)
  : Lemma
  (UP.fits (US.v metadata_max * U32.v page_size * US.v nb_size_classes))

noextract inline_for_extraction
val alg_null: v:nat{v = US.v metadata_max + 1}
noextract inline_for_extraction
val alg_null_sizet: v:US.t{US.v v = US.v metadata_max + 1}

//TODO: use  this variable
inline_for_extraction
val enable_guard_pages: bool
inline_for_extraction
val guard_pages_interval: v:US.t{2 <= US.v v /\ US.fits (US.v metadata_max + US.v v)}
