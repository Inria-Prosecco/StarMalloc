module Config

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module US = FStar.SizeT

open FStar.Mul

// LATER: code could be improved so that this value is not hardcoded anymore
inline_for_extraction
let page_size: U32.t = 4096ul

inline_for_extraction
val metadata_max: v:US.t{US.fits (US.v v * U32.v page_size)}

noextract inline_for_extraction
val alg_null: v:nat{v = US.v metadata_max + 1}
noextract inline_for_extraction
val alg_null_sizet: v:US.t{US.v v = US.v metadata_max + 1}
