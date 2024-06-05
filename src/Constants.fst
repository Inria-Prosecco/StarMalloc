module Constants

module U32 = FStar.UInt32

open FStar.Mul

// LATER: code could be improved so that this value is not hardcoded anymore
inline_for_extraction
let page_size: U32.t = 4096ul

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
let sc = x:U32.t{
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
