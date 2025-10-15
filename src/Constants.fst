module Constants

module U32 = FStar.UInt32
module US = FStar.SizeT

open FStar.Mul
open Prelude

// LATER: code could be improved so that this value is not hardcoded anymore
inline_for_extraction
let page_size: U32.t = 4096ul

//inline_for_extraction
let max_slab_size: U32.t = 131072ul

//inline_for_extraction
//let max_slab_size: US.t = US.uint32_to_sizet max_slab_size'

// TODO: this could be improved
// currently does not support size classes
// such that:
// - sc < 64, thus nb_slot sc > 64
// and
// - (nb_slots sc) % 64 <> 0
// this allows to only have a particular mechanism
// for the first u64 of the bitmap
// note: this mechanism does not rely on any loop!
inline_for_extraction noextract
let sc = x:U32.t{
  //(
  //  U32.eq x 16ul \/
  //  U32.eq x 32ul \/
  //  (min_sc <= U32.v x /\ U32.v x <= max_sc)
  //) /\
  // https://www.intel.com/content/dam/develop/external/us/en/documents/mpx-linux64-abi.pdf
  // allocated arrays should have alignment of at least 16 bytes,
  // allowing use of SSE instructions
  U32.v x > 0 /\
  (U32.v x) % 16 == 0 /\
  U32.fits (U32.v x * 256)
}

inline_for_extraction noextract
let sc_p (x: sc) (y: U32.t)
  =
  // bitmap handling: 256 bits max
  // supported number of slots: any value in S \cup {128, 256},
  // where S is the integer interval [[1, 64]]
  U32.v y <= 256 * U32.v x /\
  (
    // x = 16
    (U32.eq y (U32.mul x 256ul)) \/
    //(U32.div y 256ul)) \/
    // x = 32
    (U32.eq y (U32.mul x 128ul)) \/
    //(U32.div y 128ul)) \/
    // x >= 64
    (U32.lte y (U32.mul x 64ul))
  ) /\
  // why is this useful?
  U32.v y <= U32.v max_slab_size /\
  // one slot fits on a slab
  U32.v x <= U32.v y /\
  // for guard pages + quarantined pages: permission management is done using pages
  (U32.v y) % (U32.v page_size) == 0 /\
  // alignement
  (U32.v max_slab_size) % (U32.v y) == 0 /\
  // small sizeclasses: no page boundary crossing, useful in SizeClass.fst
  // to retrieve alignment
  (U32.v x <= 4096 ==> U32.v y <= 4096) /\
  True

type sc_full' = {
  sc: sc;
  slab_size: v:U32.t{sc_p sc v};
  md_max: v:US.t{
    US.fits (U32.v slab_size * US.v v)
  };
}
