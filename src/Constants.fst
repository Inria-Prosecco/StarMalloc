module Constants

module U32 = FStar.UInt32
module US = FStar.SizeT

open Prelude
open FStar.Mul

// LATER: code could be improved so that this value is not hardcoded anymore
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
inline_for_extraction noextract
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

/// Size classes part of the medium allocations allocator
/// this controls the slab size, that is,
/// what the page size is to the small allocations allocator ;
/// slab size = 2 * max_sc_coef * page_size
/// max allocation size within a slab = max_sc_coef * page_size,
/// the other half of the slab is a guard region
inline_for_extraction
//[@ CMacro ]
let max_sc_coef: v:US.t{
    1 <= US.v v /\
    US.fits (U32.v page_size * US.v v * 2)
  }
  =
  [@inline_let] let v = 32sz in
  assert_norm (U32.v page_size * US.v v * 2 < pow2 32);
  US.fits_u32_implies_fits (U32.v page_size * US.v v * 2);
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
  True
  //(U32.v x % U32.v page_size == 0)
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
// generic, should not be extracted
noextract inline_for_extraction
let get_u32 (scu: sc_union)
  : U32.t
  = match scu with
  | Sc v -> v
  | Sc_ex v -> v
