module SizeTUtils

module FI = FStar.Int
module FIC = FStar.Int.Cast
module US = FStar.SizeT
module U32 = FStar.UInt32
module U16 = FStar.UInt16

let small_uint32_to_sizet (x: U32.t)
  : Pure US.t
  (requires U32.v x <= FI.max_int U16.n)
  (ensures fun r ->
    US.v r = U32.v x
  )
  =
  let x' = FIC.uint32_to_uint16 x in
  assert (U16.v x' = U32.v x);
  let r = US.uint16_to_sizet x' in
  r
