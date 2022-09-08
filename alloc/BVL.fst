module BVL

open FStar.Mul
module U64 = FStar.UInt64
module U32 = FStar.UInt32

let div64_shift (k: U64.t)
  : Pure U64.t
  (requires True)
  (ensures fun r -> r == U64.div k 64UL)
  =
  let open FStar.Tactics in
  assert (pow2 6 == 64) by (norm []);
  FStar.UInt.shift_right_value_aux_3 #U64.n (U64.v k) 6;
  assert (U64.v k / 64 == FStar.UInt.shift_right (U64.v k) 6);
  let x1 = U64.div k 64UL in
  let x2 = U64.shift_right k 6ul in
  assert (x1 == x2);
  x2

let mul64_shift (k: U64.t)
  : Pure U64.t
  (requires U64.v k < FStar.UInt.max_int 32)
  (ensures fun r -> r == U64.mul k 64UL)
  =
  let open FStar.Tactics in
  assert (pow2 6 == 64) by (norm []);
  FStar.UInt.shift_left_value_aux_3 #U64.n (U64.v k) 6;
  assert (U64.v k * 64 == FStar.UInt.shift_left (U64.v k) 6);
  let x1 = U64.mul k 64UL in
  let x2 = U64.shift_left k 6ul in
  assert (x1 == x2);
  x2

let uint32_to_uint64 (x: U32.t)
  : Pure U64.t
  (requires True)
  (ensures fun r -> U64.v r == U32.v x)
  = FStar.Int.Cast.uint32_to_uint64 x
//let uint64_to_uint32 (x: U64.t)
//  : Pure U32.t
//  (requires U64.v x < FStar.UInt.max_int 32)
//  (ensures fun r -> U32.v r == U64.v x)
//  = FStar.Int.Cast.uint64_to_uint32 x

let pow_not_null (k: nat)
  : Lemma
  (pow2 k > 0)
  = ()

let div64_shift2 (k: U64.t) (s: U32.t)
  : Pure U64.t
  (requires U32.v s < U64.n)
  (ensures fun r -> U64.v r = U64.v k / (pow2 (U32.v s)))
  =
  FStar.UInt.shift_right_value_aux_3 #U64.n (U64.v k) 6;
  assert (U64.v k / (pow2 (U32.v s))
  == FStar.UInt.shift_right (U64.v k) (U32.v s));
  let x2 = U64.shift_right k s in
  x2

let logand1 (x: U64.t)
  : Lemma
  (FStar.UInt.logand (U64.v x) 1 == U64.v x % 2)
  =
  FStar.UInt.logand_mask #64 (U64.v x) 1
