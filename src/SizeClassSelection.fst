module SizeClassSelection

open Utils2
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module FU = FStar.UInt
module FBV = FStar.BitVector
module FIC = FStar.Int.Cast

open ExternUtils

open FStar.Mul

// misc
let from_vec_property (#n: pos) (a: FBV.bv_t n) (s:nat{s <= n})
  : Lemma
  (requires True)
  (ensures
    FU.from_vec a
    ==
    FU.from_vec #s (Seq.slice a 0 s) * pow2 (n - s) + FU.from_vec #(n - s) (Seq.slice a s n)
  )
  (decreases (n-s))
  =
  if s = n
  then ()
  else FU.from_vec_propriety a s

/// Sizeclass selection: simple case
///
//TODO: powers of two from 16 to 4096

/// Sizeclass selection: complex case

// @clz
let clz_to_seq_zero_vec_aux (x: U64.t) (r: U32.t) (k: nat{k < U32.v r})
  : Lemma
  (requires
    U64.v x > 0 /\
    U32.v r < 64 /\
    //clz x == r /\
    nth_is_zero x (U32.uint_to_t (63 - k))
  )
  (ensures (
    let x_as_seq = FU.to_vec (U64.v x) in
    let idx = U32.v r in
    let s1, s2 = Seq.split x_as_seq idx in
    Seq.index s1 k = false
  ))
  =
  let x_as_seq = FU.to_vec (U64.v x) in
  assert (Seq.index x_as_seq k = false);
  let idx = U32.v r in
  let s1, s2 = Seq.split x_as_seq idx in
  Seq.lemma_index_slice x_as_seq 0 idx k

let clz_to_seq_zero_vec (x: U64.t) (r: U32.t)
  : Lemma
  (requires
    U64.v x > 0 /\
    0 < U32.v r /\
    U32.v r < 64 /\
    clz x == r
  )
  (ensures (
    let x_as_seq = FU.to_vec (U64.v x) in
    let idx = U32.v r in
    let s1, s2 = Seq.split x_as_seq idx in
    s1 == FBV.zero_vec #idx
  ))
  =
  let x_as_seq = FU.to_vec (U64.v x) in
  let idx = U32.v r in
  let s1, s2 = Seq.split x_as_seq idx in
  Classical.forall_intro (Classical.move_requires (
    clz_to_seq_zero_vec_aux x r
  ));
  assert (forall (k:nat{k < idx}). Seq.index s1 k = false);
  Seq.lemma_eq_intro s1 (FBV.zero_vec #idx)

#push-options "--fuel 0 --ifuel 0"
let clz_to_seq (x: U64.t) (r: U32.t)
  : Lemma
  (requires
    U64.v x > 0 /\
    clz x == r)
  (ensures
    U64.v x >= pow2 (64 - U32.v r - 1) /\
    U64.v x < pow2 (64 - U32.v r)
  )
  =
  let x_as_seq = FU.to_vec (U64.v x) in
  let idx = U32.v r in
  let s1, s2 = Seq.split x_as_seq idx in
  from_vec_property #64 x_as_seq idx;
  let x1 = FU.from_vec #idx s1 in
  let x2 = FU.from_vec #(64 - idx) s2 in
  assert (U64.v x == x1 * pow2 (64 - U32.v r) + x2);
  assert (x2 < pow2 (64 - idx));
  if idx > 0 then (
    clz_to_seq_zero_vec x r
  ) else ();
  assert (x1 == 0);
  let s21, s22 = Seq.split s2 1 in
  from_vec_property #(64 - idx) s2 1;
  let x21 = FU.from_vec #1 s21 in
  assert (s21 `Seq.equal` Seq.create 1 true);
  assert (s21 `Seq.equal` FBV.ones_vec #1);
  assert (x21 = 1);
  let x22 = FU.from_vec #(64 - idx - 1) s22 in
  assert (x2 == x21 * pow2 (64 - U32.v r - 1) + x22);
  assert (x2 >= pow2 (64 - U32.v r - 1))
#pop-options

noextract inline_for_extraction
let log2u64_impl (x: U64.t)
  : Pure U32.t
  (requires U64.v x > 0)
  (ensures fun r ->
    U32.v r < 64 /\
    U64.v x >= pow2 (U32.v r) /\
    U64.v x < pow2 (U32.v r + 1)
  )
  =
  let r = clz x in
  clz_to_seq x r;
  U32.sub (U32.uint_to_t 63) r

[@"opaque_to_smt"]
let log2u64 (x: U64.t)
  : Pure U32.t
  (requires U64.v x > 0)
  (ensures fun r ->
    U32.v r < 64 /\
    U64.v x >= pow2 (U32.v r) /\
    U64.v x < pow2 (U32.v r + 1)
  )
  = log2u64_impl x

noextract
let log2u64_spec (x: nat)
  : Pure nat
  (requires
    x > 0 /\
    x <= 4096)
  (ensures fun r ->
    r < 64 /\
    x >= pow2 r /\
    x < pow2 (r + 1)
  )
  = U32.v (log2u64 (U64.uint_to_t x))

module FML = FStar.Math.Lemmas

let rec log2u64_eq_lemma_aux (x: nat) (r1 r2: nat)
  : Lemma
  (requires
    x > 0 /\
    x >= pow2 r1 /\
    x < pow2 (r1 + 1) /\
    x >= pow2 r2 /\
    x < pow2 (r2 + 1)
  )
  (ensures
    r1 = r2
  )
  =
  if x = 1 then ()
  else log2u64_eq_lemma_aux (x/2) (r1-1) (r2-1)

let log2u64_eq_lemma (x:nat) (r: nat)
  : Lemma
  (requires
    x > 0 /\
    x <= 4096 /\
    x >= pow2 r /\
    x < pow2 (r + 1))
  (ensures
    log2u64_spec x == r
  )
  =
  let r2 = log2u64_spec x in
  log2u64_eq_lemma_aux x r r2

noextract
let sc_list_f_aux_2 (x y: nat)
  : nat
  =
  pow2 (x + 6) + y * pow2 (x + 4)

noextract
let sc_list_f_aux (z: nat)
  : nat
  =
  let x = z / 4 in
  let y = z % 4 in
  sc_list_f_aux_2 x y

noextract
let sc_list_f
  : nat -> nat
  =
  fun x ->
    if x <= 1
    then 16 * (x+1)
    else sc_list_f_aux (x - 2)

open MiscArith

noextract
let nearest_multiple_upper_div
  (n: nat)
  (multiple: nat{multiple > 0})
  =
  (n + multiple - 1)/multiple

noextract
let nearest_multiple_upper_div_lemma
  (n: nat)
  (multiple: nat{multiple > 0})
  : Lemma
  (let r = nearest_multiple_upper_div n multiple in
  multiple * (r - 1) < n /\
  n <= multiple * r)
  =
  ()

inline_for_extraction noextract
let upper_div_impl
  (x: U32.t)
  (y: U32.t)
  : Pure U32.t
  (requires
    U32.v x <= 4096 /\
    U32.v y <= 4096 /\
    (exists (k:nat). U32.v y == pow2 k)
  )
  (ensures fun r ->
    U32.v r == nearest_multiple_upper_div (U32.v x) (U32.v y)
  )
  =
  let v = U32.sub y 1ul in
  let x' = U32.add x v in
  let r = U32.div x' y in
  r

inline_for_extraction noextract
let fast_upper_div_impl
  (x: U32.t)
  (y: U32.t)
  (k: U32.t)
  : Pure U32.t
  (requires
    U32.v x <= 4096 /\
    U32.v y <= 4096 /\
    //(exists (k:nat).
    U32.v y == pow2 (U32.v k) /\
    U32.v k < 32
  )
  (ensures fun r ->
    U32.v r == nearest_multiple_upper_div (U32.v x) (U32.v y)
  )
  =
  let v = U32.sub y 1ul in
  let x' = U32.add x v in
  let r = U32.shift_right x' k in
  r

module FML = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
noextract
let inv_aux_2 (x: nat)
  : Pure (nat & nat)
  (requires x >= 64 /\
    x <= 4096
  )
  (ensures fun r ->
    let y, z = r in
    x <= sc_list_f_aux_2 y z /\
    y <= 6 /\
    z <= 4 /\
    (y = 6 ==> z = 0)
  )
  =
  let log = log2u64_spec x in
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 12 == 4096);
  if log < 6 then FML.pow2_le_compat 6 (log+1);
  if log > 12 then FML.pow2_lt_compat log 12;
  assert (6 <= log /\ log <= 12);
  let align = pow2 log in
  let align2 = pow2 (log - 2) in
  let y = log - 6 in
  let z = nearest_multiple_upper_div (x - align) align2 in
  if (z >= 5)
  then (
    assert (x - align > 4 * align2);
    FML.pow2_plus (log - 2) 2;
    assert_norm (pow2 2 == 4);
    assert (align == 4 * align2);
    FML.pow2_double_sum log;
    assert (align + align == pow2 (log + 1))
  )
  else ();
  if (y = 6)
  then (
    assert (log == 12);
    assert (x >= pow2 12);
    assert_norm (pow2 12 == 4096);
    assert (z == 0)
  ) else ();
  y, z

noextract
let inv_aux (x: nat)
  : Pure (nat)
  (requires x >= 64 /\
    x <= 4096
  )
  (ensures fun r ->
    x <= sc_list_f_aux r /\
    r <= 24
  )
  =
  let y, z = inv_aux_2 x in
  y * 4 + z

module T = FStar.Tactics

noextract
let inv (x: nat)
  : Pure (nat)
  (requires
    x <= 4096
  )
  (ensures fun r ->
    x <= sc_list_f r /\
    r <= 26
  )
  =
  if x <= 16
  then (
    assert (sc_list_f 0 == 16) by T.compute();
    0
  ) else if (x <= 32) then (
    assert (sc_list_f 1 == 32) by T.compute();
    1
  ) else if (x <= 64) then (
    // no 48-bytes size class, complicating things a bit
    //assert (sc_list_f 1 == 32) by T.compute();
    //(nearest_multiple_upper_div x 16) - 1
    assert (sc_list_f 2 == 64) by T.compute();
    //TODO: fixme, 16 and 32 size classes are thus disabled
    2
  ) else (
    inv_aux x + 2
  )

inline_for_extraction noextract
let inv_impl_aux_2 (x: U32.t)
  : Pure (U32.t & U32.t)
  (requires U32.v x >= 64 /\
    U32.v x <= 4096
  )
  (ensures fun r ->
    let y, z = r in
    let y', z' = inv_aux_2 (U32.v x) in
    U32.v y = y' /\
    U32.v z = z' /\
    U32.v x <= sc_list_f_aux_2 y' z'
  )
  =
  let x_as_u32 = x in
  let x_as_u64 = FIC.uint32_to_uint64 x_as_u32 in
  assert (U64.v x_as_u64 == U32.v x);
  let log = log2u64 x_as_u64 in
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 12 == 4096);
  if U32.v log < 6 then FML.pow2_le_compat 6 (U32.v log + 1);
  if U32.v log > 12 then FML.pow2_lt_compat (U32.v log) 12;
  let align = U32.shift_left 1ul log in
  let align2 = U32.shift_left 1ul (U32.sub log 2ul) in
  FML.pow2_lt_compat (U32.v log) (U32.v log - 2);
  assert (U32.v align2 < U32.v align);
  let y = U32.sub log 6ul in
  let z = fast_upper_div_impl (U32.sub x_as_u32 align) align2 (U32.sub log 2ul) in
  y, z

inline_for_extraction noextract
let inv_impl_aux (x: U32.t)
  : Pure (U32.t)
  (requires U32.v x >= 64 /\
    U32.v x <= 4096
  )
  (ensures fun r ->
    let r' = inv_aux (U32.v x) in
    U32.v r == r' /\
    U32.v x <= sc_list_f_aux (U32.v r)
  )
  =
  let y, z = inv_impl_aux_2 x in
  U32.add (U32.mul y 4ul) z

let inv_impl (x: U32.t)
  : Pure (U32.t)
  (requires
    U32.v x <= 4096
  )
  (ensures fun r ->
    let r' = inv (U32.v x) in
    U32.v r == r' /\
    U32.v x <= sc_list_f (U32.v r)
  )
  =
  if U32.lte x 16ul
  then 0ul
  else if U32.lte x 32ul
  then 1ul
  else if U32.lte x 64ul
  then 2ul
  else (
    U32.add (inv_impl_aux x) 2ul
  )

