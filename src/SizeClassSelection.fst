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

#push-options "--fuel 0 --ifuel 0"

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

#push-options "--fuel 1 --ifuel 0"
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
#pop-options

//let log2u64_eq_lemma (x: U64.t) (r: U32.t)
//  : Lemma
//  (requires
//    U64.v x > 0 /\
//    pow2 (U32.v r) <= U64.v x /\
//    U64.v x < pow2 (U32.v r + 1))
//  (ensures
//    U32.v (log2u64 x) == U32.v r
//  )
//  =
//  let r2 = log2u64 x in
//  log2u64_eq_lemma_aux (U64.v x) (U32.v r) (U32.v r2)

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

let log2u64_spec_eq_lemma (x:nat) (r: nat)
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
let sc_list_f2_aux (x y: nat)
  : nat
  =
  pow2 (x + 6) + y * pow2 (x + 4)

noextract
let sc_list_f2 (z: nat)
  : nat
  =
  let x = z / 4 in
  let y = z % 4 in
  sc_list_f2_aux x y

noextract
let sc_list_f1 (x: nat)
  = 16 * x

noextract
let sc_list_f3 (x: nat)
  = 4096 * x

module T = FStar.Tactics

noextract
let sc_list_f
  : nat -> nat
  =
  fun x ->
    if x <= 1 then sc_list_f1 (x+1)
    else if x <= 26 then sc_list_f2 (x - 2)
    else sc_list_f3 (x - 25)

let sort (x:nat)
  : v:nat{v < 3}
  =
  if x <= 1 then 0
  else if x <= 26 then 1
  else 2

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
    FU.fits (U32.v x + U32.v y) U32.n /\
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

#push-options "--z3rlimit 30"
noextract
let inv2_aux (x: nat)
  : Pure (nat & nat)
  (requires
    64 <= x /\
    x <= 4096
  )
  (ensures fun r ->
    let y, z = r in
    x <= sc_list_f2_aux y z /\
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
#pop-options

noextract
let inv2 (x: nat)
  : Pure (nat)
  (requires
    64 <= x /\
    x <= 4096
  )
  (ensures fun r ->
    x <= sc_list_f2 r /\
    r <= 24
  )
  =
  let y, z = inv2_aux x in
  y * 4 + z

module T = FStar.Tactics

noextract
let inv3 (bound_input bound_len: nat) (x: nat)
  : Pure nat
  (requires
    4096 <= x /\
    x <= bound_input /\
    bound_input % 4096 = 0 /\
    bound_len = (bound_input/4096)
  )
  (ensures fun r ->
    x <= sc_list_f3 r /\
    r <= bound_len
  )
  =
  let r = nearest_multiple_upper_div x 4096 in
  assert (r*4096 <= bound_input);
  r

noextract
let inv (bound_input bound_len: nat) (x: nat)
  : Pure nat
  (requires
    x <= bound_input /\
    bound_input % 4096 = 0 /\
    bound_len = (bound_input/4096)
  )
  (ensures fun r ->
    x <= sc_list_f r /\
    r <= 26 + bound_len
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
  ) else if x <= 4096 then (
    inv2 x + 2
  ) else (
    inv3 bound_input bound_len x + 25
  )

#push-options "--z3rlimit 50"
inline_for_extraction noextract
let inv_impl2_aux (x: U32.t)
  : Pure (U32.t & U32.t)
  (requires U32.v x >= 64 /\
    U32.v x <= 4096
  )
  (ensures fun r ->
    let y, z = r in
    let y', z' = inv2_aux (U32.v x) in
    U32.v y = y' /\
    U32.v z = z' /\
    U32.v x <= sc_list_f2_aux y' z'
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
#pop-options

inline_for_extraction noextract
let inv_impl2 (x: U32.t)
  : Pure U32.t
  (requires U32.v x >= 64 /\
    U32.v x <= 4096
  )
  (ensures fun r ->
    let r' = inv2 (U32.v x) in
    U32.v r == r' /\
    U32.v x <= sc_list_f2 (U32.v r)
  )
  =
  let y, z = inv_impl2_aux x in
  U32.add (U32.mul y 4ul) z

let log2u64_ceil (x: U64.t)
  : Pure U32.t
  (requires U64.v x > 1)
  (ensures fun r ->
    U32.v r < 64 /\
    U64.v x > pow2 (U32.v r) /\
    U64.v x <= pow2 (U32.v r + 1)
  )
  =
  let log = log2u64_impl (U64.sub x 1UL) in
  log

inline_for_extraction noextract
let inv_impl3 (bound_input bound_len x: U32.t)
  : Pure U32.t
  (requires
    4096 < U32.v x /\
    FU.fits (U32.v x + 4096) U32.n /\
    U32.v x <= U32.v bound_input /\
    U32.v bound_input = pow2 (U32.v bound_len + 12)
  )
  (ensures fun r ->
    U32.v x <= sc_list_f3 (U32.v r) /\
    U32.v r <= U32.v bound_len
  )
  =
  assert_norm (pow2 12 = 4096);
  let x_as_u64 = FIC.uint32_to_uint64 x in
  let log = log2u64_ceil x_as_u64 in
  assume (U32.v log >= 12);
  admit ();
  U32.sub log 12ul

let inv_impl (bound_input bound_len x: U32.t)
  : Pure (U32.t)
  (requires
    U32.v x <= U32.v bound_input /\
    U32.v bound_input % 4096 = 0 /\
    U32.v bound_len = U32.v bound_input / 4096 /\
    U32.v x <= 4096
  )
  (ensures fun r ->
    let r' = inv (U32.v bound_input) (U32.v bound_len) (U32.v x) in
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
  else if U32.lte x 4096ul
  then U32.add (inv_impl2 x) 2ul
  else U32.add (inv_impl3 bound_input bound_len x) 27ul

let log2u64_is_mon_increasing (x y: nat)
  : Lemma
  (requires
    0 < x /\
    x <= y /\
    y <= 4096
  )
  (ensures
    log2u64_spec x <= log2u64_spec y
  )
  =
  let rx = log2u64_spec x in
  let ry = log2u64_spec y in
  if rx <= ry then ()
  else (
    FML.pow2_lt_compat rx ry;
    log2u64_spec_eq_lemma x ry
  )

let nearest_multiple_upper_div_is_mon_increasing
  (x y: nat)
  (multiple: nat{multiple > 0})
  : Lemma
  (requires x <= y)
  (ensures (
    let rx = nearest_multiple_upper_div x multiple in
    let ry = nearest_multiple_upper_div y multiple in
    rx <= ry
  ))
  =
  assert (x + multiple - 1 <= y + multiple - 1);
  FML.lemma_div_le (x + multiple - 1) (y + multiple - 1) multiple

#push-options "--z3rlimit 100"
let inv_aux_is_mon_increasing (x y: nat)
  : Lemma
  (requires
    64 <= x /\
    x <= y /\
    y <= 4096
  )
  (ensures (
    let rx = inv2 x in
    let ry = inv2 y in
    rx <= ry
  ))
  =
  let log_x = log2u64_spec x in
  let log_y = log2u64_spec y in
  log2u64_is_mon_increasing x y;
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 12 == 4096);
  if log_x < 6 then FML.pow2_le_compat 6 (log_x+1);
  if log_y > 12 then FML.pow2_lt_compat log_y 12;
  assert (6 <= log_x /\ log_x <= log_y /\ log_y <= 12);
  if log_x = log_y
  then (
    let align = pow2 log_x in
    let align2 = pow2 (log_x - 2) in
    nearest_multiple_upper_div_is_mon_increasing (x - align) (y - align) align2
  ) else ()
#pop-options

(*)
let inv_is_mon_increasing (x y: nat)
  : Lemma
  (requires
    x <= 4096 /\
    y <= 4096
  )
  (ensures (
    let rx = inv x in
    let ry = inv y in
    x <= y ==> rx <= ry
  ))
  =
  if x <= y then (
    if x <= 64
    then ()
    else inv_aux_is_mon_increasing x y
  ) else ()

#push-options "--z3rlimit 150"
let sc_list_f_aux_is_smon_increasing_lt
  (x y: nat)
  : Lemma
  (requires
    x < y
  )
  (ensures
    sc_list_f_aux x < sc_list_f_aux y /\
    sc_list_f_aux y - sc_list_f_aux x >= 16
  )
  =
  let rx = sc_list_f_aux x in
  let ry = sc_list_f_aux y in
  let x1 = x / 4 in
  let y1 = y / 4 in
  let x2 = x % 4 in
  let y2 = y % 4 in
  if x1 = y1 then (
    assert (y2 - x2 > 0);
    assert_norm (pow2 4 = 16);
    FML.pow2_le_compat (x1 + 4) 4;
    assert (ry - rx = (y2 - x2) * pow2 (x1 + 4))
  ) else (
    assert (x1 < y1);
    // first step: factorization of the difference
    let c = pow2 (x1 + 4) in
    FML.pow2_plus (x1 + 4) (y1 - x1 + 2);
    FML.pow2_plus (x1 + 4) (y1 - x1);
    assert (ry = c * (pow2 (y1 - x1 + 2) + y2 * pow2 (y1 - x1)));
    FML.pow2_plus (x1 + 4) 2;
    assert_norm (pow2 2 == 4);
    assert (rx = c * (4 + x2));
    let ry' = pow2 (y1 - x1 + 2) + y2 * pow2 (y1 - x1) in
    assert (ry = c * ry');
    let rx' = 4 + x2 in
    assert (rx = c * rx');
    FML.distributivity_sub_right c ry' rx';
    assert (ry - rx = c * (ry' - rx'));

    // second step: ry' - rx' > 0
    let c' = pow2 (y1 - x1) in
    FML.pow2_plus (y1 - x1) 2;
    assert (ry' = c' * (4 + y2));
    FML.pow2_le_compat (y1 - x1) 1;
    FML.lemma_mult_le_right (4 + y2) 2 c';
    assert (ry' >= 2 * (4 + y2));
    FML.lemma_mult_le_left 2 4 (4 + y2);
    assert (ry' >= 8);
    assert (rx' < 8);
    assert (ry' - rx' > 0);
    assert (ry - rx > 0);

    // third step: c >= 16
    assert_norm (pow2 4 = 16);
    FML.pow2_le_compat (x1 + 4) 4;
    ()
  )
#pop-options

let sc_list_f_aux_is_smon_increasing_lte
  (x y: nat)
  : Lemma
  (requires
    x <= y
  )
  (ensures
    sc_list_f_aux x <= sc_list_f_aux y
  )
  =
  if x < y
  then sc_list_f_aux_is_smon_increasing_lt x y
  else ()

let sc_list_f_aux_min
  (x: nat)
  : Lemma
  (sc_list_f_aux x >= 64)
  =
  let r = sc_list_f_aux 0 in
  assert_norm (r == 64);
  sc_list_f_aux_is_smon_increasing_lte 0 x

let sc_list_f_is_smon_increasing_lt
  (x y: nat)
  : Lemma
  (requires
    x < y
  )
  (ensures
    sc_list_f x < sc_list_f y
  )
  =
  let rx = sc_list_f x in
  let ry = sc_list_f y in
  if x > 1
  then sc_list_f_aux_is_smon_increasing_lt (x - 2) (y - 2)
  else (
    FML.lemma_mult_le_right 16 (x+1) 2;
    assert (sc_list_f x <= 32);
    if y > 1 then (
      sc_list_f_aux_min (y-2);
      assert (sc_list_f y >= 64)
    ) else (
      FML.lemma_mult_lt_right 16 (x+1) (y+1)
    )
  )

let sc_list_f_is_smon_increasing_lte
  (x y: nat)
  : Lemma
  (requires
    x <= y
  )
  (ensures
    sc_list_f x <= sc_list_f y
  )
  =
  if x < y
  then sc_list_f_is_smon_increasing_lt x y
  else ()

#push-options "--z3rlimit 50"
let inv_exact_log (k: nat)
  : Lemma
  (requires k <= 24)
  (ensures
    64 <= sc_list_f_aux k /\
    sc_list_f_aux k <= 4096 /\
    (let r = sc_list_f_aux k in
    log2u64_spec r = (k/4) + 6
  ))
  =
  let k1 = k/4 in
  let k2 = k%4 in
  let r = sc_list_f_aux k in
  sc_list_f_aux_min k;
  sc_list_f_aux_is_smon_increasing_lte k 24;
  assert_norm (sc_list_f_aux 24 == 4096);
  assert (r == pow2 (k1 + 6) + k2 * pow2 (k1 + 4));
  assert (k2 < 4);
  FML.pow2_plus (k1 + 4) 2;
  assert_norm (pow2 2 == 4);
  assert (pow2 (k1 + 4) * 4 = pow2 (k1 + 6));
  assert (pow2 (k1 + 6) <= r);
  FML.pow2_double_sum (k1 + 6);
  assert (r < pow2 (k1 + 6 + 1));
  log2u64_spec_eq_lemma r (k1 + 6)
#pop-options

#push-options "--z3rlimit 50"
let inv_exact_aux (k: nat)
  : Lemma
  (requires k <= 24)
  (ensures
    64 <= sc_list_f_aux k /\
    sc_list_f_aux k <= 4096 /\
    inv_aux (sc_list_f_aux k) == k
  )
  =
  let x = sc_list_f_aux k in
  sc_list_f_aux_min k;
  sc_list_f_aux_is_smon_increasing_lte k 24;
  assert_norm (sc_list_f_aux 24 == 4096);
  let log = log2u64_spec x in
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 12 == 4096);
  inv_exact_log k;
  assert (log = k/4 +6);
  if log < 6 then FML.pow2_le_compat 6 (log+1);
  if log > 12 then FML.pow2_lt_compat log 12;
  assert (6 <= log /\ log <= 12);
  let align = pow2 log in
  let align2 = pow2 (log - 2) in
  let y = log - 6 in
  let z = nearest_multiple_upper_div (x - align) align2 in
  assert ((y, z) = inv_aux_2 x);
  assert (k / 4 = y);
  ()
#pop-options

let inv_exact (k: nat)
  : Lemma
  (requires k <= 26)
  (ensures
    sc_list_f k <= 4096 /\
    inv (sc_list_f k) == k
  )
  =
  sc_list_f_is_smon_increasing_lte k 26;
  assert (sc_list_f 26 = 4096) by T.compute();
  if k = 0 then (
    assert (sc_list_f 0 == 16) by T.compute()
  ) else if (k = 1) then (
    assert (sc_list_f 1 == 32) by T.compute()
  ) else if (k = 2) then (
    assert (sc_list_f 2 == 64) by T.compute()
  ) else (
    assert (k >= 3);
    sc_list_f_is_smon_increasing_lt 2 k;
    assert_norm (sc_list_f 2 >= 64);
    assert (sc_list_f k > 64);
    assert (sc_list_f k == sc_list_f_aux (k-2));
    inv_exact_aux (k-2);
    assert (inv_aux (sc_list_f_aux (k-2)) == k-2);
    assert (inv (sc_list_f_aux (k-2)) == inv_aux (sc_list_f_aux (k-2)) + 2)
  )

let inv_exact_log2 (k: nat)
  : Lemma
  (requires 1 <= k /\ k <= 24)
  (ensures
    64 <= sc_list_f_aux (k-1) /\
    sc_list_f_aux (k-1) < 4096 /\
    (let r = sc_list_f_aux (k-1) + 1 in
    log2u64_spec r = (k-1)/4 + 6
  ))
  =
  let k1 = (k-1)/4 in
  let k2 = (k-1)%4 in
  let r = sc_list_f_aux (k-1) + 1 in
  sc_list_f_aux_min (k-1);
  sc_list_f_aux_is_smon_increasing_lt (k-1) 24;
  assert_norm (sc_list_f_aux 24 == 4096);
  assert (r == pow2 (k1 + 6) + k2 * pow2 (k1 + 4) + 1);
  assert (r >= pow2 (k1 + 6));
  assert (k2 < 4);
  FML.pow2_plus (k1 + 4) 2;
  assert_norm (pow2 2 == 4);
  assert (pow2 (k1 + 4) * 4 = pow2 (k1 + 6));
  assert (pow2 (k1 + 6) <= r);
  FML.pow2_double_sum (k1 + 6);
  assert (r < pow2 (k1 + 6 + 1));
  log2u64_spec_eq_lemma r (k1 + 6)

#push-options "--z3rlimit 50"
let inv_exact_aux2 (k: nat)
  : Lemma
  (requires 1 <= k /\ k <= 24)
  (ensures
    64 <= sc_list_f_aux (k-1) /\
    sc_list_f_aux (k-1) < 4096 /\
    inv_aux (sc_list_f_aux (k-1) + 1) == k
  )
  =
  let x = sc_list_f_aux (k-1) + 1 in
  sc_list_f_aux_min (k-1);
  sc_list_f_aux_is_smon_increasing_lt (k-1) 24;
  assert_norm (sc_list_f_aux 24 == 4096);
  let log = log2u64_spec x in
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 12 == 4096);
  inv_exact_log2 k;
  assert (log = (k-1)/4+6);
  if log < 6 then FML.pow2_le_compat 6 (log+1);
  if log > 12 then FML.pow2_lt_compat log 12;
  assert (6 <= log /\ log <= 12);
  let align = pow2 log in
  let align2 = pow2 (log - 2) in
  let y = log - 6 in
  let z = nearest_multiple_upper_div (x - align) align2 in
  assert ((y, z) = inv_aux_2 x);
  assert ((k-1) / 4 = y);
  ()
#pop-options

let inv_exact2 (k: nat)
  : Lemma
  (requires k <= 26)
  (ensures
    2 <= sc_list_f k /\
    sc_list_f k <= 4096 /\
    inv (sc_list_f k - 2) == k
  )
  =
  sc_list_f_is_smon_increasing_lte 0 k;
  sc_list_f_is_smon_increasing_lte k 26;
  assert_norm (sc_list_f 0 = 16);
  assert_norm (sc_list_f 26 = 4096);
  if k = 0 then (
    assert (sc_list_f 0 == 16) by T.compute()
  ) else if (k = 1) then (
    assert (sc_list_f 1 == 32) by T.compute()
  ) else if (k = 2) then (
    assert (sc_list_f 2 == 64) by T.compute()
  ) else (
    assert (k >= 3);
    sc_list_f_is_smon_increasing_lt 2 k;
    assert_norm (sc_list_f 2 >= 64);
    assert (sc_list_f k > 64);
    assert (sc_list_f k == sc_list_f_aux (k-2));
    inv_exact_aux (k-2);
    inv_exact_aux2 (k-2);
    assert (inv_aux (sc_list_f_aux (k-2)) == k-2);
    assert (inv_aux (sc_list_f_aux (k-3) + 1) == k-2);
    sc_list_f_aux_is_smon_increasing_lt (k-3) (k-2);
    assert (sc_list_f_aux (k-3) + 1 <= sc_list_f_aux (k-2) - 2);
    assert (sc_list_f_aux (k-2) - 2 <= sc_list_f_aux (k-2));
    inv_aux_is_mon_increasing (sc_list_f_aux (k-3) + 1) (sc_list_f_aux (k-2) - 2);
    inv_aux_is_mon_increasing (sc_list_f_aux (k-2) - 2) (sc_list_f_aux (k-2));
    assert (inv (sc_list_f_aux (k-2)) == inv_aux (sc_list_f_aux (k-2)) + 2)
  )
