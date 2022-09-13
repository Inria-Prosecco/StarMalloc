module Bitmap3

module U64 = FStar.UInt64
module U32 = FStar.UInt32
open FStar.UInt
open FStar.Mul

open Bitmap1
open Bitmap2

inline_for_extraction noextract
let u64_bool_of_uint (x: U64.t)
  : bool
  =
  if U64.eq x U64.one
  then true
  else false

let u64_bool_of_uint_lemma (x: U64.t)
  : Lemma
  (u64_bool_of_uint x = bool_of_uint (U64.v x))
  = ()

inline_for_extraction noextract
let get (b: U64.t) (m:U32.t{U32.v m < U64.n})
  : bool
  =
  let r1 = U64.shift_right b m in
  let r2 = U64.logand r1 1UL in
  let r3 = u64_bool_of_uint r2 in
  r3

let bv_get_lemma (b: U64.t) (m:U32.t{U32.v m < 64})
  : Lemma
  (get b m = nth (U64.v b) (U64.n - U32.v m - 1))
  =
  let r1 = U64.shift_right b m in
  shift_right_value_lemma (U64.v b) (U32.v m);
  let r2 = U64.logand r1 1UL in
  logand_mask #U64.n (U64.v r1) (U64.v 1UL);
  let r3 = u64_bool_of_uint r2 in
  u64_bool_of_uint_lemma r2;
  spec2_bv_get (U64.v b) (U32.v m)

inline_for_extraction noextract
let set (b: U64.t) (m:U32.t{U32.v m < U64.n})
  : U64.t
  =
  let a = U64.shift_left 1UL m in
  let r = U64.logor a b in
  r

let shift_left_is_pow2 (m:U32.t{U32.v m < U64.n})
  : Lemma
  (U64.v (U64.shift_left 1UL m) == pow2 (U32.v m))
  =
  let a = U64.shift_left 1UL m in
  shift_left_value_lemma (U64.v 1UL) (U32.v m);
  FStar.Math.Lemmas.pow2_lt_compat U64.n (U32.v m)

let bv_set_lemma (b: U64.t) (m:U32.t{U32.v m < U64.n})
  : Lemma
  (requires nth (U64.v b) (U64.n - U32.v m - 1) = false)
  (ensures
    nth (U64.v (set b m)) (U64.n - U32.v m - 1) = true /\
    to_vec #64 (U64.v (set b m)) = Seq.upd (to_vec #64 (U64.v b)) (U64.n - U32.v m - 1) true
  )
  =
  let r = set b m in
  shift_left_is_pow2 m;
  assert (U64.v r == spec2_set (U64.v b) (U32.v m));
  spec2_bv_set (U64.v b) (U32.v m);
  Seq.lemma_eq_intro
    (to_vec #64 (U64.v (set b m)))
    (Seq.upd (to_vec #64 (U64.v b)) (U64.n - U32.v m - 1) true)

inline_for_extraction noextract
let unset (b: U64.t) (m:U32.t{U32.v m < U64.n})
  : U64.t
  =
  let a = U64.shift_left 1UL m in
  let c = U64.lognot a in
  let r = U64.logand c b in
  r

let bv_unset_lemma (b: U64.t) (m:U32.t{U32.v m < U64.n})
  : Lemma
  (requires nth (U64.v b) (U64.n - U32.v m - 1) = true)
  (ensures
    nth (U64.v (set b m)) (U64.n - U32.v m - 1) = false /\
    to_vec #64 (U64.v (unset b m)) = Seq.upd (to_vec #64 (U64.v b)) (U64.n - U32.v m - 1) false
  )
  =
  let r = unset b m in
  shift_left_is_pow2 m;
  assert (U64.v r == spec2_unset (U64.v b) (U32.v m));
  spec2_bv_unset (U64.v b) (U32.v m);
  admit ();
  Seq.lemma_eq_intro
    (to_vec #64 (U64.v (unset b m)))
    (Seq.upd (to_vec #64 (U64.v b)) (U64.n - U32.v m - 1) false)
