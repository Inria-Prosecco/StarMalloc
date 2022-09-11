module Bitmap2

module Seq = FStar.Seq
module FBV = FStar.BitVector
open FStar.UInt
open FStar.Mul
open Bitmap1


let append_lemma (#n:pos) (#m:nat) (a:FBV.bv_t n) (b:FBV.bv_t m)
  : Lemma (from_vec #(n + m) (Seq.append a b) = (from_vec #n a) * pow2 m + (from_vec #m b))
  =
  assert(Seq.equal a (Seq.slice (Seq.append a b) 0 n));
  assert(Seq.equal b (Seq.slice (Seq.append a b) n (n + m)));
  if m = 0
  then ()
  else from_vec_propriety #(n + m) (Seq.append a b) n

let slice_right_lemma (#n:pos) (a:FBV.bv_t n) (s:nat{s < n})
  : Lemma
  (requires True)
  (ensures from_vec #s (Seq.slice a (n - s) n) = (from_vec #n a) % (pow2 s))
  =
  if s = 0 then ()
  else begin
    from_vec_propriety #n a (n - s);
    FStar.Math.Lemmas.modulo_addition_lemma (from_vec #s (Seq.slice a (n - s) n)) (pow2 s) (from_vec #(n - s) (Seq.slice a 0 (n - s)));
    FStar.Math.Lemmas.small_modulo_lemma_1 (from_vec #s (Seq.slice a (n - s) n)) (pow2 s)
  end

// slice_left_lemma
// logor_disjoint
// shift_left_value_aux_3
// shift_right_value_aux_3

#push-options "--z3rlimit 30"
let logand_mask (#n:pos) (a:uint_t n) (m:nat{m < n})
  : Lemma (pow2 m < pow2 n /\ logand #n a (pow2 m - 1) == a % pow2 m)
  =
  FStar.Math.Lemmas.pow2_lt_compat n m;
  assert (pow2 m < pow2 n);
  Seq.lemma_split (FBV.logand_vec (to_vec a) (to_vec (pow2 m - 1))) (n - m);
  Seq.lemma_eq_intro
    (FBV.logand_vec (to_vec a) (to_vec (pow2 m - 1)))
    (Seq.append (FBV.zero_vec #(n - m)) (Seq.slice (to_vec a) (n - m) n));
  append_lemma #(n - m) #m (FBV.zero_vec #(n - m)) (Seq.slice (to_vec a) (n - m) n);
  assert (0 * pow2 m + a % pow2 m == a % pow2 m);
  assert (from_vec #(n - m) (FBV.zero_vec #(n - m)) == 0);
  slice_right_lemma #n (to_vec a) m;
  assert (from_vec #m (Seq.slice (to_vec a) (n - m) n) == a % pow2 m)
#pop-options

let spec2_bv_get (#n:nat{n > 1}) (b: uint_t n) (m:nat{m < n})
  : Lemma
  (let r1 = shift_right b m in
  let r2 = bool_of_uint #n (logand r1 1) in
  nth b (n - m - 1) = r2)
  =
  let r1 = shift_right b m in
  let r2 = logand r1 1 in
  shift_right_value_lemma b m;
  assert (r1 == b / (pow2 m));
  logand_mask #n r1 1;
  assert (r2 == r1 % 2);
  spec_bv_get b m

let spec2_set (#n: pos) (b: uint_t n) (m:nat{m < n})
  : uint_t n
  =
  let a = pow2_n m in
  let r = logor a b in
  r

let spec2_bv_set (#n:pos) (b: uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    nth b (n - m - 1) = false)
  (ensures (
    let r = spec2_set b m in
    nth r (n - m - 1) = true
  ))
  =
  spec_bv_set b m

let spec2_unset (#n: pos) (b: uint_t n) (m:nat{m < n})
  : uint_t n
  =
  let a = pow2_n m in
  let c = lognot a in
  let r = logand c b in
  r

let spec2_bv_unset (#n:pos) (b: uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    nth b (n - m - 1) = true)
  (ensures (
    let r = spec2_unset b m in
    nth r (n - m - 1) = false))
  =
  spec_bv_unset b m
