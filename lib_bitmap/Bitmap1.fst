module Bitmap1

module Seq = FStar.Seq
module Seq2 = Seq2
open FStar.BitVector
open FStar.Mul

unfold let f_and (b1 b2: bool) : bool = b1 && b2
unfold let f_or (b1 b2: bool) : bool = b1 || b2
unfold let f_not (b1: bool) : bool = not b1

let logand_vec_map (#n: pos) (a b: bv_t n) : bv_t n
  =
  Seq2.map_seq2_len f_and a b;
  Seq2.map_seq2 f_and a b

let logor_vec_map (#n: pos) (a b: bv_t n) : bv_t n
  =
  Seq2.map_seq2_len f_or a b;
  Seq2.map_seq2 f_or a b

let lognot_vec_map (#n: pos) (b: bv_t n) : bv_t n
  =
  Seq.map_seq_len f_not b;
  Seq.map_seq f_not b

let logand_vec_equiv (#n: pos) (a b: bv_t n)
  : Lemma
  (logand_vec_map a b == logand_vec a b)
  =
  let logand_vec_def (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (Seq.index (logand_vec #n a b) i
           = (Seq.index a i && Seq.index b i))
    = logand_vec_definition a b i in
  let r1 = logand_vec a b in
  let r2 = logand_vec_map a b in
  Classical.forall_intro (logand_vec_def a b);
  Seq2.map_seq2_len f_and a b;
  Classical.forall_intro (Seq2.map_seq2_index f_and a b);
  Seq.lemma_eq_intro r1 r2

let logor_vec_equiv (#n: pos) (a b: bv_t n)
  : Lemma
  (logor_vec_map a b == logor_vec a b)
  =
  let logor_vec_def (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (Seq.index (logor_vec #n a b) i
           = (Seq.index a i || Seq.index b i))
    = logor_vec_definition a b i in
  let r1 = logor_vec a b in
  let r2 = logor_vec_map a b in
  Classical.forall_intro (logor_vec_def a b);
  Seq2.map_seq2_len f_or a b;
  Classical.forall_intro (Seq2.map_seq2_index f_or a b);
  Seq.lemma_eq_intro r1 r2

let lognot_vec_equiv (#n: pos) (b: bv_t n)
  : Lemma
  (lognot_vec_map b == lognot_vec b)
  =
  let lognot_vec_def (#n: pos) (b: bv_t n) (i: nat{i < n})
    : Lemma (Seq.index (lognot_vec #n b) i
           = not (Seq.index b i))
    = lognot_vec_definition b i in
  let r1 = lognot_vec b in
  let r2 = lognot_vec_map b in
  Classical.forall_intro (lognot_vec_def b);
  Seq.map_seq_len f_not b;
  Classical.forall_intro (Seq.map_seq_index f_not b);
  Seq.lemma_eq_intro r1 r2

open FStar.UInt
let from_vec1 (vec: bv_t 1)
  : Lemma
  (from_vec vec = uint_of_bool (Seq.index vec 0))
  = ()

let keep_only_last_bit (#n:pos) (b:uint_t n)
  : Lemma
  (b % 2 = uint_of_bool #n (nth b (n - 1)))
  =
  let vb = to_vec b in
  from_vec_propriety vb (n-1);
  let vb2 = Seq.slice vb (n-1) n in
  assert (from_vec vb
  = (from_vec #(n-1) (Seq.slice vb 0 (n-1))) * (pow2 1)
  + from_vec #1 vb2);
  assert ((from_vec vb) % 2 = from_vec #1 vb2);
  from_vec1 vb2

let spec_bv_get (#n:pos) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (let r1 = b / (pow2 m) % 2 in
  let r2 = bool_of_uint #n r1 in
  nth b (n - m - 1) = r2)
  =
  shift_right_value_lemma b m;
  assert (shift_right b m = b / (pow2 m));
  let vb = to_vec b in
  FStar.BitVector.shift_right_vec_lemma_2 #n vb m (n-1);
  assert (nth #n (b / pow2 m) (n-1) == nth b (n - m - 1));
  keep_only_last_bit #n (b / pow2 m)

#push-options "--z3rlimit 20"
let split3_pow2_yay (#n: pos) (vr: bv_t n) (m: nat{m < n})
  : Lemma
  (let vr1, vr2 = Seq.split vr (n - m - 1) in
  let vr21, vr22 = Seq.split vr2 1 in
  from_vec vr
  = from_vec #(n-m-1) vr1 * (pow2 (m+1))
  + uint_of_bool #n (Seq.index vr21 0) * (pow2 m)
  + from_vec #m vr22)
  =
  let vr1, vr2 = Seq.split vr (n - m - 1) in
  let vr21, vr22 = Seq.split vr2 1 in
  from_vec_propriety vr (n - m - 1);
  assert (from_vec vr = from_vec #(n - m - 1) vr1 * pow2 (m + 1) + from_vec #(m + 1) vr2);
  if (m > 0)
  then begin
    from_vec_propriety #(m+1) vr2 1;
    assert (from_vec #(m+1) vr2
    = from_vec #1 vr21 * (pow2 m) + from_vec #m vr22);
    assert (Seq.length vr21 == 1);
    from_vec1 vr21;
    assert (from_vec #1 vr21 == uint_of_bool (Seq.index vr21 0));
    assert (from_vec #(m+1) vr2
    = uint_of_bool #n (Seq.index vr21 0) * (pow2 m)
    + from_vec #m vr22);
    ()
  end else ()
#pop-options

let split3_pow2_yay2 (#n: pos) (vr: bv_t n) (m: nat{m < n})
  : Lemma
  (from_vec vr
  = from_vec #(n-m-1) (Seq.slice vr 0 (n - m - 1)) * (pow2 (m+1))
  + uint_of_bool #n (Seq.index vr (n - m - 1)) * (pow2 m)
  + from_vec #m (Seq.slice vr (n-m) n))
  =
  let vr1, vr2 = Seq.split vr (n - m - 1) in
  let vr21, vr22 = Seq.split vr2 1 in
  assert (vr1 == Seq.slice vr 0 (n - m - 1));
  Seq.slice_slice vr (n - m - 1) n 0 1;
  assert (Seq.index vr21 0 == Seq.index vr (n - m - 1));
  Seq.slice_slice vr (n - m - 1) n 1 (m+1);
  assert (vr22 == Seq.slice vr (n - m) n);
  split3_pow2_yay vr m;
  ()

let logor_one_add (#n: pos) (a:uint_t n) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    a == pow2 m /\
    nth b (n - m - 1) = false)
  (ensures (
    let r = logor a b in
    r = b + 1 * a /\
    nth r (n - m - 1)))
  =
  let pow2_to_vec_lemma_loc (#n: pos) (p: nat{p < n}) (i: nat{i < n})
    : Lemma (Seq.index (to_vec (pow2_n #n p)) i
           = Seq.index (elem_vec #n (n - p - 1)) i)
    = pow2_to_vec_lemma #n p i in
  let va = to_vec a in
  let vb = to_vec b in
  assert (a == pow2_n #n m);
  assert (Seq.index vb (n - m - 1) = false);
  Classical.forall_intro (pow2_to_vec_lemma_loc #n m);
  Seq.lemma_eq_intro va (elem_vec #n (n - m -1));
  let vr = logor_vec_map va vb in
  Seq2.map_seq2_len f_or va vb;
  Classical.forall_intro (Seq2.map_seq2_index f_or va vb);
  assert (forall i. (i = n - m - 1 ==> Seq.index vr i = true));
  assert (forall i. (i <> n - m - 1 ==> Seq.index vr i = Seq.index vb i));
  let vr1 = Seq.slice vr 0 (n - m - 1) in
  let vb1 = Seq.slice vb 0 (n - m - 1) in
  let vr2 = Seq.slice vr (n - m) n in
  let vb2 = Seq.slice vb (n - m) n in
  Seq.lemma_eq_intro vr1 vb1;
  Seq.lemma_eq_intro vr2 vb2;
  split3_pow2_yay2 #n vr m;
  assert (from_vec vr
  = from_vec #(n-m-1) vr1 * (pow2 (m+1))
  + 1 * (pow2 m)
  + from_vec #m vr2);
  split3_pow2_yay2 #n vb m;
  assert (from_vec vb
  = from_vec #(n-m-1) vb1 * (pow2 (m+1))
  + 0 * (pow2 m)
  + from_vec #m vb2);
  assert (from_vec vr = from_vec vb + 1 * (pow2 m));
  let r = from_vec vr in
  let r2 = logor a b in
  inverse_num_lemma r2;
  logor_vec_equiv va vb;
  assert(r = r2);
  assert (from_vec vb = b);
  assert (r = b + 1 * a)

let spec_bv_set (#n:pos) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    nth b (n - m - 1) = false)
  (ensures (
    let a = pow2_n m in
    let r = logor a b in
    r = a + b /\
    nth r (n - m - 1) = true))
  =
  logor_one_add #n (pow2_n m) b m

#push-options "--z3rlimit 30"
let logand_one_sub (#n: pos) (a:uint_t n) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    a == pow2 m /\
    nth b (n - m - 1) = true)
  (ensures (
    let r = logand (lognot a) b in
    r = b - 1 * a /\
    nth r (n - m - 1) = false))
  =
  let pow2_to_vec_lemma_loc (#n: pos) (p: nat{p < n}) (i: nat{i < n})
    : Lemma (Seq.index (to_vec (pow2_n #n p)) i
           = Seq.index (elem_vec #n (n - p - 1)) i)
    = pow2_to_vec_lemma #n p i in
  let va = to_vec a in
  let vb = to_vec b in
  assert (a == pow2_n #n m);
  assert (Seq.index vb (n - m - 1) = true);
  Classical.forall_intro (pow2_to_vec_lemma_loc #n m);
  Seq.lemma_eq_intro va (elem_vec #n (n - m -1));
  let vc = lognot_vec_map va in
  Seq.map_seq_len f_not va;
  Classical.forall_intro (Seq.map_seq_index f_not va);
  assert (forall i. (i = n - m - 1) ==> Seq.index vc i = false);
  assert (forall i. (i <> n - m - 1 ==> Seq.index vc i = true));
  let vr = logand_vec_map vc vb in
  Seq2.map_seq2_len f_and vc vb;
  Classical.forall_intro (Seq2.map_seq2_index f_and vc vb);
  assert (forall i. (i = n - m - 1) ==> Seq.index vr i = false);
  assert (forall i. (i <> n - m - 1 ==> Seq.index vr i = Seq.index vb i));
  let vr1 = Seq.slice vr 0 (n - m - 1) in
  let vb1 = Seq.slice vb 0 (n - m - 1) in
  let vr2 = Seq.slice vr (n - m) n in
  let vb2 = Seq.slice vb (n - m) n in
  Seq.lemma_eq_intro vr1 vb1;
  Seq.lemma_eq_intro vr2 vb2;
  split3_pow2_yay2 #n vr m;
  assert (from_vec vr
  = from_vec #(n-m-1) vr1 * (pow2 (m+1))
  + 0 * (pow2 m)
  + from_vec #m vr2);
  split3_pow2_yay2 #n vb m;
  assert (from_vec vb
  = from_vec #(n-m-1) vb1 * (pow2 (m+1))
  + 1 * (pow2 m)
  + from_vec #m vb2);
  assert (from_vec vb = from_vec vr + 1 * (pow2 m));
  let r = from_vec vr in
  let r2 = logand (lognot a) b in
  inverse_num_lemma r2;
  lognot_vec_equiv va;
  logand_vec_equiv vc vb;
  assert (r == r2);
  assert (from_vec vb = b);
  assert (r = b - 1 * a)
#pop-options

let spec_bv_unset (#n:pos) (b:uint_t n) (m:nat{m < n})
  : Lemma
  (requires
    nth b (n - m - 1) = true)
  (ensures (
    let a = pow2_n m in
    let r = logand (lognot a) b in
    r = b - a /\
    nth r (n - m - 1) = false))
  =
  logand_one_sub #n (pow2_n m) b m

