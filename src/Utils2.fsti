module Utils2

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module FU = FStar.UInt

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

open Config

let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr

unfold let same_base_array (#a: Type) (arr1 arr2: array a)
  =
  A.base (A.ptr_of arr1) == A.base (A.ptr_of arr2)

unfold let slab_metadata = r:array U64.t{A.length r = 4}

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
  (U32.eq x 16ul \/ U32.eq x 32ul \/ (min_sc <= U32.v x /\ U32.v x <= max_sc)) /\
  (U32.v page_size) % (U32.v x) == 0
}

let nb_slots (size_class: sc)
  : Pure U32.t
  (requires True)
  (ensures fun r ->
    U32.v r >= 1 /\
    U32.v r <= 256
  )
  =
  U32.div page_size size_class

open FStar.Mul

#push-options "--ifuel 0 --fuel 0"
let nb_slots_correct
  (size_class: sc)
  (pos: U32.t)
  : Lemma
  (requires U32.v pos < U32.v (nb_slots size_class))
  (ensures U32.v (U32.mul pos size_class) <= U32.v page_size - U32.v size_class)
  =
  assert (U32.v pos <= U32.v (nb_slots size_class) - 1);
  assert (U32.v pos * U32.v size_class <= U32.v (U32.mul (nb_slots size_class) size_class) - U32.v size_class);
  assert (U32.v (U32.mul (nb_slots size_class) size_class) <= U32.v page_size)
#pop-options

let zf_b
  (arr: Seq.seq bool)
  : prop
  = arr == (Seq.create (Seq.length arr) false)

let zf_b_slice
  (arr: Seq.seq bool)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length arr})
  : Lemma
  (requires zf_b arr)
  (ensures zf_b (Seq.slice arr i j))
  =
  Seq.lemma_eq_intro (Seq.slice arr i j) (Seq.create (j - i) false)

noextract
let max64_nat : nat = FStar.Int.max_int U64.n
noextract inline_for_extraction
let max64 : U64.t = U64.lognot 0UL

let max64_check (_:unit)
  : Lemma
  (U64.v max64 == max64_nat)
  = admit ()

noextract
let nth_is_zero (x: U64.t) (pos: U32.t{U32.v pos < 64})
  : bool
  = FU.nth (U64.v x) (U64.n - U32.v pos - 1) = false

module G = FStar.Ghost
// CAUTION: assume val, no implementation
val ffs64 (x: U64.t) (bound: G.erased U32.t)
  : Pure U32.t
  (requires
    U32.v (G.reveal bound) <= 64 /\
    (exists (k:nat{k < U32.v (G.reveal bound)}). nth_is_zero x (U32.uint_to_t k)))
  (ensures fun r ->
    U32.v r < U32.v (G.reveal bound) /\
    nth_is_zero x r /\
    (forall (k:nat{k < U64.n /\ nth_is_zero x (U32.uint_to_t k)}).
      U32.v r <= k
    )
  )

let max64_lemma_aux (i:nat{i < 64})
  : Lemma
  (not (nth_is_zero max64 (U32.uint_to_t i)))
  = ()

//let max64_lemma_aux2'
//  (n: nat)
//  (s1 s2: Seq.lseq bool n)
//  (k:nat{k < n})
//  : Lemma
//  (requires
//    Seq.index s1 (n - k - 1)
//    <>
//    Seq.index s2 (n - k - 1)
//  )
//  (ensures
//    exists (k':nat{k' < n}).
//    Seq.index s1 k'
//    <>
//    Seq.index s2 k'
//  )
//  =
//  ()

let max64_lemma_aux2
  (b: nat{b <= 64})
  (x1 x2: U64.t)
  (k:nat{k < b})
  : Lemma
  (requires
    Seq.index (FU.to_vec #64 (U64.v x1)) (U64.n - k - 1)
    <>
    Seq.index (FU.to_vec #64 (U64.v x2)) (U64.n - k - 1)
  )
  (ensures
    exists (k':nat{k' < b}).
    nth_is_zero x1 (U32.uint_to_t k')
    <>
    nth_is_zero x2 (U32.uint_to_t k')
  )
  = ()

let max64_lemma_aux3 (x1 x2: U64.t) (k:nat{k < 64})
  : Lemma
  (requires
    Seq.index (FU.to_vec #64 (U64.v x1)) k
    <>
    Seq.index (FU.to_vec #64 (U64.v x2)) k
  )
  (ensures
    exists (k':nat{k' < 64}).
    nth_is_zero x1 (U32.uint_to_t k')
    <>
    nth_is_zero x2 (U32.uint_to_t k')
  )
  = max64_lemma_aux2 64 x1 x2 (U64.n - k - 1)

// will likely requires to have the converse at some point
let max64_lemma (x: U64.t)
  : Lemma
  (requires x <> max64)
  (ensures (exists (k:nat{k < 64}).
    nth_is_zero x (U32.uint_to_t k)))
  =
  let s1 = FU.to_vec #64 (U64.v x) in
  let s2 = FU.to_vec #64 (U64.v max64) in
  if (Seq.eq s1 s2)
  then FU.to_vec_lemma_2 (U64.v x) (U64.v max64)
  else ();
  assert (s1 <> s2);
  assert (Seq.length s1 == Seq.length s2);
  assert (Seq.length s1 == 64);
  assert (exists (k:nat{k < 64}). Seq.index s1 k <> Seq.index s2 k);
  Classical.forall_to_exists (Classical.move_requires (
    max64_lemma_aux3 x max64
  ));
  assert (exists (k:nat{k < 64}).
     nth_is_zero x (U32.uint_to_t k)
  <> nth_is_zero max64 (U32.uint_to_t k))

module FBV = FStar.BitVector
let pow2_lemma (n: nat{n < 64}) (i: nat{i < n})
  : Lemma
  (
    FStar.Math.Lemmas.pow2_lt_compat 64 n;
    FStar.Math.Lemmas.pow2_le_compat n 0;
    not (nth_is_zero (U64.uint_to_t (pow2 n - 1)) (U32.uint_to_t i) = true))
  =
  match n with
  | 1 -> ()
  | n ->
    FStar.Math.Lemmas.pow2_lt_compat 64 n;
    FStar.Math.Lemmas.pow2_le_compat n 0;
    assert (pow2 n - 1 == pow2 (n-1) +  pow2 (n-1) - 1);
    Classical.forall_intro_2 (Bitmap1.spec_bv_get #64);
    if i < n -1
    then begin
      assert (
        nth_is_zero (U64.uint_to_t (pow2 n - 1)) (U32.uint_to_t i)
        ==
        nth_is_zero (U64.uint_to_t (pow2 (n-1) - 1)) (U32.uint_to_t i))
    end else begin
      ()
    end

inline_for_extraction
let full_n_aux (bound: U32.t)
  : Pure U64.t
  (requires 0 < U32.v bound /\ U32.v bound < 64)
  (ensures fun r ->
    U64.v r == pow2 (U32.v bound) - 1 /\
    ~ (exists (k:nat{k < U32.v bound}). nth_is_zero r (U32.uint_to_t k))
  )
  =
  let x1 = U64.shift_left 1UL bound in
  FU.shift_left_value_lemma #64 (U64.v 1UL) (U32.v bound);
  FStar.Math.Lemmas.pow2_lt_compat 64 (U32.v bound);
  assert (U64.v x1 == pow2 (U32.v bound));
  FStar.Math.Lemmas.pow2_le_compat (U32.v bound) 0;
  assert (U64.v x1 >= 1);
  let x2 = U64.sub x1 1UL in
  Classical.forall_intro (pow2_lemma (U32.v bound));
  x2

let full_n (bound: U32.t)
  : Pure U64.t
  (requires
    0 < U32.v bound /\ U32.v bound <= 64)
  (ensures fun r ->
    ~ (exists (k:nat{k < U32.v bound}). nth_is_zero r (U32.uint_to_t k))
  )
  =
  if U32.eq bound 64ul
  then max64
  else full_n_aux bound

let full_n_decomposition1 (bound: U32.t)
  : Lemma
  (requires 0 < U32.v bound /\ U32.v bound <= 64)
  (ensures (
    let bm = FU.to_vec #64 (U64.v (full_n bound)) in
    Seq.slice bm (64 - U32.v bound) 64 == FBV.ones_vec #(U32.v bound)
  ))
  =
  if U32.eq bound 64ul
  then
    Seq.lemma_eq_intro
      (FU.to_vec #64 (U64.v max64))
      (FBV.ones_vec #64)
  else (
    let x = full_n_aux bound in
    assert (x == full_n bound);
    assert (U64.v x == pow2 (U32.v bound) - 1);
    Classical.forall_intro (pow2_lemma (U32.v bound));
    let bm = FU.to_vec #64 (U64.v x) in
    Seq.lemma_eq_intro
      (Seq.slice bm (64 - U32.v bound) 64)
      (FBV.ones_vec #(U32.v bound))
  )

#push-options "--fuel 0 --ifuel 0"
let full_n_decomposition2 (bound: U32.t)
  : Lemma
  (requires 0 < U32.v bound /\ U32.v bound <= 64)
  (ensures (
    let bm = FU.to_vec #64 (U64.v (full_n bound)) in
    zf_b (Seq.slice bm 0 (64 - U32.v bound))))
  =
  if U32.eq bound 64ul
  then (
    let bm = FU.to_vec #64 (U64.v max64) in
    Seq.lemma_len_slice bm 0 (64 - U32.v bound);
    Seq.lemma_empty (Seq.slice bm 0 (64 - U32.v bound));
    assert (Seq.slice bm 0 (64 - U32.v bound) == Seq.empty);
    Seq.lemma_eq_intro Seq.empty (Seq.create 0 false)
  ) else (
    let x = full_n_aux bound in
    let bm = FU.to_vec #64 (U64.v x) in
    assert (x == full_n bound);
    assert (U64.v x == pow2 (U32.v bound) - 1);
    FU.slice_left_lemma #64 bm (64 - U32.v bound);
    let s = Seq.slice bm 0 (64 - U32.v bound) in
    assert (FU.from_vec #(64 - U32.v bound) s = FU.from_vec bm / pow2 (U32.v bound));
    FU.inverse_num_lemma #64 (U64.v x);
    assert (FU.from_vec bm == (U64.v x));
    assert (FU.from_vec #(64 - U32.v bound) s = 0);
    assert (FU.from_vec #(64 - U32.v bound) s = FU.zero (64 - U32.v bound));
    Seq.lemma_eq_intro
      (Seq.slice bm 0 (64 - U32.v bound))
      (Seq.create (64 - U32.v bound) false)
  )
#pop-options

#push-options "--fuel 0 --ifuel 0"
let full_n_lemma (x: U64.t) (bound: U32.t)
  : Lemma
  (requires
    0 < U32.v bound /\ U32.v bound <= 64 /\
    x <> full_n bound /\
    zf_b (Seq.slice (FU.to_vec #64 (U64.v x)) 0 (64 - U32.v bound))
  )
  (ensures (exists (k:nat{k < U32.v bound}).
    nth_is_zero x (U32.uint_to_t k)
  ))
  =
  let s1 = FU.to_vec #64 (U64.v x) in
  let s2 = FU.to_vec #64 (U64.v (full_n bound)) in
  let s11 = Seq.slice s1 0 (64 - U32.v bound) in
  let s21 = Seq.slice s2 0 (64 - U32.v bound) in
  let s12 = Seq.slice s1 (64 - U32.v bound) 64 in
  let s22 = Seq.slice s2 (64 - U32.v bound) 64 in
  full_n_decomposition2 bound;
  assert (s11 == s21);
  if (Seq.eq s12 s22)
  then (
    Seq.lemma_split s1 (64 - U32.v bound);
    Seq.lemma_split s2 (64 - U32.v bound);
    assert (s1 == s2);
    FU.to_vec_lemma_2 (U64.v x) (U64.v (full_n bound))
  ) else ();
  assert (s12 <> s22);
  assert (Seq.length s12 == Seq.length s22);
  assert (Seq.length s12 == U32.v bound);
  assert (exists (k:nat{k < U32.v bound}). Seq.index s12 k <> Seq.index s22 k);
  Classical.forall_intro (
    SeqUtils.lemma_index_slice s1 (64 - U32.v bound) 64);
  Classical.forall_intro (
    SeqUtils.lemma_index_slice s2 (64 - U32.v bound) 64);
  assert (exists (k:nat{k >= 64 - U32.v bound /\ k < 64}). Seq.index s1 k <> Seq.index s2 k);
  eliminate exists (k:nat{k >= 64 - U32.v bound /\ k < 64}). Seq.index s1 k <> Seq.index s2 k
    returns exists (k:nat{k < U32.v bound}). Seq.index s1 (64 - k - 1) <> Seq.index s2 (64 - k - 1)
    with _.
      introduce exists (k:nat{k < U32.v bound}). Seq.index s1 (64 - k - 1) <> Seq.index s2 (64 - k - 1)
      with (64 -k - 1)
      and ();
  assert (exists (k:nat{k < U32.v bound}). Seq.index s1 (64 - k - 1) <> Seq.index s2 (64 - k - 1));
  Classical.forall_intro (Classical.move_requires (
    max64_lemma_aux2 (U32.v bound) x (full_n bound)
  ))
#pop-options

noextract inline_for_extraction
let bound2_gen (v: U32.t) (size_class: G.erased sc)
  : Pure U32.t
  (requires v == nb_slots (G.reveal size_class))
  (ensures fun r ->
    0 < U32.v r /\
    U32.v r <= 64 /\
    U32.v r <= U32.v (nb_slots size_class))
  =
  let nb_slots_v_rem = U32.rem v 64ul in
  if U32.eq nb_slots_v_rem 0ul
  then 64ul
  else nb_slots_v_rem

noextract
let has_free_slot
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  let max = U64.v max64 in
  let nb_slots_v = nb_slots size_class in
  let bound = (U32.v nb_slots_v) / 64 in
  let bound2 = U32.v (bound2_gen nb_slots_v (G.hide size_class)) in
  //FStar.Math.Lemmas.lemma_mod_lt nb_slots U64.n;
  assert (0 <= bound2 /\ bound2 <= 64);
  let full = U64.v (full_n (U32.uint_to_t bound2)) in
  (U64.v (Seq.index s 0) <> full) ||
  (bound > 1 && (U64.v (Seq.index s 1) <> max)) ||
  (bound > 2 && (U64.v (Seq.index s 2) <> max)) ||
  (bound > 3 && (U64.v (Seq.index s 3) <> max))

let has_free_slot_s
  (size_class: sc)
  (md: slab_metadata)
  : Steel bool
  (A.varray md) (fun _ -> A.varray md)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel md h1 == A.asel md h0 /\
    r == has_free_slot size_class (A.asel md h0)
  )
  =
  let nb_slots_v = nb_slots size_class in
  let bound = U32.div nb_slots_v 64ul in
  let bound2 = bound2_gen nb_slots_v (G.hide size_class) in
  let full = full_n bound2 in
  let v0 = A.index md 0sz in
  let v1 = A.index md 1sz in
  let v2 = A.index md 2sz in
  let v3 = A.index md 3sz in
  (not (U64.eq v0 full)) ||
  (U32.gt bound 1ul && (not (U64.eq v1 max64))) ||
  (U32.gt bound 2ul && (not (U64.eq v2 max64))) ||
  (U32.gt bound 3ul && (not (U64.eq v3 max64)))

noextract
let is_empty
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  let max = FStar.Int.max_int U64.n in
  let bound = U32.v (nb_slots size_class) / 64 in
  (U64.v (Seq.index s 0) = 0) &&
  (bound <= 1 || (U64.v (Seq.index s 1) = 0)) &&
  (bound <= 2 || (U64.v (Seq.index s 2) = 0)) &&
  (bound <= 3 || (U64.v (Seq.index s 3) = 0))

let is_empty_s
  (size_class: sc)
  (md: slab_metadata)
  : Steel bool
  (A.varray md) (fun _ -> A.varray md)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel md h1 == A.asel md h0 /\
    r == is_empty size_class (A.asel md h0)
  )
  =
  let bound = U32.div (nb_slots size_class) 64ul in
  let v0 = A.index md 0sz in
  let v1 = A.index md 1sz in
  let v2 = A.index md 2sz in
  let v3 = A.index md 3sz in
  (U64.eq v0 0UL) &&
  (U32.lte bound 1ul || (U64.eq v1 0UL)) &&
  (U32.lte bound 2ul || (U64.eq v2 0UL)) &&
  (U32.lte bound 3ul || (U64.eq v3 0UL))

noextract
let is_partial
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  has_free_slot size_class s && (not (is_empty size_class s))

let is_partial_s
  (size_class: sc)
  (md: slab_metadata)
  : Steel bool
  (A.varray md) (fun _ -> A.varray md)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel md h1 == A.asel md h0 /\
    r == is_partial size_class (A.asel md h0)
  )
  =
  let b1 = has_free_slot_s size_class md in
  let b2 = is_empty_s size_class md in
  b1 && not b2

noextract
let is_full
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  not (has_free_slot size_class s)

let is_full_s
  (size_class: sc)
  (md: slab_metadata)
  : Steel bool
  (A.varray md) (fun _ -> A.varray md)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel md h1 == A.asel md h0 /\
    r == is_full size_class (A.asel md h0)
  )
  =
  let b = has_free_slot_s size_class md in
  not b

noextract
let zeroes_impl_empty
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : Lemma
  (requires s == Seq.create 4 0UL)
  (ensures is_empty size_class s)
  = ()

let zf_u64
  (arr: Seq.seq U64.t)
  : prop
  = arr == (Seq.create (Seq.length arr) 0UL)

let zf_u64_slice
  (arr: Seq.seq U64.t)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length arr})
  : Lemma
  (requires zf_u64 arr)
  (ensures zf_u64 (Seq.slice arr i j))
  =
  Seq.lemma_eq_intro (Seq.slice arr i j) (Seq.create (j - i) 0UL)

let zf_u8
  (arr: Seq.seq U8.t)
  : prop
  = arr == (Seq.create (Seq.length arr) 0z)

let zf_u8_slice
  (arr: Seq.seq U8.t)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length arr})
  : Lemma
  (requires zf_u8 arr)
  (ensures zf_u8 (Seq.slice arr i j))
  =
  Seq.lemma_eq_intro (Seq.slice arr i j) (Seq.create (j - i) 0z)


open FStar.Mul
//TODO: FStar.Math.Lemmas.multiple_division_lemma
let lemma_div (x y z: nat)
  : Lemma
  (requires
    x = y * z /\
    z > 0
  )
  (ensures
    x / z = y
  )
  =
  FStar.Math.Lemmas.lemma_mod_plus 0 y z;
  assert ((y * z) % z = 0)

let array_to_bv_slice
  (#n: nat)
  (s0: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires
    i < n
  )
  (ensures (
    let bm0 = Bitmap4.array_to_bv2 s0 in
    let x = Seq.index s0 i in
    Seq.slice bm0 (i*64) ((i+1)*64)
    =
    FU.to_vec #64 (U64.v x)))
  =
  Bitmap4.array_to_bv_lemma_upd_set_aux4 s0 (i*64)

let lemma_nth_nonzero
  (x: U64.t)
  (i: nat{i < 64})
  : Lemma
  (requires FU.nth (U64.v x) i = true)
  (ensures x <> 0UL)
  =
  if x = 0UL
  then (
    assert (FU.nth #64 (U64.v x) i = true);
    FU.zero_to_vec_lemma #64 i;
    assert (FU.nth #64 0 i = false);
    assert (FU.to_vec #64 (U64.v x) =!= FU.to_vec #64 0);
    FU.to_vec_lemma_1 #64 (U64.v x) 0
  ) else ()

let lemma_nth_nonmax64
  (x: U64.t)
  (i: nat{i < 64})
  : Lemma
  (requires FU.nth (U64.v x) i = false)
  (ensures x <> max64)
  =
  if x = max64
  then (
    assert (FU.nth #64 (U64.v x) i = false);
    max64_check ();
    assert (U64.v max64 = FStar.Int.max_int U64.n);
    assert (U64.v max64 = FU.ones 64);
    FU.ones_to_vec_lemma #64 i;
    assert (FU.nth #64 0 i = true);
    assert (FU.to_vec #64 (U64.v x) =!= FU.to_vec #64 0);
    FU.to_vec_lemma_1 #64 (U64.v x) 0
  ) else ()

//let lemma_nth_nonfull
//  (size_class: sc)
//  (x: U64.t)
//  (i: nat{i < U32.v (nb_slots size_class) /\ i < 64})
//  : Lemma
//  (requires FU.nth (U64.v x) i = false)
//  (ensures (
//    let bound2 = U32.v (bound2_gen (nb_slots size_class) (G.hide size_class)) in
//    let full = full_n (U32.uint_to_t bound2) in
//    x <> full))
//  =
//  admit ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 75"
open FStar.UInt
let set_lemma_nonempty
  (size_class: sc)
  (md_as_seq1: Seq.lseq U64.t 4)
  (md_as_seq2: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U64.n * 4})
  : Lemma
  (requires (
    let idx = Bitmap4.f #4 (U32.v pos) in
    let bm1 = Bitmap4.array_to_bv2 md_as_seq1 in
    md_as_seq2 == Bitmap4.set md_as_seq1 pos /\
    Seq.index bm1 idx = false /\
    U32.v pos < U32.v (nb_slots size_class)))
  (ensures not (is_empty size_class md_as_seq2))
  =
  Bitmap4.set_lemma2 #4 md_as_seq1 pos;
  let idx = Bitmap4.f #4 (U32.v pos) in
  let bm2 = Bitmap4.array_to_bv2 md_as_seq2 in
  assert (Seq.index bm2 idx = true);
  let i1 = U32.div pos 64ul in
  let i2 = U32.rem pos 64ul in
  assert (U32.v i1 * 64 <= idx /\ idx < (U32.v i1 + 1) * 64);
  array_to_bv_slice #4 md_as_seq2 (U32.v i1);
  Seq.lemma_index_slice bm2 (U32.v i1 * 64) ((U32.v i1+1) * 64) (idx - U32.v i1 * 64);
  let x = Seq.index md_as_seq2 (U32.v i1) in
  assert (FU.nth #64 (U64.v x) (idx - U32.v i1 * 64) = true);
  lemma_nth_nonzero x (idx - U32.v i1 * 64);
  assert (x <> 0UL);
  assert (Seq.index md_as_seq2 (U32.v i1) <> 0UL)

let set_lemma_nonfull
  (size_class: sc)
  (md_as_seq1: Seq.lseq U64.t 4)
  (md_as_seq2: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U64.n * 4})
  : Lemma
  (requires (
    let idx = Bitmap4.f #4 (U32.v pos) in
    let bm1 = Bitmap4.array_to_bv2 md_as_seq1 in
    md_as_seq2 == Bitmap4.unset md_as_seq1 pos /\
    Seq.index bm1 idx = true /\
    U32.v pos < U32.v (nb_slots size_class)))
  (ensures not (is_full size_class md_as_seq2))
  =
  Bitmap4.unset_lemma2 #4 md_as_seq1 pos;
  let idx = Bitmap4.f #4 (U32.v pos) in
  let bm2 = Bitmap4.array_to_bv2 md_as_seq2 in
  assert (Seq.index bm2 idx = false);
  let i1 = U32.div pos 64ul in
  let i2 = U32.rem pos 64ul in
  assert (U32.v i1 * 64 <= idx /\ idx < (U32.v i1 + 1) * 64);
  array_to_bv_slice #4 md_as_seq2 (U32.v i1);
  Seq.lemma_index_slice bm2 (U32.v i1 * 64) ((U32.v i1+1) * 64) (idx - U32.v i1 * 64);
  let x = Seq.index md_as_seq2 (U32.v i1) in
  assert (FU.nth #64 (U64.v x) (idx - U32.v i1 * 64) = false);
  if U32.eq i1 0ul
  then (
    let bound2 = U32.v (bound2_gen (nb_slots size_class) (G.hide size_class)) in
    let full = full_n (U32.uint_to_t bound2) in
    //lemma_nth_nonfull size_class x (idx - U32.v i1 * 64);
    assume (x <> full);
    assert (Seq.index md_as_seq2 (U32.v i1) <> full)

  ) else (
    lemma_nth_nonmax64 x (idx - U32.v i1 * 64);
    assert (x <> max64);
    assert (Seq.index md_as_seq2 (U32.v i1) <> max64)
  )
