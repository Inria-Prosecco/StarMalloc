module Utils2

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module FU = FStar.UInt

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr

// 1) ptrdiff
// 2) ffs64/ffz64

unfold let same_base_array (#a: Type) (arr1 arr2: array a)
  =
  A.base (A.ptr_of arr1) == A.base (A.ptr_of arr2)

unfold let slab_metadata = r:array U64.t{A.length r = 4}

//TODO: should not be hardcoded
let page_size = 4096ul
let metadata_max = 131072ul

noextract
let min_sc = 16
noextract
let max_sc = 64

//TODO: second constraint should be relaxed
//currently does not support size classes with <64 slots
//that require a subtle loop to read only possible
//corresponding slots in the bitmap
let sc = x:U32.t{min_sc <= U32.v x /\ U32.v x <= max_sc}


let nb_slots (size_class: sc)
  : Pure U32.t
  (requires True)
  (ensures fun r ->
    U32.v r >= 1 /\
    U32.v r <= 256
  )
  =
  U32.div page_size size_class

let nb_slots_correct
  (size_class: sc)
  (pos: U32.t)
  : Lemma
  (requires U32.v pos < U32.v (nb_slots size_class))
  (ensures U32.v (U32.mul pos size_class) <= U32.v page_size)
  = ()

noextract
let max64_nat : nat = FStar.Int.max_int U64.n
noextract inline_for_extraction
let max64 : U64.t = U64.lognot 0UL

noextract
let has_free_slot
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  let max = U64.v max64 in
  let bound = U32.v (nb_slots size_class) / 64 in
  (U64.v (Seq.index s 0) <> max) ||
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
  let bound = U32.div (nb_slots size_class) 64ul in
  let v0 = A.index md 0sz in
  let v1 = A.index md 1sz in
  let v2 = A.index md 2sz in
  let v3 = A.index md 3sz in
  (not (U64.eq v0 max64)) ||
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

//CAUTION: assume val
val ffs64 (x: U64.t)
  : Pure U32.t
  (requires U64.v x <> U64.v max64)
  (ensures fun r ->
    U32.v r < 64 /\
    FU.nth (U64.v x) (U64.n - U32.v r - 1) = false
  )

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

open FStar.UInt
let set_lemma_nonzero
  (size_class: sc)
  (md_as_seq1: Seq.lseq U64.t 4)
  (md_as_seq2: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U64.n * 4})
  //: Steel unit opened
  //(A.varray md) (fun _ -> A.varray md)
  : Lemma
  (requires
    md_as_seq2 == Bitmap4.set md_as_seq1 pos /\
    U32.v pos < U32.v (nb_slots size_class))
  (ensures not (is_empty size_class md_as_seq2))
  =
  admit ();
  let i1 = U32.div pos 64ul in
  let i2 = U32.rem pos 64ul in
  assert (Seq.index md_as_seq2 (U32.v i1) == Bitmap3.set (Seq.index md_as_seq1 (U32.v i1)) i2);
  assert (Seq.index md_as_seq2 (U32.v i1) <> 0UL);
  ()
