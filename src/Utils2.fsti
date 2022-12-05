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
let slab_max_number = 4096ul

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

noextract inline_for_extraction
let max64 : U64.t = U64.uint_to_t (FStar.Int.max_int U64.n)

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

val ffs64 (x: U64.t)
  : Pure U32.t
  (requires U64.v x <> U64.v max64)
  (ensures fun r ->
    U32.v r < 64 /\
    FU.nth (U64.v x) (U64.n - U32.v r - 1) = false
  )

open FStar.Mul
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
