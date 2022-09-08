module Slabs

module L = FStar.List.Tot
open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module M = FStar.Math.Lib
module G = FStar.Ghost
open Seq2

let array = Steel.ST.Array.array

//noextract
//let size_classes : list nzn = [
//  //(* 0 *) 0;
//  (* 16 *) 16; 32; 48; 64; 80; 96; 112; 128;
//  (* 32 *) 160; 192; 224; 256;
//  (* 64 *) 320; 384; 448; 512;
//]
//
//
//noextract
//let size_class_slots : list nzn =
//  L.map nb_of_slots size_classes
//
//let f (_:unit) =
//  let v = L.nth size_class_slots 0 in
//  assert(Some?.v v == 256);
//  ()

let page_size = 4096ul

let nzn = x:U32.t{U32.v x > 0 /\ U32.v x <= U32.v page_size}
let slab = slab:array U8.t{A.length slab == U32.v page_size}

let nb_slots (x: nzn) : nzn = U32.div page_size x

let slab_metadata (size_class: nzn)
  = Seq.lseq bool (U32.v (nb_slots size_class))

// used outside of spec, hence the u32
let ptr_slot
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  (n: U32.t{U32.lt n (nb_slots size_class)})
  : A.ptr U8.t
  =
  let ptr_slab = dfst slab in
  let shift = U32.mul n size_class in
  let ptr_slot = A.ptr_shift ptr_slab shift in
  ptr_slot

let arr_slot
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  (n: U32.t{U32.lt n (nb_slots size_class)})
  : arr:array U8.t{A.length arr = U32.v size_class}
  =
  let ptr = ptr_slot size_class slab n in
  let length = G.hide (U32.v size_class) in
  (| ptr, length |)

//@Spec
noextract
let init_nat (len: nat)
  : Seq.lseq (k:nat{k < len}) len
  = Seq.init len (fun k -> k)
//@Spec
noextract
let init_u32 (len: U32.t)
  : Seq.lseq (k:U32.t{U32.v k < U32.v len}) (U32.v len)
  =
  let s : Seq.lseq (k:nat{k < U32.v len}) (U32.v len)
    = init_nat (U32.v len) in
  let f : k:nat{k < U32.v len} -> k':U32.t{U32.v k' < U32.v len}
    = fun k -> U32.uint_to_t k in
  Seq.map_seq_len f s;
  Seq.map_seq f s
//@Spec
noextract
let slab_to_slots
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  : Seq.lseq
    (arr:array U8.t{A.length arr = U32.v size_class})
    (U32.v (nb_slots size_class))
  =
  let n = nb_slots size_class in
  let s = init_u32 n in
  let f = fun (k:U32.t{U32.v k < U32.v n})
          -> arr_slot size_class slab k in
  Seq.map_seq_len f s;
  Seq.map_seq f s
//@Spec
noextract
let sl_state
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  (slab_md: slab_metadata size_class)
  : Seq.lseq vprop (U32.v (nb_slots size_class))
  =
  let f : bool -> array U8.t -> vprop
    = fun b arr -> if b then A.varray arr else emp in
  let s1 = slab_md in
  let s2 = slab_to_slots size_class slab
  in
  map_seq2_len f s1 s2;
  map_seq2 f s1 s2
//@Spec
let set_alloc
  (size_class: nzn)
  (slab_md: slab_metadata size_class)
  (i:nat{i < Seq.length slab_md})
  : Pure (slab_metadata size_class)
  (requires Seq.index slab_md i = false)
  (ensures fun slab_md' ->
    Seq.index slab_md' i = true /\
    (forall j. j <> i ==> Seq.index slab_md' j == Seq.index slab_md j)
  )
  = Seq.upd slab_md i true
//@Spec
let set_free
  (size_class: nzn)
  (slab_md: slab_metadata size_class)
  (i:nat{i < Seq.length slab_md})
  : Pure (slab_metadata size_class)
  (requires Seq.index slab_md i = true)
  (ensures fun slab_md' ->
    Seq.index slab_md' i = false /\
    (forall j. j <> i ==> Seq.index slab_md' j == Seq.index slab_md j)
  )
  = Seq.upd slab_md i false

let div_nbn_is_n (x y: int)
  : Lemma
  (requires x >= 0 /\ y > 0)
  (ensures x / y >= 0)
  = ()

noextract
let spec_smd_index_op0
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: Seq.lseq U64.t 4)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : U64.t
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  let bucket_pos = U32.v i / 64 in
  assert (bucket_pos < 4);
  let bucket = Seq.index slab_md bucket_pos in
  bucket

//@Spec
//open FStar.UInt
let uint64_to_uint32 (x: U64.t) (bound: nat)
  : Pure U32.t
  (requires U64.v x < bound /\ bound < FStar.UInt.max_int 32)
  (ensures fun r -> U32.v r == U64.v x /\ U32.v r < bound)
  = FStar.Int.Cast.uint64_to_uint32 x
open BVL

let smd_index_op0
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Steel U64.t
  (A.varray slab_md)
  (fun _ -> A.varray slab_md)
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    A.asel slab_md h1 == A.asel slab_md h0 /\
    x == spec_smd_index_op0 size_class (A.asel slab_md h1) i
  )
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  assert (U32.v i < 256);
  let i64 = uint32_to_uint64 i in
  let bucket_pos = div64_shift i64 in
  assert (U64.v bucket_pos < 4);
  let bucket_pos = uint64_to_uint32 bucket_pos 4 in
  let bucket = A.index slab_md bucket_pos in
  bucket

//@Spec
open FStar.Mul
noextract
let spec_smd_index_op1
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : nat
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  assert (U32.v i < 256);
  let bucket_pos = U32.v i / 64 in
  assert (bucket_pos < 4);
  let mask_shift : nat = U32.v i - (bucket_pos * 64) in
  assert (mask_shift = U32.v i % 64);
  mask_shift

let smd_index_op1
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : r:U32.t{U32.v r < 64}
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  assert (U32.v i < 256);
  let i64 = uint32_to_uint64 i in
  assert (U64.v i64 == U32.v i);
  let bucket_pos = div64_shift i64 in
  assert (U64.v bucket_pos = U32.v i / 64);
  assert (U64.v bucket_pos < 4);
  let mask_shift_aux = mul64_shift bucket_pos in
  assert (U64.v mask_shift_aux = 64 * U64.v bucket_pos);
  let mask_shift = U64.sub i64 mask_shift_aux in
  assert (U64.v mask_shift = (U32.v i) % 64);
  assert (U64.v mask_shift < 64);
  let mask_shift32 : k:U32.t{U32.v k < 64}
    = uint64_to_uint32 mask_shift 64 in
  mask_shift32

let equiv_smd_index_op1
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Lemma
  (
  let r11 = spec_smd_index_op1 size_class bucket i in
  let r21 = smd_index_op1 size_class bucket i in
  r11 = U32.v r21)
  = ()

noextract
let spec_smd_index_op2
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: nat)
  : bool
  =
  div_nbn_is_n (U64.v bucket) (pow2  mask_shift);
  let r : nat = (U64.v bucket) / (pow2 mask_shift) in
  if r % 2 = 1
  then true
  else false

let smd_index_op2
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: U32.t{U32.v mask_shift < 64})
  : bool
  =
  let r = div64_shift2 bucket mask_shift in
  assert (U64.v r == (U64.v bucket) / (pow2 (U32.v mask_shift)));
  let r = U64.logand r 1UL in
  if U64.eq r 1UL
  then true
  else false

let equiv_smd_index_op2
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: U32.t{U32.v mask_shift < 64})
  : Lemma
  (
  let r11 = spec_smd_index_op2 size_class bucket (U32.v mask_shift) in
  let r21 = smd_index_op2 size_class bucket mask_shift in
  r11 = r21)
  =
  Classical.forall_intro logand1

//@Spec
noextract
let spec_smd_index
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: Seq.lseq U64.t 4)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : bool
  =
  let bucket = spec_smd_index_op0 size_class slab_md i in
  let mask_shift = spec_smd_index_op1 size_class bucket i in
  let r = spec_smd_index_op2 size_class bucket mask_shift in
  r

let smd_index
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Steel bool
  (A.varray slab_md)
  (fun _ -> A.varray slab_md)
  (requires fun h0 -> True)
  (ensures fun h0 b h1 ->
      b == spec_smd_index size_class (A.asel slab_md h1) i /\
      A.asel slab_md h1 == A.asel slab_md h0
  )
  =
  let bucket = smd_index_op0 size_class slab_md i in
  let mask_shift = smd_index_op1 size_class bucket i in
  equiv_smd_index_op1 size_class bucket i;
  let r = smd_index_op2 size_class bucket mask_shift in
  equiv_smd_index_op2 size_class bucket mask_shift;
  return r

//@Spec
noextract
let smd2b
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: Seq.lseq U64.t 4)
  : (Seq.lseq bool (U32.v (nb_slots size_class)))
  =
  let f = spec_smd_index size_class slab_md in
  let s1 = init_u32 (nb_slots size_class) in
  Seq.map_seq_len f s1;
  Seq.map_seq f s1

[@@__steel_reduce__]
noextract
let v_smd
  (#vp:vprop)
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (h:rmem vp{
    FStar.Tactics.with_tactic selector_tactic
      (can_be_split vp (A.varray slab_md) /\ True)
  })
  : GTot (Seq.lseq bool (U32.v (nb_slots size_class)))
  =
  let s : G.erased (Seq.lseq U64.t 4) = h (A.varray slab_md) in
  G.hide (smd2b size_class (G.reveal s))

(*)


let slab_md_array_set_alloc
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Steel unit
  (A.varray slab_md)
  (fun _ -> A.varray slab_md)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 ->

  )



(*)

let slab_md_array_to_seq
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  //: slab_metadata size_class
  : unit
  = ()


(*)
let get_slot (page: array U8.t) (size_class: nat) (pos: nat)
  : Steel (array U8.t)
    (A.varray page)
    (fun r -> A.varray r)
    (fun h0 ->
      A.length page == page_size
    )
    (fun h0 r h1 -> A.length r == size_class)
    =
    return page
