module Slots2

module FU = FStar.UInt
module FI = FStar.Int
module STU = SizeTUtils
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

module G = FStar.Ghost

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

open Utils2
open SteelOptUtils
open SteelStarSeqUtils
open FStar.Mul

open Slots

let starseq_upd_aux_lemma3
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires (
    let bm1 = a2bv (G.reveal md_as_seq1) in
    let bm2 = a2bv (G.reveal md_as_seq2) in
    Seq.index bm1 (Bitmap5.f #4 (U32.v pos)) = true /\
    bm2 == Seq.upd bm1 (Bitmap5.f #4 (U32.v pos)) false
  ))
  (ensures
    ((slab_vprop_aux_f size_class md_as_seq2 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
    ==
    some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos)
  )
  =
  let bm2 = a2bv (G.reveal md_as_seq2) in
  SeqUtils.init_u32_refined_index (U32.v (nb_slots size_class)) (U32.v pos);
  assert (Seq.index (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))) (U32.v pos) = pos);
  let k_index = Bitmap5.f #4 (U32.v pos) in
  assert (Seq.index bm2 k_index = false);
  equiv_get_a2bv_index size_class md_as_seq2 (U32.v pos);
  assert (Bitmap4.get md_as_seq2 pos = Seq.index bm2 k_index);
  assert (Bitmap4.get md_as_seq2 pos = false)

let apply_starseq_upd2 (#opened:_)
  (size_class: sc)
  //TODO: remove
  (md: slab_metadata)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : SteelGhost unit opened
  (
    (slab_vprop_aux_f size_class md_as_seq2 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq1 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (fun _ ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq2 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq2 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    let bm1 = a2bv (G.reveal md_as_seq1) in
    let bm2 = a2bv (G.reveal md_as_seq2) in
    Seq.index bm1 (Bitmap5.f #4 (U32.v pos)) = true /\
    bm2 == Seq.upd bm1 (Bitmap5.f #4 (U32.v pos)) false)
  (ensures fun h0 _ h1 ->
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq1 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0;
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq2 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq2 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1;
    slab_vprop_aux_f_lemma size_class md_as_seq1 arr
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos));
    let v1 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq1 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0 in
    let v2 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq2 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq2 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1 in
    let x
      : normal (t_of
        ((slab_vprop_aux_f size_class md_as_seq2 arr)
          (Seq.index
            (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
            (U32.v pos))))
      = h0
      ((slab_vprop_aux_f size_class md_as_seq2 arr)
        (Seq.index
          (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
          (U32.v pos))) in
    v2 == Seq.upd v1 (U32.v pos) x)
  =
  starseq_upd_aux_lemma1
    size_class md md_as_seq1 md_as_seq2 arr pos true;

  let bm1 = a2bv (G.reveal md_as_seq1) in
  let bm2 = a2bv (G.reveal md_as_seq2) in
  SeqUtils.lemma_upd_bij bm1 bm2 (Bitmap5.f #4 (U32.v pos)) false;
  assert (bm1 == Seq.upd bm2 (Bitmap5.f #4 (U32.v pos)) true);

  starseq_upd_aux_lemma2
    size_class md md_as_seq2 md_as_seq1 arr pos;
  starseq_upd_aux_lemma3
    size_class md md_as_seq1 md_as_seq2 arr pos;
  starseq_upd4
    #_
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(Seq.lseq U8.t (U32.v size_class))
    (slab_vprop_aux_f size_class md_as_seq1 arr)
    (slab_vprop_aux_f size_class md_as_seq2 arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq2 arr)
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (U32.v pos)

noextract inline_for_extraction
let deallocate_slot_aux
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Steel unit
  (
    (slab_vprop_aux_f size_class md_as_seq arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)) `star`
    A.varray md `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (fun _ ->
    A.varray md `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    let bm0 = a2bv (A.asel md h0) in
    let idx = Bitmap5.f #4 (U32.v pos) in
    A.asel md h0 == G.reveal md_as_seq /\
    Seq.index bm0 idx = false
  )
  (ensures fun h0 _ h1 ->
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0;
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1;
    let blob1 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0 in
    let blob2 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1 in
    let v1 = A.asel md h0 in
    let v2 = A.asel md h1 in
    //let idx = Bitmap5.f #4 (U32.v pos) in
    //TODO
    //v2 == Bitmap4.unset v1 pos /\
    //TODO
    //blob2 == Seq.upd blob1 (U32.v pos) None)
    True)
  =
  assert_norm (4 < FI.max_int U16.n);

  let bm1 = G.hide (a2bv (Bitmap4.set md_as_seq pos)) in
  let bm2 = G.hide (a2bv md_as_seq) in
  assume (G.reveal bm1 == Seq.upd (G.reveal bm2) (Bitmap5.f #4 (U32.v pos)) true);
  SeqUtils.lemma_upd_bij bm2 bm1 (Bitmap5.f #4 (U32.v pos)) true;
  assert (G.reveal bm2 == Seq.upd (G.reveal bm1) (Bitmap5.f #4 (U32.v pos)) false);
  //TODO
  //Bitmap5.bm_unset #4 md pos;
  apply_starseq_upd2
    size_class
    md
    (G.hide (Bitmap4.set md_as_seq pos))
    md_as_seq
    arr
    pos;
  return ()


open SteelPtrdiff

module US = FStar.SizeT

// if this function yields true,
// with an additional condition on the offset,
// then it means it is a valid pointer that *could* be allocated
// proper alignment means also one can recover the pos of the slot within the slab

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
//TODO: check for spec
let deallocate_slot_aux0
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  : Pure bool
  (requires
    same_base_array arr ptr /\
    US.v (ptrdiff (A.ptr_of ptr) (A.ptr_of arr)) < U32.v page_size
  )
  (ensures
    fun r ->
    r == (US.v (ptrdiff (A.ptr_of ptr) (A.ptr_of arr)) % (U32.v size_class) = 0)
  )
  =
  let diff = ptrdiff (A.ptr_of ptr) (A.ptr_of arr) in
  assume (US.fits_u32);
  let size_class_sz = US.uint32_to_sizet size_class in
  assert (US.v size_class_sz == U32.v size_class);
  let rem = US.rem diff size_class_sz in
  assert (US.v rem = US.v diff % U32.v size_class);
  let r = rem = 0sz in
  assert (r == (US.v diff % U32.v size_class = 0));
  r

let slot_array_offset_lemma (size_class: sc) (arr: array U8.t) (pos: U32.t)
  : Lemma
  (requires
    U32.v pos < U32.v (nb_slots size_class) /\
    A.length arr = U32.v page_size)
  (ensures
    U32.v (U32.mul pos size_class)
    ==
    A.offset (A.ptr_of (slot_array size_class arr pos)) - A.offset (A.ptr_of arr)
  )
  =
  let ptr = A.ptr_of arr in
  let shift = U32.mul pos size_class in
  nb_slots_correct size_class pos;
  assert (U32.v shift <= U32.v page_size);
  assert_norm (U32.v shift <= FI.max_int U16.n);
  assert (U32.v shift <= FI.max_int U16.n);
  let shift_size_t = STU.small_uint32_to_sizet shift in
  assert (US.v shift_size_t < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  assert (ptr_shifted == A.ptr_of (slot_array size_class arr pos));
  ()

let deallocate_slot_aux1
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  : Lemma
  (requires
    same_base_array arr ptr /\
    US.v (ptrdiff (A.ptr_of ptr) (A.ptr_of arr)) < U32.v page_size /\
    US.v (ptrdiff (A.ptr_of ptr) (A.ptr_of arr)) % (U32.v size_class) == 0
  )
  (ensures (
    let diff = ptrdiff (A.ptr_of ptr) (A.ptr_of arr) in
    let pos = US.v diff / U32.v size_class in
    pos < U32.v (nb_slots size_class) /\
    ptr == slot_array size_class arr (U32.uint_to_t pos)
  ))
  =
  let diff = ptrdiff (A.ptr_of ptr) (A.ptr_of arr) in
  assume (US.fits_u32);
  let size_class_sz = US.uint32_to_sizet size_class in
  assert (US.v size_class_sz == U32.v size_class);
  let pos = US.div diff size_class_sz in
  let rem = US.rem diff size_class_sz in
  assume (US.v rem = US.v pos % U32.v size_class);
  assume (US.v rem == 0);
  assert (diff = US.mul size_class_sz pos);
  assume (U32.v (U32.uint_to_t (US.v pos)) < U32.v (nb_slots size_class));
  slot_array_offset_lemma size_class arr (U32.uint_to_t (US.v pos));

  let ptr' = slot_array size_class arr (U32.uint_to_t (US.v pos)) in
  assert (A.offset (A.ptr_of ptr) == A.offset (A.ptr_of ptr'));
  A.ptr_base_offset_inj (A.ptr_of ptr) (A.ptr_of ptr');
  assert (A.ptr_of ptr == A.ptr_of ptr');
  // CAUTION: discuss with Aymeric, metaproperty
  assume (A.length ptr == U32.v size_class);
  assert (ptr == ptr')

let temp (b: bool)
  : SteelT unit
  (if b then emp else emp)
  (fun _ -> if b then emp else emp)
  =
  return ()

(*)
//TODO: check for spec
let deallocate_slot_aux1
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  : Steel bool
  (
    A.varray md `star`
    A.varray ptr
//    starseq
//      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
//      #(option (Seq.lseq U8.t (U32.v size_class)))
//      (slab_vprop_aux_f size_class md_as_seq arr)
//      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
//      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (fun _ ->
    A.varray md `star`
    A.varray ptr
//    starseq
//      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
//      #(option (Seq.lseq U8.t (U32.v size_class)))
//      (slab_vprop_aux_f size_class md_as_seq arr)
//      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
//      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    same_base_array arr ptr /\
    US.v (ptrdiff (A.ptr_of ptr) (A.ptr_of arr)) < U32.v page_size /\
    US.v (ptrdiff (A.ptr_of ptr) (A.ptr_of arr)) % (U32.v size_class) /\
    A.asel md h0 == G.reveal md_as_seq
  )
  (ensures fun _ _ _ -> True)
  =
  let diff = ptrdiff (A.ptr_of ptr) (A.ptr_of arr) in
  assume (US.fits_u32);
  let size_class_sz = US.uint32_to_sizet size_class in
  let rem = US.rem diff size_class_sz in
  let r = rem = 0sz in
  return r



(*)
- [ok] ptrdiff
- [ok] uintptr_t
- [ok-ish] deallocate_slot_aux
  - bv lemma
  - starseq lemma
- deallocate_slot
