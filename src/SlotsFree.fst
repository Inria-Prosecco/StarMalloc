module SlotsFree

module FI = FStar.Int
module US = FStar.SizeT
module UP = FStar.PtrdiffT
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

open Prelude
open Config
open Utils2
open ExternUtils
open SteelOptUtils
open SteelStarSeqUtils
open FStar.Mul

open SlotsAlloc

let apply_starseq_upd2 (#opened:_)
  (size_class: sc)
  //TODO: remove
  (md: slab_metadata)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
    size_class md_as_seq2 arr pos;
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
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
    v2 == v1)
  =
  assert_norm (4 < FI.max_int U16.n);
  let bm1 = G.hide (a2bv (Bitmap4.set md_as_seq pos)) in
  let bm2 = G.hide (a2bv md_as_seq) in
  let idx = G.hide (Bitmap4.f #4 (U32.v pos)) in
  Bitmap4.set_lemma2 md_as_seq pos;
  assert (G.reveal bm1 == Seq.upd (G.reveal bm2) (G.reveal idx) true);
  SeqUtils.lemma_upd_bij bm2 bm1 (Bitmap5.f #4 (U32.v pos)) true;
  assert (G.reveal bm2 == Seq.upd (G.reveal bm1) (Bitmap5.f #4 (U32.v pos)) false);
  apply_starseq_upd2
    size_class
    md
    (G.hide (Bitmap4.set md_as_seq pos))
    md_as_seq
    arr
    pos;
  return ()

// if this function yields true,
// then it means it is a valid pointer that *could* be allocated
// as pointing to the part of the array that can be allocated
// that is, A.split_r arr (rounding size_class)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let deallocate_slot_aux0
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (ptr: array U8.t)
  (diff: U32.t)
  : Pure bool
  (requires (
    let diff2 = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array arr ptr /\
    0 <= diff2 /\
    diff2 <= U32.v page_size /\
    U32.v diff == diff2
  ))
  (ensures
    fun r ->
      let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
      r = (diff < US.v (rounding size_class))
  )
  =
  let diff_sz = US.uint32_to_sizet diff in
  US.lt diff_sz (rounding size_class)

let deallocate_slot_aux_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (ptr: array U8.t)
  (diff: nat)
  : Lemma
  (requires (
    let diff2 = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array arr ptr /\
    0 <= diff2 /\
    diff2 < US.v (rounding size_class) /\
    diff2 % (U32.v size_class) = 0 /\
    diff == diff2
  ))
  (ensures (
    let r = diff / (U32.v size_class) in
    r < U32.v (nb_slots size_class)
  ))
  =
  let x = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
  let y = US.v (rounding size_class) in
  assert (x % (U32.v size_class) == 0);
  Math.Lemmas.cancel_mul_mod (U32.v (nb_slots size_class)) (U32.v size_class);
  assert (y % (U32.v size_class) == 0);
  assert (x < y)

let deallocate_slot_aux1
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (ptr: array U8.t)
  (diff: U32.t)
  : Pure U32.t
  (requires (
    let diff2 = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array arr ptr /\
    0 <= diff2 /\
    diff2 < US.v (rounding size_class) /\
    diff2 % (U32.v size_class) = 0 /\
    U32.v diff == diff2
  ))
  (ensures fun r ->
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    U32.v r = diff / (U32.v size_class) /\
    U32.v r < U32.v (nb_slots size_class) /\
    U32.v r < U64.n * 4)
  =
  deallocate_slot_aux_lemma size_class arr ptr (U32.v diff);
  let div = U32.div diff size_class in
  div

let slot_array_offset_lemma (size_class: sc) (arr: array U8.t) (pos: U32.t)
  : Lemma
  (requires
    U32.v pos < U32.v (nb_slots size_class) /\
    A.length arr = US.v (rounding size_class))
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
  let shift_size_t = US.uint32_to_sizet shift in
  assert (US.v shift_size_t < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  assert (ptr_shifted == A.ptr_of (slot_array size_class arr pos));
  ()

let deallocate_slot_aux2
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (ptr: array U8.t)
  : Lemma
  (requires (
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array arr ptr /\
    0 <= diff /\
    diff < US.v (rounding size_class) /\
    diff % (U32.v size_class) == 0 /\
    A.length ptr == U32.v size_class
  ))
  (ensures (
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    let pos = diff / U32.v size_class in
    pos < U32.v (nb_slots size_class) /\
    ptr == slot_array size_class arr (U32.uint_to_t pos)
  ))
  =
  let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
  let pos = diff / (U32.v size_class) in
  let rem = diff % (U32.v size_class) in
  assert (rem = 0);
  assert (diff = pos * (U32.v size_class));
  assert (nb_slots size_class = U32.div page_size size_class);
  deallocate_slot_aux_lemma size_class arr ptr diff;
  assert (pos < U32.v (nb_slots size_class));
  slot_array_offset_lemma size_class arr (U32.uint_to_t pos);
  let ptr' = slot_array size_class arr (U32.uint_to_t pos) in
  assert (A.offset (A.ptr_of ptr) == A.offset (A.ptr_of ptr'));
  A.ptr_base_offset_inj (A.ptr_of ptr) (A.ptr_of ptr');
  assert (A.ptr_of ptr == A.ptr_of ptr');
  assert (ptr == ptr')
#pop-options

#push-options "--z3rlimit 50"
let deallocate_slot'_aux0
  (#opened:_)
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  (ptr: array U8.t)
  : SteelGhost unit opened
  (A.varray ptr)
  (fun _ ->
    ((slab_vprop_aux_f size_class (G.reveal md_as_seq) arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
  )
  (requires fun _ ->
    let bm = a2bv md_as_seq in
    ptr == slot_array size_class arr pos /\
    Seq.index bm (Bitmap5.f #4 (U32.v pos)) = false
  )
  (ensures fun h0 _ h1 -> True)
  =
  change_slprop_rel
    (A.varray ptr)
    (A.varray (slot_array size_class arr pos))
    (fun x y -> x == y)
    (fun _ -> ());
  change_slprop_rel
    (A.varray (slot_array size_class arr pos))
    (some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos))
    (fun
      (x: t_of (A.varray (slot_array size_class arr pos)))
      (y: t_of (some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos)))
      ->
      let x' : Seq.lseq U8.t (U32.v size_class) = x in
      let y' : option (Seq.lseq U8.t (U32.v size_class)) = y in
      y' == Some x')
    (fun _ -> ());
  starseq_upd_aux_lemma3 size_class (G.reveal md_as_seq) arr pos;
  SeqUtils.init_u32_refined_index (U32.v (nb_slots size_class)) (U32.v pos);
  assert (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos) == pos);
  assert (Bitmap4.get (G.reveal md_as_seq) pos = false);
  assert (
    (some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos))
    ==
    ((slab_vprop_aux_f size_class (G.reveal md_as_seq) arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
  );
  change_equal_slprop
    (some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos))
    ((slab_vprop_aux_f size_class (G.reveal md_as_seq) arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))

let set_unset_bij
  (size_class: sc)
  (md_as_seq1 md_as_seq2: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires (
    let idx = Bitmap4.f #4 (U32.v pos) in
    let bm0 = Bitmap4.array_to_bv2 md_as_seq1 in
    Seq.index bm0 idx = false /\
    md_as_seq2 = Bitmap4.set md_as_seq1 pos))
  (ensures md_as_seq1 == Bitmap4.unset md_as_seq2 pos)
  =
  let md_as_seq3 = Bitmap4.unset md_as_seq2 pos in
  let bm1 = Bitmap4.array_to_bv2 md_as_seq1 in
  let bm2 = Bitmap4.array_to_bv2 md_as_seq2 in
  let bm3 = Bitmap4.array_to_bv2 md_as_seq3 in
  let idx = Bitmap4.f #4 (U32.v pos) in
  Bitmap4.set_lemma2 #4 md_as_seq1 pos;
  assert (bm2 == Seq.upd bm1 idx true);
  Bitmap4.unset_lemma2 #4 md_as_seq2 pos;
  assert (bm3 == Seq.upd bm2 idx false);
  Seq.lemma_eq_intro bm1 bm3;
  assert (bm1 == bm3);
  Bitmap4.array_to_bv2_inj
    md_as_seq1
    (Bitmap4.unset md_as_seq2 pos)

let unset_set_bij
  (size_class: sc)
  (md_as_seq1 md_as_seq2: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires (
    let idx = Bitmap4.f #4 (U32.v pos) in
    let bm0 = Bitmap4.array_to_bv2 md_as_seq1 in
    Seq.index bm0 idx = true /\
    md_as_seq2 = Bitmap4.unset md_as_seq1 pos))
  (ensures  md_as_seq1 = Bitmap4.set md_as_seq2 pos)
  =
  let md_as_seq3 = Bitmap4.set md_as_seq2 pos in
  let bm1 = Bitmap4.array_to_bv2 md_as_seq1 in
  let bm2 = Bitmap4.array_to_bv2 md_as_seq2 in
  let bm3 = Bitmap4.array_to_bv2 md_as_seq3 in
  let idx = Bitmap4.f #4 (U32.v pos) in
  Bitmap4.unset_lemma2 #4 md_as_seq1 pos;
  assert (bm2 == Seq.upd bm1 idx false);
  Bitmap4.set_lemma2 #4 md_as_seq2 pos;
  assert (bm3 == Seq.upd bm2 idx true);
  Seq.lemma_eq_intro bm1 bm3;
  assert (bm1 == bm3);
  Bitmap4.array_to_bv2_inj
    md_as_seq1
    (Bitmap4.set md_as_seq2 pos)

let deallocate_slot'_aux1
  (#opened: _)
  (size_class: sc)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : SteelGhost unit opened
  (
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
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq2 pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq2 pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    let bm0 = a2bv md_as_seq1 in
    let idx = Bitmap5.f #4 (U32.v pos) in
    Seq.index bm0 idx = true /\
    G.reveal md_as_seq2 == Bitmap4.unset (G.reveal md_as_seq1) pos
  )
  (ensures fun _ _ _ -> True)
  =
  unset_set_bij size_class (G.reveal md_as_seq1) (G.reveal md_as_seq2) pos;
  assert (Bitmap4.set (G.reveal md_as_seq2) pos == G.reveal md_as_seq1);
  starseq_weakening
    #_
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.lseq U8.t (U32.v size_class)))
    (slab_vprop_aux_f size_class md_as_seq1 arr)
    (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq2 pos) arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
    (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq2 pos) arr)
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))

let deallocate_slot'_aux2
  (#opened: _)
  (size_class: sc)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : SteelGhost unit opened
  (
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
      (slab_vprop_aux_f size_class (Bitmap4.unset md_as_seq2 pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.unset md_as_seq2 pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    let bm0 = a2bv md_as_seq1 in
    let idx = Bitmap5.f #4 (U32.v pos) in
    Seq.index bm0 idx = false /\
    G.reveal md_as_seq2 == Bitmap4.set (G.reveal md_as_seq1) pos
  )
  (ensures fun _ _ _ -> True)
  =
  set_unset_bij size_class (G.reveal md_as_seq1) (G.reveal md_as_seq2) pos;
  assert (Bitmap4.unset (G.reveal md_as_seq2) pos == G.reveal md_as_seq1);
  starseq_weakening
    #_
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.lseq U8.t (U32.v size_class)))
    (slab_vprop_aux_f size_class md_as_seq1 arr)
    (slab_vprop_aux_f size_class (Bitmap4.unset md_as_seq2 pos) arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
    (slab_vprop_aux_f_lemma size_class (Bitmap4.unset md_as_seq2 pos) arr)
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))

let u32_bounded
  = v:U32.t{U32.v v < 256}

#restart-solver

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
let deallocate_slot'
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (ptr: array U8.t)
  (diff_: US.t)
  : Steel (bool & G.erased u32_bounded)
  (
    A.varray md `star`
    A.varray ptr `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (fun r ->
    A.varray md `star`
    (if (fst r) then
      emp `star`
      starseq
        #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
        #(option (Seq.lseq U8.t (U32.v size_class)))
        (slab_vprop_aux_f size_class (Bitmap4.unset md_as_seq (snd r)) arr)
        (slab_vprop_aux_f_lemma size_class (Bitmap4.unset md_as_seq (snd r)) arr)
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    else
      A.varray ptr `star`
      starseq
        #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
        #(option (Seq.lseq U8.t (U32.v size_class)))
        (slab_vprop_aux_f size_class md_as_seq arr)
        (slab_vprop_aux_f_lemma size_class md_as_seq arr)
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    )
  )
  (requires fun h0 ->
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array ptr arr /\
    0 <= diff /\
    diff < U32.v page_size /\
    diff % U32.v size_class == 0 /\
    US.v diff_ == diff /\
    A.asel md h0 == G.reveal md_as_seq /\
    A.length ptr == U32.v size_class
  )
  (ensures fun h0 r h1 ->
    // using h0 (A.varray md) instead fails
    let v0 : Seq.lseq U64.t 4 = A.asel md h0 in
    // using A.asel md h1 instead fails
    let v1 : Seq.lseq U64.t 4 = A.asel md h1 in
    (fst r ==>
      U32.v (G.reveal (snd r)) < U32.v (nb_slots size_class) /\
      Bitmap4.get v0 (snd r) = true /\
      v1 == Bitmap4.unset v0 (snd r)) /\
    (not (fst r) ==> v1 == v0)
  )
  =
  let _ = Ghost.hide (UP.mk (FStar.Int.Cast.uint32_to_int16 page_size)) in
  assert_norm (US.v diff_== A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr));
  assert_norm (4 < FI.max_int 16);
  let diff_u32 = US.sizet_to_uint32 diff_ in
  let b = deallocate_slot_aux0 size_class arr ptr diff_u32 in
  if b then (
    deallocate_slot_aux2 size_class arr ptr;
    let pos : u32_bounded
      = deallocate_slot_aux1 size_class arr ptr diff_u32 in
    assert (U32.v pos < U32.v (nb_slots size_class));
    let b = Bitmap5.bm_get #4 md pos in
    if b then (
      Bitmap5.bm_unset #4 md pos;
      let md_as_seq2 = gget (A.varray md) in
      // analogous of Slots@returned_value lemma
      apply_zeroing_u8_cond ptr (u32_to_sz size_class);
      deallocate_slot'_aux0 size_class md_as_seq2 arr pos ptr;
      deallocate_slot'_aux1 size_class md_as_seq md_as_seq2 arr pos;
      deallocate_slot_aux size_class md md_as_seq2 arr pos;
      unset_set_bij size_class (G.reveal md_as_seq) (G.reveal md_as_seq2) pos;
      assert (G.reveal md_as_seq == Bitmap4.set (G.reveal md_as_seq2) pos);
      deallocate_slot'_aux2 size_class md_as_seq2 md_as_seq arr pos;
      return (true, G.hide pos)
    ) else (
      return (false, G.hide 0ul)
    )
  ) else (
    return (false, G.hide 0ul)
  )

let lemma_div_lt
  (d: nat)
  (x: pos)
  (y: pos)
  : Lemma
  (requires d % x == 0 /\ x < y /\ d / x > 0)
  (ensures d / x > d / y)
  = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let bound2_inv2
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires (
    let bm = Bitmap4.array_to_bv2 md_as_seq in
    let idx = Bitmap4.f #4 (U32.v pos) in
    slab_vprop_aux2 size_class md_as_seq /\
    Seq.index bm idx = true
  ))
  (ensures
    slab_vprop_aux2 size_class (Bitmap4.unset md_as_seq pos)
  )
  =
  let bm = Bitmap4.array_to_bv2 md_as_seq in
  let nb_slots_sc = nb_slots size_class in
  let bound2 = bound2_gen nb_slots_sc (G.hide size_class) in
  assert (zf_b (Seq.slice bm 0 (64 - U32.v bound2)));
  let md_as_seq' = Bitmap4.unset md_as_seq pos in
  let bm' = Bitmap4.array_to_bv2 md_as_seq' in
  let nb_slots_sc_rem = U32.rem nb_slots_sc 64ul in
  if (U32.v size_class <= 64)
  then (
    assert (size_class = 16ul \/ size_class = 32ul \/ size_class = 64ul);
    assert (U32.v nb_slots_sc_rem = 0);
    Seq.lemma_empty (Seq.slice bm' 0 (64 - U32.v bound2))
  ) else (
    assert (U32.v size_class > 64);
    lemma_div_lt (U32.v page_size) 64 (U32.v size_class);
    assert (U32.v nb_slots_sc < 64);
    assert (nb_slots_sc_rem = nb_slots_sc);
    let idx = Bitmap4.f #4 (U32.v pos) in
    Bitmap4.unset_lemma2 md_as_seq pos;
    Seq.lemma_eq_intro
      (Seq.slice bm 0 (64 - U32.v bound2))
      (Seq.slice bm' 0 (64 - U32.v bound2))
  )
#pop-options

#restart-solver

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
let deallocate_slot
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  (diff_: US.t)
  : Steel bool
  (A.varray ptr `star` slab_vprop size_class arr md)
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    slab_vprop size_class arr md)
  (requires fun h0 ->
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    //let blob0 : t_of (slab_vprop size_class arr md))
    //  = h0 (slab_vprop size_class arr md) in
    //let v0 : Seq.lseq U64.t 4 = dfst blob0 in
    same_base_array arr ptr /\
    0 <= diff /\
    diff < U32.v page_size /\
    diff % U32.v size_class == 0 /\
    US.v diff_ = diff /\
    A.length ptr == U32.v size_class
  )
    //not (is_empty size_class v0))
  (ensures fun h0 b h1 ->
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    let blob1 : t_of (slab_vprop size_class arr md)
      = h1 (slab_vprop size_class arr md) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    (b ==> not (is_full size_class v1)) /\
    (not b ==> v1 == v0))
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  //TODO: fix
  let md_as_seq : G.erased (Seq.lseq U64.t 4)
    = elim_slab_vprop size_class md arr in
  let r = deallocate_slot' size_class md md_as_seq (A.split_l arr (rounding size_class)) ptr diff_ in
  if (fst r) then (
    change_equal_slprop
      (if (fst r) then
        emp `star`
        starseq
          #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
          #(option (Seq.lseq U8.t (U32.v size_class)))
          (slab_vprop_aux_f size_class (Bitmap4.unset md_as_seq (snd r)) (A.split_l arr (rounding size_class)))
          (slab_vprop_aux_f_lemma size_class (Bitmap4.unset md_as_seq (snd r)) (A.split_l arr (rounding size_class)))
          (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      else
        A.varray ptr `star`
        starseq
          #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
          #(option (Seq.lseq U8.t (U32.v size_class)))
          (slab_vprop_aux_f size_class md_as_seq (A.split_l arr (rounding size_class)))
          (slab_vprop_aux_f_lemma size_class md_as_seq (A.split_l arr (rounding size_class)))
          (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      )
      (emp `star`
      starseq
        #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
        #(option (Seq.lseq U8.t (U32.v size_class)))
        (slab_vprop_aux_f size_class (Bitmap4.unset md_as_seq (snd r)) (A.split_l arr (rounding size_class)))
        (slab_vprop_aux_f_lemma size_class (Bitmap4.unset md_as_seq (snd r)) (A.split_l arr (rounding size_class)))
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))));
    assert (U32.v (G.reveal (snd r)) < U32.v (nb_slots size_class));
    Bitmap4.get_lemma2 (G.reveal md_as_seq) (G.reveal (snd r));
    set_lemma_nonfull size_class (G.reveal md_as_seq) (Bitmap4.unset (G.reveal md_as_seq) (snd r)) (snd r);
    bound2_inv2 size_class (G.reveal md_as_seq) (snd r);
    intro_slab_vprop size_class md (G.hide (Bitmap4.unset md_as_seq (snd r))) arr;
    change_equal_slprop
      emp
      (if (fst r) then emp else A.varray ptr);
    return (fst r)
  ) else  (
    change_equal_slprop
      (if (fst r) then
        emp `star`
        starseq
          #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
          #(option (Seq.lseq U8.t (U32.v size_class)))
          (slab_vprop_aux_f size_class (Bitmap4.unset md_as_seq (snd r)) (A.split_l arr (rounding size_class)))
          (slab_vprop_aux_f_lemma size_class (Bitmap4.unset md_as_seq (snd r)) (A.split_l arr (rounding size_class)))
          (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      else
        A.varray ptr `star`
        starseq
          #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
          #(option (Seq.lseq U8.t (U32.v size_class)))
          (slab_vprop_aux_f size_class md_as_seq (A.split_l arr (rounding size_class)))
          (slab_vprop_aux_f_lemma size_class md_as_seq (A.split_l arr (rounding size_class)))
          (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      )
      (A.varray ptr `star`
      starseq
        #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
        #(option (Seq.lseq U8.t (U32.v size_class)))
        (slab_vprop_aux_f size_class md_as_seq (A.split_l arr (rounding size_class)))
        (slab_vprop_aux_f_lemma size_class md_as_seq (A.split_l arr (rounding size_class)))
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))));
    intro_slab_vprop size_class md md_as_seq arr;
    change_equal_slprop
      (A.varray ptr)
      (if (fst r) then emp else A.varray ptr);
    return (fst r)
  )
#pop-options

(*)
- complications
  - remove expected_size, add a split for each slot
  - page_size % size_class <> 0: take it into account
