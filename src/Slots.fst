module Slots

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

#push-options "--fuel 1 --ifuel 0 --z3rlimit 30"
let slot_array (size_class: sc) (arr: array U8.t) (pos: U32.t)
  : Pure (array U8.t)
  (requires
    U32.v pos < U32.v (nb_slots size_class) /\
    A.length arr = U32.v page_size)
  (ensures fun r ->
    A.length r == U32.v size_class /\
    same_base_array r arr /\
    True)
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
  (| ptr_shifted, G.hide (U32.v size_class) |)
#pop-options

let slot_vprop
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  =
  A.varray (slot_array size_class arr pos)

let slot_vprop_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (t_of (slot_vprop size_class arr pos) == Seq.lseq U8.t (U32.v size_class))
  =
  ()

let slab_vprop_aux_f
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (i: U32.t{U32.v i < U32.v (nb_slots size_class)})
  : vprop
  =
  let vp = slot_vprop size_class arr i in
  slot_vprop_lemma size_class arr i;
  c2 #(Seq.lseq U8.t (U32.v size_class)) (not (Bitmap4.get md_as_seq i)) vp

let slab_vprop_aux_f_lemma
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : (i: U32.t{U32.v i < U32.v (nb_slots size_class)}) ->
    Lemma (
      t_of (slab_vprop_aux_f size_class md_as_seq arr i)
      ==
      option (Seq.lseq U8.t (U32.v size_class)))
  =
  fun i ->
  let vp = slot_vprop size_class arr i in
  slot_vprop_lemma size_class arr i;
  c2_t #(Seq.lseq U8.t (U32.v size_class)) (Bitmap4.get md_as_seq i) vp

let slab_vprop_aux
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md_as_seq: Seq.lseq U64.t 4)
  : vprop
  =
  let nb_slots_as_nat = U32.v (nb_slots size_class) in
  let incr_seq = SeqUtils.init_u32_refined nb_slots_as_nat in
  starseq
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.lseq U8.t (U32.v size_class)))
    (slab_vprop_aux_f size_class md_as_seq arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq arr)
    incr_seq

let slab_vprop_aux2
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  : prop
  =
  let bm = Bitmap4.array_to_bv2 md_as_seq in
  let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
  zf_b (Seq.slice bm 0 (64 - U32.v bound2))

//unfold
//[@@__steel_reduce__]
open SteelVRefineDep


let slab_vprop
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  =
  vrefinedep
    (A.varray md)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_r arr 0sz) md_as_seq)
  `star`
  A.varray (A.split_l arr 0sz)

#push-options "--print_implicits"

noextract
let a2bv = Bitmap4.array_to_bv2 #4
//noextract
//let f = Bitmap5.f #4

//TODO: move to Bitmap5/BitmapUtils
let f_invol (#n: nat)
  (k:nat{k < n * U64.n})
  : Lemma
  (Bitmap5.f #n (Bitmap5.f #n k) == k)
  =
  ()

//TODO: move to Bitmap5/BitmapUtils
let equiv_get_a2bv_index
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (k:nat{k < U32.v (nb_slots size_class)})
  : Lemma
  (Bitmap4.get md_as_seq (U32.uint_to_t k)
  == Seq.index (a2bv md_as_seq) (Bitmap5.f #4 k))
  =
  let k' = U32.uint_to_t k in
  let bm = a2bv md_as_seq in
  let k_index = Bitmap5.f #4 k in
  let v1 = Bitmap4.get md_as_seq k' in
  let v2 = Seq.index bm k_index in
  Bitmap4.get_lemma md_as_seq k';
  assert (v1 == FU.nth (U64.v (Seq.index md_as_seq (k/U64.n))) (U64.n - (k%U64.n) - 1));
  Bitmap4.array_to_bv2_index md_as_seq k_index;
  f_invol #4 k;
  assert (Bitmap5.f #4 k_index == k);
  ()

let starseq_upd_aux_lemma1_aux
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  (v: bool)
  (k:nat{k <> (U32.v pos) /\ k < U32.v (nb_slots size_class)})
  : Lemma
  (requires (
    let bm1 = a2bv (G.reveal md_as_seq1) in
    let bm2 = a2bv (G.reveal md_as_seq2) in
    Seq.index bm1 (Bitmap5.f #4 (U32.v pos)) = v /\
    bm2 == Seq.upd bm1 (Bitmap5.f #4 (U32.v pos)) (not v)
  ))
  (ensures
    (slab_vprop_aux_f size_class md_as_seq2 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        k)
    ==
    (slab_vprop_aux_f size_class md_as_seq1 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        k)
  )
  =
  let bm1 = a2bv (G.reveal md_as_seq1) in
  let bm2 = a2bv (G.reveal md_as_seq2) in
  let k_index = Bitmap5.f #4 k in
  Seq.lemma_index_upd2 bm1 (Bitmap5.f #4 (U32.v pos)) (not v) k_index;
  assert (Seq.index bm1 k_index = Seq.index bm2 k_index);
  equiv_get_a2bv_index size_class md_as_seq1 k;
  equiv_get_a2bv_index size_class md_as_seq2 k;
  assert (Bitmap4.get md_as_seq1 (U32.uint_to_t k) == Seq.index bm1 k_index);
  assert (Bitmap4.get md_as_seq2 (U32.uint_to_t k) == Seq.index bm2 k_index);
  SeqUtils.init_u32_refined_index (U32.v (nb_slots size_class)) k;
  assert (Seq.index (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))) k = U32.uint_to_t k)

let starseq_upd_aux_lemma1
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  (v: bool)
  : Lemma
  (requires (
    let bm1 = a2bv (G.reveal md_as_seq1) in
    let bm2 = a2bv (G.reveal md_as_seq2) in
    Seq.index bm1 (Bitmap5.f #4 (U32.v pos)) = v /\
    bm2 == Seq.upd bm1 (Bitmap5.f #4 (U32.v pos)) (not v)
  ))
  (ensures
    forall (k:nat{k <> (U32.v pos) /\ k < U32.v (nb_slots size_class)}).
    ((slab_vprop_aux_f size_class md_as_seq2 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        k))
    ==
    ((slab_vprop_aux_f size_class md_as_seq1 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        k))
  )
  =
  Classical.forall_intro (Classical.move_requires (
    starseq_upd_aux_lemma1_aux
      size_class md md_as_seq1 md_as_seq2 arr pos v
  ))

let starseq_upd_aux_lemma2
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
    Seq.index bm1 (Bitmap5.f #4 (U32.v pos)) = false /\
    bm2 == Seq.upd bm1 (Bitmap5.f #4 (U32.v pos)) true
  ))
  (ensures
    ((slab_vprop_aux_f size_class md_as_seq2 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
    ==
    none_as_emp #(Seq.lseq U8.t (U32.v size_class))
  )
  =
  let bm2 = a2bv (G.reveal md_as_seq2) in
  SeqUtils.init_u32_refined_index (U32.v (nb_slots size_class)) (U32.v pos);
  assert (Seq.index (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))) (U32.v pos) = pos);
  let k_index = Bitmap5.f #4 (U32.v pos) in
  assert (Seq.index bm2 k_index = true);
  equiv_get_a2bv_index size_class md_as_seq2 (U32.v pos);
  assert (Bitmap4.get md_as_seq2 pos = Seq.index bm2 k_index);
  assert (Bitmap4.get md_as_seq2 pos = true)

let apply_starseq_upd (#opened:_)
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
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
  (
  fun _ ->
  //A.varray md `star`
  (slab_vprop_aux_f size_class md_as_seq1 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)) `star`
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
    Seq.index bm1 (Bitmap5.f #4 (U32.v pos)) = false /\
    bm2 == Seq.upd bm1 (Bitmap5.f #4 (U32.v pos)) true)
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
    v2 == Seq.upd v1 (U32.v pos) None)
  =
  starseq_upd_aux_lemma1
    size_class md md_as_seq1 md_as_seq2 arr pos false;
  starseq_upd_aux_lemma2
    size_class md md_as_seq1 md_as_seq2 arr pos;
  starseq_upd3
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

let starseq_upd_aux_lemma3
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires (
    let bm = a2bv (G.reveal md_as_seq) in
    Seq.index bm (Bitmap5.f #4 (U32.v pos)) = false
  ))
  (ensures
    ((slab_vprop_aux_f size_class md_as_seq arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
    ==
    some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos)
  )
  =
  let bm = a2bv (G.reveal md_as_seq) in
  SeqUtils.init_u32_refined_index (U32.v (nb_slots size_class)) (U32.v pos);
  assert (Seq.index (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))) (U32.v pos) = pos);
  let k_index = Bitmap5.f #4 (U32.v pos) in
  assert (Seq.index bm k_index = false);
  equiv_get_a2bv_index size_class md_as_seq (U32.v pos);
  assert (Bitmap4.get md_as_seq pos = Seq.index bm k_index);
  assert (Bitmap4.get md_as_seq pos = false)

let get_slot_as_returned_value
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Steel (array U8.t)
  ((slab_vprop_aux_f size_class (G.reveal md_as_seq) arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
  (fun r -> A.varray r)
  (requires fun h0 ->
    let bm = a2bv md_as_seq in
    Seq.index bm (Bitmap5.f #4 (U32.v pos)) = false)
  (ensures fun h0 _ h1 -> True)
  =
  starseq_upd_aux_lemma3 size_class (G.reveal md_as_seq) arr pos;
  change_slprop_rel
    ((slab_vprop_aux_f size_class md_as_seq arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
    (some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos))
    (fun x y -> x == y)
    (fun _ -> ());
  let r = slot_array size_class arr pos in
  change_slprop_rel
    (some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos))
    (A.varray r)
    (fun
      (x: t_of (some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (slot_vprop size_class arr pos)))
      (y: t_of (A.varray r))
      ->
      let x' : option (Seq.lseq U8.t (U32.v size_class)) = x in
      let y' : Seq.lseq U8.t (U32.v size_class) = y in
      x' == Some y')
    (fun _ -> ());
  return r

noextract inline_for_extraction
let allocate_slot_aux
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Steel (array U8.t)
  (
  A.varray md `star`
  starseq
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.lseq U8.t (U32.v size_class)))
    (slab_vprop_aux_f size_class md_as_seq arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq arr)
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (
  fun r ->
  A.varray md `star`
  A.varray r `star`
  starseq
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.lseq U8.t (U32.v size_class)))
    (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
    (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
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
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0;
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1;
    let blob1 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0 in
    let blob2 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1 in
    let v1 = A.asel md h0 in
    let v2 = A.asel md h1 in
    //let idx = Bitmap5.f #4 (U32.v pos) in
    v2 == Bitmap4.set v1 pos /\
    blob2 == Seq.upd blob1 (U32.v pos) None)
  =
  assert_norm (4 < FI.max_int U16.n);
  Bitmap5.bm_set #(Ghost.hide 4) md pos;
  apply_starseq_upd
    size_class
    md
    md_as_seq
    (Bitmap4.set md_as_seq pos)
    arr
    pos;
  let r = get_slot_as_returned_value
    size_class md_as_seq arr pos in
  return r

//TODO: FIXME @SizeT lib
//assert (US.fits 256): impossible?

let f_lemma (#n: nat)
  (q:nat{q < n})
  (r:nat{r < U64.n})
  (r1:nat{r1 < n * U64.n})
  (r2:nat{r2 < n * U64.n})
  : Lemma
  (requires
    r1 == q * U64.n + r /\
    r2 == q * U64.n + (U64.n - r - 1)
  )
  (ensures
    r2 == Bitmap5.f #n r1
  )
  = ()

#push-options "--z3rlimit 50"
inline_for_extraction noextract
let get_free_slot_aux
  (size_class: sc)
  (bitmap: slab_metadata)
  (i: U32.t)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    U32.v i < U32.v (nb_slots size_class) / 64 /\
    U64.v (Seq.index (A.asel bitmap h0) (U32.v i)) <> U64.v max64)
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    //True)
    Seq.index bm idx = false)
  )
  =
  let h0 = get () in
  assert (U32.v i <= 3);
  assert_norm (3 <= FI.max_int U16.n);
  let i2 = STU.small_uint32_to_sizet i in
  let x = A.index bitmap i2 in
  max64_lemma x;
  let r = ffs64 x (G.hide 64ul) in
  let bm = G.hide (Bitmap4.array_to_bv2 (A.asel bitmap h0)) in
  let idx1 = G.hide ((U32.v i) * 64) in
  let idx2 = G.hide ((U32.v i + 1) * 64) in
  assert (x == Seq.index (A.asel bitmap h0) (U32.v i));
  assert (FU.nth (U64.v x) (U64.n - 1 - U32.v r) = false);
  array_to_bv_slice (A.asel bitmap h0) (U32.v i);
  assert (FU.to_vec (U64.v x) == Seq.slice bm ((U32.v i)*64) ((U32.v i + 1)*64));
  assert (Seq.index (Seq.slice bm ((U32.v i)*64) ((U32.v i + 1)*64)) (U64.n - U32.v r - 1) = false);
  Seq.lemma_index_slice bm ((U32.v i)*64) ((U32.v i + 1)*64) (U32.v r);
  let idx = G.hide ((U32.v i)*64 + (U64.n - U32.v r - 1)) in
  assert (Seq.index bm (G.reveal idx) = false);
  let r' = U32.mul i 64ul in
  let r'' = U32.add r r' in
  assert (U32.v r'' = U32.v i * 64 + U32.v r);
  f_lemma #4 (U32.v i) (U32.v r) (U32.v r'') (G.reveal idx);
  assert (G.reveal idx == Bitmap5.f #4 (U32.v r''));
  assert (Seq.index bm (Bitmap5.f #4 (U32.v r'')) = false);
  r''
#pop-options

#push-options "--z3rlimit 50"
inline_for_extraction noextract
let get_free_slot_aux2
  (size_class: sc)
  (bitmap: slab_metadata)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
    zf_b (Seq.slice bm 0 (64 - U32.v bound2)) /\
    U64.v (Seq.index (A.asel bitmap h0) 0) <> U64.v (full_n bound2))
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false)
  )
  =
  let h0 = get () in
  let x = A.index bitmap 0sz in
  let bound2 = G.hide (bound2_gen (nb_slots size_class) (G.hide size_class)) in
  let bm = G.hide (Bitmap4.array_to_bv2 (A.asel bitmap h0)) in
  array_to_bv_slice (A.asel bitmap h0) 0;
  assert (FU.to_vec (U64.v x) == Seq.slice bm 0 64);
  Seq.slice_slice bm 0 64 0 (64 - U32.v bound2);
  assert (zf_b (Seq.slice (FU.to_vec #64 (U64.v x)) 0 (64 - U32.v bound2)));
  full_n_lemma x bound2;
  assert (U32.lte bound2 (nb_slots size_class));
  let r = ffs64 x bound2 in
  assert (x == Seq.index (A.asel bitmap h0) 0);
  assert (FU.nth (U64.v x) (U64.n - 1 - U32.v r) = false);
  assert (Seq.index (Seq.slice bm 0 64) (U64.n - 1 - U32.v r) = false);
  Seq.lemma_index_slice bm 0 64 (U32.v r);
  assert (Seq.index bm (U64.n - 1 - U32.v r) = false);
  f_lemma #4 0 (U32.v r) (U32.v r) (U64.n - 1 - U32.v r);
  r
#pop-options

let get_free_slot (size_class: sc) (bitmap: slab_metadata)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    let s = A.asel bitmap h0 in
    let bm = Bitmap4.array_to_bv2 s in
    let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
    zf_b (Seq.slice bm 0 (64 - U32.v bound2)) /\
    has_free_slot size_class s
  )
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false)
  )
  =
  let h0 = get () in
  let bm = G.hide (Bitmap4.array_to_bv2 (A.asel bitmap h0)) in
  let nb_slots_v = nb_slots size_class in
  let bound = U32.div nb_slots_v 64ul in
  let bound2 = bound2_gen nb_slots_v (G.hide size_class) in
  let full = full_n bound2 in
  assert (U32.v bound == U32.v (nb_slots size_class) / 64);
  let x1 = A.index bitmap 0sz in
  if (U64.eq x1 full && U32.gt bound 1ul) then (
    let x2 = A.index bitmap 1sz in
    if (U64.eq x2 max64 && U32.gt bound 2ul) then (
      let x3 = A.index bitmap 2sz in
      if (U64.eq x3 max64 && U32.gt bound 3ul) then (
        get_free_slot_aux size_class bitmap 3ul
      ) else (
        get_free_slot_aux size_class bitmap 2ul
      )
    ) else (
      get_free_slot_aux size_class bitmap 1ul
    )
  ) else (
    get_free_slot_aux2 size_class bitmap
  )

#push-options "--z3rlimit 30"
let intro_slab_vprop (#opened:_)
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  : SteelGhost unit opened
  (A.varray md `star`
    A.varray (A.split_l arr 0sz) `star`
    slab_vprop_aux size_class (A.split_r arr 0sz) (G.reveal md_as_seq))
  (fun _ -> slab_vprop size_class arr md)
  (requires fun h0 ->
    G.reveal md_as_seq == A.asel md h0 /\
    slab_vprop_aux2 size_class md_as_seq
  )
  (ensures fun h0 _ h1 ->
    let blob1 : t_of (slab_vprop size_class arr md)
      = h1 (slab_vprop size_class arr md) in
    let x1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    x1 == A.asel md h0 /\
    dsnd (fst blob1) == h0 (slab_vprop_aux size_class (A.split_r arr 0sz) (G.reveal md_as_seq)) /\
    snd blob1 == A.asel (A.split_l arr 0sz) h0
  )
  =
  intro_vrefinedep
    (A.varray md)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_r arr 0sz) md_as_seq)
    (slab_vprop_aux size_class (A.split_r arr 0sz) (G.reveal md_as_seq));
  change_slprop_rel
    (vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_r arr 0sz) md_as_seq)
    `star`
    A.varray (A.split_l arr 0sz))
    (slab_vprop size_class arr md)
    (fun x y -> x == y)
    (fun _ -> admit ())

let elim_slab_vprop (#opened:_)
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : SteelGhost (G.erased (Seq.lseq U64.t 4)) opened
  (slab_vprop size_class arr md)
  (fun r ->
    A.varray md `star`
    A.varray (A.split_l arr 0sz) `star`
    slab_vprop_aux size_class (A.split_r arr 0sz) r)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let x0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    G.reveal r == x0 /\
    G.reveal r == A.asel md h1 /\
    dsnd (fst blob0) == h1 (slab_vprop_aux size_class (A.split_r arr 0sz) r) /\
    snd blob0 == A.asel (A.split_l arr 0sz) h1 /\
    slab_vprop_aux2 size_class (G.reveal r)
  )
  =
  change_slprop_rel
    (slab_vprop size_class arr md)
    (vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_r arr 0sz) md_as_seq)
    `star`
    A.varray (A.split_l arr 0sz))
    (fun x y -> x == y)
    (fun _ -> admit ());
  let md_as_seq
    : G.erased (t_of (vrefine
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
    ))
    = elim_vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_r arr 0sz) md_as_seq)
  in
  let md_as_seq2
    : G.erased (Seq.lseq U64.t 4)
    = G.hide (G.reveal md_as_seq <: Seq.lseq U64.t 4) in
  change_equal_slprop
    (slab_vprop_aux size_class (A.split_r arr 0sz) (G.reveal md_as_seq))
    (slab_vprop_aux size_class (A.split_r arr 0sz) (G.reveal md_as_seq2));
  md_as_seq2

let bound2_inv
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires slab_vprop_aux2 size_class md_as_seq)
  (ensures slab_vprop_aux2 size_class (Bitmap4.set md_as_seq pos))
  = admit ()

let allocate_slot
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : Steel (array U8.t)
  (slab_vprop size_class arr md)
  (fun r -> A.varray r `star` slab_vprop size_class arr md)
  (requires fun h0 ->
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    has_free_slot size_class v0)
  (ensures fun h0 _ h1 ->
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let blob1 : t_of (slab_vprop size_class arr md)
      = h1 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    not (is_empty size_class v1))
    //U32.v (G.reveal (snd r)) < U64.n * 4 /\
    //v1 == Bitmap4.set v0 (G.reveal (snd r)))
    //TODO: is it worth having such a precise spec?
    //requires having pos as ghost in returned value
    //considering the case of multiple consecutive allocations
    //probably for testing slab filling
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  let md_as_seq : G.erased (Seq.lseq U64.t 4)
    = elim_slab_vprop size_class md arr in
  assert (has_free_slot size_class (G.reveal md_as_seq));
  let pos = get_free_slot size_class md in
  let r = allocate_slot_aux
    size_class
    md
    md_as_seq
    (A.split_r arr 0sz)
    pos in
  set_lemma_nonzero size_class (G.reveal md_as_seq) (Bitmap4.set (G.reveal md_as_seq) pos) pos;
  bound2_inv size_class (G.reveal md_as_seq) pos;
  intro_slab_vprop size_class md (G.hide (Bitmap4.set (G.reveal md_as_seq) pos)) arr;
  return r
#pop-options
