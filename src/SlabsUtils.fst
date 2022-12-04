module SlabsUtils

module STU = SizeTUtils
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

module G = FStar.Ghost
module L = FStar.List.Tot
open FStar.Mul

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
//module SR = Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

open Utils2
open SteelOptUtils
open SteelStarSeqUtils
//open SteelFix

#push-options "--z3rlimit 30"
let slot_array (size_class: sc) (arr: array U8.t) (pos: U32.t)
  : Pure (array U8.t)
  (requires
    U32.v pos < U32.v (nb_slots size_class) /\
    A.length arr = U32.v page_size)
  (ensures fun r ->
    A.length r = U32.v size_class /\
    same_base_array r arr /\
    True)
  =
  let ptr = A.ptr_of arr in
  let shift = U32.mul pos size_class in
  nb_slots_correct size_class pos;
  assert (U32.v shift <= U32.v page_size);
  assert_norm (U32.v shift <= FStar.Int.max_int U16.n);
  assert (U32.v shift <= FStar.Int.max_int U16.n);
  let shift_size_t = STU.small_uint32_to_sizet shift in
  assert (US.v shift_size_t < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (| ptr_shifted, G.hide (U32.v size_class) |)
#pop-options

let array_slot (size_class: sc) (arr: array U8.t) (slot: array U8.t)
  : Pure (G.erased int)
  (requires same_base_array arr slot)
  (ensures fun r -> True)
  =
  let ptr1 = A.ptr_of arr in
  assert (A.offset ptr1 <= A.base_len (A.base ptr1));
  let ptr2 = A.ptr_of slot in
  assert (A.offset ptr2 <= A.base_len (A.base ptr2));
  let offset_bytes = A.offset ptr2 - A.offset ptr1 in
  let offset_slot = offset_bytes / (U32.v size_class) in
  offset_slot

let array_slot_slot_array_bij (size_class: sc) (arr: array U8.t) (pos: U32.t)
  : Lemma
  (requires
    U32.v pos < U32.v (nb_slots size_class) /\
    A.length arr = U32.v page_size)
  (ensures (
    let slot_as_array = slot_array size_class arr pos in
    let slot_as_pos = array_slot size_class arr slot_as_array in
    G.reveal slot_as_pos = U32.v pos))
  =
  let ptr = A.ptr_of arr in
  let shift = U32.mul pos size_class in
  nb_slots_correct size_class pos;
  let shift_size_t = STU.small_uint32_to_sizet shift in
  assert (US.v shift_size_t < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  let slot_as_array = slot_array size_class arr pos in
  assert (A.ptr_of slot_as_array == ptr_shifted);
  let offset_bytes = A.offset ptr_shifted - A.offset ptr in
  assert (offset_bytes = U32.v shift);
  assert (offset_bytes = U32.v pos * U32.v size_class);
  let offset_slot = offset_bytes / (U32.v size_class) in
  lemma_div offset_bytes (U32.v pos) (U32.v size_class);
  assert (offset_slot = U32.v pos);
  let slot_as_pos = array_slot size_class arr slot_as_array in
  assert (G.reveal slot_as_pos == offset_slot)

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
  (t_of (slot_vprop size_class arr pos) == Seq.seq U8.t)
  =
  //TODO: FIXME
  admit ()

let slab_vprop_aux_f
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (i: U32.t{U32.v i < U32.v (nb_slots size_class)})
  : vprop
  =
  let vp = slot_vprop size_class arr i in
  slot_vprop_lemma size_class arr i;
  assert_norm (VUnit? vp);
  c2 #(Seq.seq U8.t) (Bitmap4.get md_as_seq i) vp

let slab_vprop_aux_f_lemma
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : (i: U32.t{U32.v i < U32.v (nb_slots size_class)}) ->
    Lemma (
      t_of (slab_vprop_aux_f size_class md_as_seq arr i)
      ==
      option (Seq.seq U8.t))
  =
  fun i ->
  let vp = slot_vprop size_class arr i in
  slot_vprop_lemma size_class arr i;
  assert_norm (VUnit? vp);
  c2_t #(Seq.seq U8.t) (Bitmap4.get md_as_seq i) vp

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
    #(option (Seq.seq U8.t))
    (slab_vprop_aux_f size_class md_as_seq arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq arr)
    incr_seq

let slab_vprop_aux_unpack
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  : Steel unit
  (slab_vprop_aux size_class arr (G.reveal md_as_seq))
  (fun _ ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    h0 (slab_vprop_aux size_class arr (G.reveal md_as_seq))
    ==
    h1 (starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    )
  )
  =
  change_slprop_rel
    (slab_vprop_aux size_class arr md_as_seq)
    (starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))))
    (fun x y -> x == y)
    (fun _ -> ())

let slab_vprop_aux_pack
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  : Steel unit
  (starseq
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.seq U8.t))
    (slab_vprop_aux_f size_class md_as_seq arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq arr)
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))))
  (fun _ ->
    slab_vprop_aux size_class arr (G.reveal md_as_seq)
  )
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    h1 (slab_vprop_aux size_class arr (G.reveal md_as_seq))
    ==
    h0 (starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    )
  )
  =
  change_slprop_rel
    (starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))))
    (slab_vprop_aux size_class arr md_as_seq)
    (fun x y -> x == y)
    (fun _ -> ())

let slab_vprop_aux_idem
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  : Steel unit
  (slab_vprop_aux size_class arr (G.reveal md_as_seq))
  (fun _ -> slab_vprop_aux size_class arr (G.reveal md_as_seq))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    h1 (slab_vprop_aux size_class arr (G.reveal md_as_seq))
    ==
    h0 (slab_vprop_aux size_class arr (G.reveal md_as_seq))
  )
  =
  slab_vprop_aux_unpack size_class arr md_as_seq;
  slab_vprop_aux_pack size_class arr md_as_seq;
  return ()

//unfold
//[@@__steel_reduce__]
let slab_vprop
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  =
  A.varray md `vdep` (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class arr md_as_seq)


//works
let slab_vprop1
  (md: slab_metadata)
  =
  reveal_emp ();
  assume (normal (t_of emp) == unit);
  emp `vdep` (fun _ -> emp)

//works
let slab_vprop2
  (md: slab_metadata)
  =
  A.varray md `vdep` (fun (x: Seq.seq U64.t) -> emp)

let slab_vprop3
  (md: slab_metadata)
  =
  A.varray md `vdep` (fun (x: Seq.lseq U64.t 4) -> emp)

let slab_vprop4_aux
  = fun (x: Seq.lseq U64.t 4) -> emp

let slab_vprop4
  (md: array U64.t{A.length md = 4})
  =
  A.varray md `vdep`
    (fun (x: Seq.lseq U64.t 4) -> slab_vprop4_aux x)

let slab_vprop_test
  (md: slab_metadata)
  = slab_vprop4 md

#push-options "--print_implicits"

let t (md: array U64.t)
  : Lemma
  (requires A.length md = 4)
  (ensures
    //normal (t_of (A.varray md)) == Seq.lseq U64.t 4
    t_of (A.varray md) == Seq.lseq U64.t 4
  )
  = ()


//inline_for_extraction
//let elim_intro_vdep_test_aux3
//  (size_class: sc)
//  (md: array U64.t{A.length md = 4})
//  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
//  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
//  (arr: array U8.t{A.length arr = U32.v page_size})
//  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
//  : Lemma
//  (requires
//    Bitmap4.get
//  )
//  (
//    (slab_vprop_aux_f size_class md_as_seq1 arr)
//      (Seq.index
//        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
//        (U32.v pos)))
//  (fun _ -> slot_vprop size_class arr pos)

let a2bv = Bitmap4.array_to_bv2 #4

inline_for_extraction
let elim_intro_vdep_test_aux2_lemma
  (size_class: sc)
  (md: array U64.t{A.length md = 4})
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  (k:nat{k <> (U32.v pos) /\ k < U32.v (nb_slots size_class)})
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
        k))
    ==
    ((slab_vprop_aux_f size_class md_as_seq1 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        k))
  )
  =
  //assert (U32.v (nb_slots size_class) <= 4 * U64.n);
  //let k : k2:U32.t{U32.v k2 < 4 * U64.n}
  //  = (U32.uint_to_t k) <: (k2:U32.t{U32.v k2 < 4 * U64.n}) in
  //Bitmap4.get_lemma md_as_seq1 k;
  //Bitmap4.get_lemma md_as_seq2 k;
  //assert (Bitmap4.get md_as_seq1 k == Bitmap4.get md_as_seq2 k);
  admit ()

inline_for_extraction
let elim_intro_vdep_test_aux2_lemma2
  (size_class: sc)
  (md: array U64.t{A.length md = 4})
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
    elim_intro_vdep_test_aux2_lemma
      size_class md md_as_seq1 md_as_seq2 arr pos
  ))

let elim_intro_vdep_test_aux2_lemma3
  (size_class: sc)
  (md: array U64.t{A.length md = 4})
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
    none_as_emp #(Seq.seq U8.t)
  )
  = admit ()

let elim_intro_vdep_test_aux2_lemma4
  (size_class: sc)
  (md: array U64.t{A.length md = 4})
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires True)
  (ensures (
    slot_vprop_lemma size_class arr pos;
    ((slab_vprop_aux_f size_class md_as_seq1 arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
    ==
    some_as_vp #(Seq.seq U8.t) (slot_vprop size_class arr pos)
  ))
  = admit ()

inline_for_extraction
let elim_intro_vdep_test_aux3
  (size_class: sc)
  (md: array U64.t{A.length md = 4})
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Steel unit
  (
  starseq
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.seq U8.t))
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
    #(option (Seq.seq U8.t))
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
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq1 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0;
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq2 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq2 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1;
    let v1 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq1 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0 in
    let v2 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq2 arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq2 arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1 in
    v2 == Seq.upd v1 (U32.v pos) None)
  =
  elim_intro_vdep_test_aux2_lemma2
    size_class md md_as_seq1 md_as_seq2 arr pos;
  elim_intro_vdep_test_aux2_lemma3
    size_class md md_as_seq1 md_as_seq2 arr pos;
  starseq_upd3
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(Seq.seq U8.t)
    (slab_vprop_aux_f size_class md_as_seq1 arr)
    (slab_vprop_aux_f size_class md_as_seq2 arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq1 arr)
    (slab_vprop_aux_f_lemma size_class md_as_seq2 arr)
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (U32.v pos)

let rewriting_f1_seq_index_s_n_as_returned_value
  (size_class: sc)
  (md: array U64.t{A.length md = 4})
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Steel (array U8.t)
  ((slab_vprop_aux_f size_class md_as_seq arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
  (fun r -> A.varray r)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> True)
  =
  let r = slot_array size_class arr pos in
  //TODO: selector relation
  rewrite_slprop
    ((slab_vprop_aux_f size_class md_as_seq arr)
      (Seq.index
        (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
        (U32.v pos)))
    (A.varray r)
    //(fun x y -> Some?.v x == y)
    (fun _ -> admit ());
  return r

//#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
inline_for_extraction
let elim_intro_vdep_test_aux
  (size_class: sc)
  (md: array U64.t{A.length md = 4})
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Steel (array U8.t)
  (
  A.varray md `star`
  starseq
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.seq U8.t))
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
    #(option (Seq.seq U8.t))
    (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
    (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    let bm0 = Bitmap4.array_to_bv2 (A.asel md h0) in
    let idx = Bitmap5.f #4 (U32.v pos) in
    A.asel md h0 == G.reveal md_as_seq /\
    Seq.index bm0 idx = false
  )
  (ensures fun h0 _ h1 ->
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0;
    v_starseq_len
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1;
    let v1 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h0 in
    let v2 = v_starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.seq U8.t))
      (slab_vprop_aux_f size_class (Bitmap4.set md_as_seq pos) arr)
      (slab_vprop_aux_f_lemma size_class (Bitmap4.set md_as_seq pos) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      h1 in
    v2 == Seq.upd v1 (U32.v pos) None)
  =
  assert_norm (4 < FStar.Int.max_int U16.n);
  Bitmap5.bm_set #4 md pos;
  elim_intro_vdep_test_aux3
    size_class
    md
    md_as_seq
    (Bitmap4.set md_as_seq pos)
    arr
    pos;
  let r = rewriting_f1_seq_index_s_n_as_returned_value
    size_class md md_as_seq arr pos in
  return r

(*)
#push-options "--z3rlimit 30"
let elim_intro_vdep_test
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Steel unit
  (slab_vprop size_class arr md)
  (fun r -> slab_vprop size_class arr md)
  (requires fun h0 ->
    let bm0 = Bitmap4.array_to_bv2 (A.asel md h0) in
    let idx = Bitmap5.f #4 (U32.v pos) in
    Seq.index bm0 idx = false)
  (ensures fun h0 _ h1 ->
    h1 (slab_vprop size_class arr md)
    ==
    h0 (slab_vprop size_class arr md)
  )
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  //let md_as_seq : G.erased (normal (t_of (A.varray md))) = elim_vdep
  //let md_as_seq : G.erased (Seq.lseq U64.t 4) = elim_vdep
  let md_as_seq = elim_vdep
    (A.varray md)
    (fun (x: Seq.lseq U64.t 4) -> slab_vprop_aux size_class arr x)
  in
  let md_as_seq2 = G.hide ((G.reveal md_as_seq) <: Seq.lseq U64.t 4) in
  change_slprop_rel
    (slab_vprop_aux size_class arr (G.reveal md_as_seq))
    (slab_vprop_aux size_class arr (G.reveal md_as_seq2))
    (fun x y -> x == y)
    (fun _ -> ());
  //slassert (A.varray md `star` slab_vprop_aux size_class arr (G.reveal md_as_seq2));
  slab_vprop_aux_idem size_class arr md_as_seq2;
  //slab_vprop_aux_unpack size_class arr md_as_seq2;
  //elim_intro_vdep_test_aux
  //  size_class
  //  md
  //  md_as_seq2
  //  arr
  //  pos;
  //slab_vprop_aux_pack size_class arr md_as_seq2;
  intro_vdep
    (A.varray md)
    (slab_vprop_aux size_class arr md_as_seq2)
    (fun (x: Seq.lseq U64.t 4) -> slab_vprop_aux size_class arr x);
  return ()
#pop-options
