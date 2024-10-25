module SlotsAlloc

module FU = FStar.UInt
module FI = FStar.Int
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

open Prelude
open Constants
open Config
open Utils2
open ExternUtils
open SteelOptUtils
open SteelStarSeqUtils

#push-options "--fuel 0 --ifuel 0"

#push-options "--z3rlimit 50"
let slot_array (size_class: sc) (arr: array U8.t) (pos: U32.t)
  : Pure (array U8.t)
  (requires
    U32.v pos < U32.v (nb_slots size_class) /\
    A.length arr >= US.v (rounding size_class))
  (ensures fun r ->
    A.length r == U32.v size_class /\
    same_base_array r arr /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) >= 0 /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) < U32.v page_size /\
    (A.offset (A.ptr_of r) - A.offset (A.ptr_of arr)) % (U32.v size_class) == 0
  )
  =
  let ptr = A.ptr_of arr in
  let shift = U32.mul pos size_class in
  Math.Lemmas.cancel_mul_mod (U32.v pos) (U32.v size_class);
  assert (U32.v shift % U32.v size_class == 0);
  nb_slots_correct size_class pos;
  assert (U32.v shift <= U32.v page_size);
  assert_norm (U32.v shift <= FI.max_int U16.n);
  assert (U32.v shift <= FI.max_int U16.n);
  let shift_size_t = US.uint32_to_sizet shift in
  assert (US.v shift_size_t < A.length arr);
  assert (US.v shift_size_t % U32.v size_class == 0);
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (| ptr_shifted, G.hide (U32.v size_class) |)
#pop-options

let slot_vprop
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  =
  A.varray (slot_array size_class arr pos)

#push-options "--fuel 1 --ifuel 1"
let slot_vprop_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (t_of (slot_vprop size_class arr pos) == Seq.lseq U8.t (U32.v size_class))
  =
  ()
#pop-options

let slab_vprop_aux_f
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (i: U32.t{U32.v i < U32.v (nb_slots size_class)})
  : vprop
  =
  let vp = slot_vprop size_class arr i in
  slot_vprop_lemma size_class arr i;
  c2 #(Seq.lseq U8.t (U32.v size_class)) (not (Bitmap4.get md_as_seq i)) vp

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_aux_f_lemma
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
#pop-options

let slab_vprop_aux
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_aux_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (md_as_seq: Seq.lseq U64.t 4)
  : Lemma
  (t_of (slab_vprop_aux size_class arr md_as_seq)
  ==
  Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class))
  )
  =
  assert (Seq.length (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))) == U32.v (nb_slots size_class));
  ()
#pop-options

let slab_vprop_aux2
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  : prop
  =
  let nb_slots_sc = nb_slots size_class in
  let bound = U32.div nb_slots_sc 64ul in
  let bound2 = bound2_gen nb_slots_sc (G.hide size_class) in
  let bm = Bitmap4.array_to_bv2 md_as_seq in
  zf_b (Seq.slice bm 0 (64 - U32.v bound2)) /\
  (U32.lte bound 3ul ==> Seq.index md_as_seq 3 == 0UL) /\
  (U32.lte bound 2ul ==> Seq.index md_as_seq 2 == 0UL) /\
  (U32.lte bound 1ul ==> Seq.index md_as_seq 1 == 0UL)

open SteelVRefineDep

#push-options "--fuel 1 --ifuel 1"
let slab_vprop
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  =
  vrefinedep
    (A.varray md)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
  `star`
  A.varray (A.split_r arr (rounding size_class))
#pop-options

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_lemma_aux
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  : Lemma
  (t_of (vrefinedep
    (A.varray md)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
  )
  ==
    dtuple2
      (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
      (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
  )
  =
  let aux (n1 n2:nat) (p:Seq.lseq U64.t n1 -> prop) : Lemma
      (requires n1 == n2)
      (ensures (x:Seq.lseq U64.t n1{p x}) == (x:Seq.lseq U64.t n2{p x}))
    = () in
    let aux2 (a a':Type) (b c:Type) : Lemma
      (requires a == a' /\ b == c)
      (ensures dtuple2 a (fun _ -> b) == dtuple2 a' (fun _ -> c))
    = () in
    // The SMT solver needs some help to prove type equality, with rewritings deep in the terms.
    // In particular, it does not seem to be able to apply the rewritings for aux and aux2 without
    // explicit calls to the lemmas when they occur under dtuple2
    assert_norm (
      t_of (vrefinedep
        (A.varray md)
        (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
        (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
      )
      ==
      dtuple2
        (x:Seq.lseq U64.t (A.length md){slab_vprop_aux2 size_class x})
        (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class))))
          (Seq.length (SeqUtils.init_u32_refined (UInt32.v (nb_slots size_class)))))
    );
   aux (A.length md) 4 (slab_vprop_aux2 size_class);
   aux2
     (x:Seq.lseq U64.t (A.length md){slab_vprop_aux2 size_class x})
     (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
     (Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class))))
       (Seq.length (SeqUtils.init_u32_refined (UInt32.v (nb_slots size_class)))))
     (Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class))))
       (U32.v (nb_slots size_class)))
#pop-options

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  : Lemma
  (t_of (slab_vprop size_class arr md)
  ==
    dtuple2
      (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
      (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
    &
    Seq.lseq U8.t (U32.v page_size - US.v (rounding size_class))
  )
  =
  slab_vprop_lemma_aux size_class arr md;
  assert(A.length (A.split_r arr (rounding size_class)) == U32.v page_size - US.v (rounding size_class));
  assert(t_of (A.varray (A.split_r arr (rounding size_class))) == Seq.lseq U8.t (U32.v page_size - US.v (rounding size_class)))
#pop-options

//[@@ __steel_reduce__]
//let v_slab_vprop_slabs (#p:vprop)
//  (size_class: sc)
//  (arr: array U8.t{A.length arr = U32.v page_size})
//  (md: slab_metadata)
//  (h:rmem p{FStar.Tactics.with_tactic selector_tactic
//    (can_be_split p (slab_vprop size_class arr md) /\ True)})
//  : GTot (
//      Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class))
//  )
//  =
//  let blob
//    : t_of (slab_vprop size_class arr md)
//    = h (slab_vprop size_class arr md) in
//  slab_vprop_aux_lemma size_class (A.split_l arr (rounding size_class)) (dfst (fst blob));
//  dsnd (fst blob)

//#push-options "--print_implicits"

noextract
let a2bv = Bitmap4.array_to_bv2 #4
//noextract
//let f = Bitmap5.f #4

open FStar.Mul
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
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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

#push-options "--fuel 1 --ifuel 1"
let starseq_upd_aux_lemma3
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
#pop-options

#push-options "--fuel 1 --ifuel 1"
let get_slot_as_returned_value
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
  (ensures fun h0 r h1 ->
    A.length r == U32.v size_class /\
    same_base_array r arr /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) >= 0 /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) < U32.v page_size /\
    (A.offset (A.ptr_of r) - A.offset (A.ptr_of arr)) % (U32.v size_class) == 0
  )
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
#pop-options

noextract inline_for_extraction
let allocate_slot_aux
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
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
  (ensures fun h0 r h1 ->
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
    A.length r == U32.v size_class /\
    same_base_array r arr /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) >= 0 /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) < U32.v page_size /\
    (A.offset (A.ptr_of r) - A.offset (A.ptr_of arr)) % (U32.v size_class) == 0
  )
    //blob2 == Seq.upd blob1 (U32.v pos) None /\
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
  let i2 = US.uint32_to_sizet i in
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

#push-options "--fuel 1 --ifuel 1"
let elim_slab_vprop_aux
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    slab_vprop size_class arr md
  )) m)
  (ensures SM.interp (hp_of (
    vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
    `star`
    A.varray (A.split_r arr (rounding size_class))
  )) m /\
  sel_of (
    vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
    `star`
    A.varray (A.split_r arr (rounding size_class))
  ) m
  ==
  sel_of (slab_vprop size_class arr md) m)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let intro_slab_vprop (#opened:_)
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  : SteelGhost unit opened
  (
    slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq) `star`
    (A.varray md `star`
    A.varray (A.split_r arr (rounding size_class)))
  )
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
    dsnd (fst blob1) == h0 (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq)) /\
    snd blob1 == A.asel (A.split_r arr (rounding size_class)) h0
  )
  =
  intro_vrefinedep
    (A.varray md)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
    (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq));
  change_equal_slprop
    (vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
    `star`
    A.varray (A.split_r arr (rounding size_class)))
    (slab_vprop size_class arr md)
#pop-options

// without compat_pre_typed_indexed_effects
// this fails in lax mode
#push-options "--fuel 2 --ifuel 2 --z3rlimit 30 --compat_pre_typed_indexed_effects"
let elim_slab_vprop (#opened:_)
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : SteelGhost (G.erased (Seq.lseq U64.t 4)) opened
  (slab_vprop size_class arr md)
  (fun r ->
    slab_vprop_aux size_class (A.split_l arr (rounding size_class)) r `star`
    (A.varray md `star`
    A.varray (A.split_r arr (rounding size_class)))
  )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let x0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    G.reveal r == x0 /\
    G.reveal r == A.asel md h1 /\
    dsnd (fst blob0) == h1 (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) r) /\
    slab_vprop_aux2 size_class (G.reveal r) /\
    snd blob0 == A.asel (A.split_r arr (rounding size_class)) h1
  )
  =
  change_slprop_rel
    (slab_vprop size_class arr md)
    (vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
    `star`
    A.varray (A.split_r arr (rounding size_class)))
    (fun x y -> x == y)
    (fun m -> elim_slab_vprop_aux size_class md arr m);
  let md_as_seq
    : G.erased (t_of (vrefine
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
    ))
    = elim_vrefinedep
      (A.varray md)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
      (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
  in
  let md_as_seq2
    : G.erased (Seq.lseq U64.t 4)
    = G.hide (G.reveal md_as_seq <: Seq.lseq U64.t 4) in
  change_equal_slprop
    (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq))
    (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq2));
  md_as_seq2
#pop-options

#push-options "--z3rlimit 150"
let bound2_inv
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (requires (
    let bm = Bitmap4.array_to_bv2 md_as_seq in
    let idx = Bitmap4.f #4 (U32.v pos) in
    slab_vprop_aux2 size_class md_as_seq /\
    Seq.index bm idx = false
  ))
  (ensures slab_vprop_aux2 size_class (Bitmap4.set md_as_seq pos))
  =
  let bm = Bitmap4.array_to_bv2 md_as_seq in
  let nb_slots_sc = nb_slots size_class in
  let bound2 = bound2_gen nb_slots_sc (G.hide size_class) in
  assert (zf_b (Seq.slice bm 0 (64 - U32.v bound2)));
  let md_as_seq' = Bitmap4.set md_as_seq pos in
  let bm' = Bitmap4.array_to_bv2 md_as_seq' in
  let nb_slots_sc_rem = U32.rem nb_slots_sc 64ul in
  if (U32.v size_class <= 64)
  then (
    assert (size_class = 16ul \/ size_class = 32ul \/ size_class = 64ul);
    assert (U32.v nb_slots_sc_rem = 0);
    Seq.lemma_empty (Seq.slice bm' 0 (64 - U32.v bound2))
  ) else (
    assert (U32.v size_class > 64);
    assert (U32.v nb_slots_sc < 64);
    assert (nb_slots_sc_rem = nb_slots_sc);
    let idx = Bitmap4.f #4 (U32.v pos) in
    Bitmap4.set_lemma2 md_as_seq pos;
    Seq.lemma_eq_intro
      (Seq.slice bm 0 (64 - U32.v bound2))
      (Seq.slice bm' 0 (64 - U32.v bound2))
  )
#pop-options

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
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
  (ensures fun h0 r h1 ->
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let blob1 : t_of (slab_vprop size_class arr md)
      = h1 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    not (is_empty size_class v1) /\
    A.length r == U32.v size_class /\
    same_base_array r arr /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) >= 0 /\
    A.offset (A.ptr_of r) - A.offset (A.ptr_of arr) < U32.v page_size /\
    (A.offset (A.ptr_of r) - A.offset (A.ptr_of arr)) % (U32.v size_class) == 0
  )
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
    (A.split_l arr (rounding size_class))
    pos in
  set_lemma_nonempty size_class (G.reveal md_as_seq) (Bitmap4.set (G.reveal md_as_seq) pos) pos;
  bound2_inv size_class (G.reveal md_as_seq) pos;
  let md_as_seq' : G.erased (Seq.lseq U64.t 4)
    = G.hide (Bitmap4.set md_as_seq pos) in
  change_equal_slprop
    (slab_vprop_aux
      size_class (A.split_l arr (rounding size_class))
      (Bitmap4.set md_as_seq pos))
    (slab_vprop_aux
      size_class (A.split_l arr (rounding size_class))
      md_as_seq');
  intro_slab_vprop size_class md md_as_seq' arr;
  return r
#pop-options
