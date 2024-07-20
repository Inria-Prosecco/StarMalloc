module SlotsCommon

module FU = FStar.UInt
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module G = FStar.Ghost

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module SM = Steel.Memory

open Constants
open Utils2

#push-options "--fuel 0 --ifuel 0"

let seq_u64_or
  (s1 s2: Seq.lseq U64.t 4)
  : Seq.lseq U64.t 4
  =
  Seq2.map_seq2_len (fun x y -> U64.logor x y) s1 s2;
  Seq2.map_seq2 (fun x y -> U64.logor x y) s1 s2

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
  assert_norm (U32.v shift <= FU.max_int U32.n);
  assert (U32.v shift <= FU.max_int U32.n);
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

open SteelOptUtils
let slab_vprop_aux_f
  (size_class: sc)
  (md: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (i: U32.t{U32.v i < U32.v (nb_slots size_class)})
  : vprop
  =
  let vp = slot_vprop size_class arr i in
  slot_vprop_lemma size_class arr i;
  c2
    #(Seq.lseq U8.t (U32.v size_class))
    (not (Bitmap4.get md i))
    vp

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_aux_f_lemma
  (size_class: sc)
  (md: Seq.lseq U64.t 4)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  : (i: U32.t{U32.v i < U32.v (nb_slots size_class)}) ->
    Lemma (
      t_of (slab_vprop_aux_f size_class md arr i)
      ==
      option (Seq.lseq U8.t (U32.v size_class)))
  =
  fun i ->
  let vp = slot_vprop size_class arr i in
  slot_vprop_lemma size_class arr i;
  c2_t
    #(Seq.lseq U8.t (U32.v size_class))
    (not (Bitmap4.get md i))
    vp
#pop-options

open SteelStarSeqUtils
let slab_vprop_aux
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (md: Seq.lseq U64.t 4)
  : vprop
  =
  let nb_slots_as_nat = U32.v (nb_slots size_class) in
  let incr_seq = SeqUtils.init_u32_refined nb_slots_as_nat in
  starseq
    #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(option (Seq.lseq U8.t (U32.v size_class)))
    (slab_vprop_aux_f size_class md arr)
    (slab_vprop_aux_f_lemma size_class md arr)
    incr_seq

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_aux_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (md: Seq.lseq U64.t 4)
  : Lemma
  (t_of (slab_vprop_aux size_class arr md)
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
  (md md_q: slab_metadata)
  : vprop
  =
  vrefinedep
    (A.varray md `star` A.varray md_q)
    (fun (mds: _ & Seq.lseq U64.t 4) -> //Seq.lseq U64.t 4 & Seq.lseq U64.t 4) ->
      slab_vprop_aux2 size_class (fst mds) /\
      slab_vprop_aux2 size_class (snd mds))
    (fun (mds: _ & Seq.lseq U64.t 4) -> //Seq.lseq U64.t 4 & Seq.lseq U64.t 4) ->
      slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst mds))
  `star`
  A.varray (A.split_r arr (rounding size_class))
#pop-options

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_lemma_aux
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md md_q: slab_metadata)
  : Lemma
  (t_of (vrefinedep
    (A.varray md `star` A.varray md_q)
    (fun (mds: _ & Seq.lseq U64.t 4) ->
      slab_vprop_aux2 size_class (fst mds) /\
      slab_vprop_aux2 size_class (snd mds))
    (fun (mds: _ & Seq.lseq U64.t 4) ->
      slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst mds))
  )
  ==
    dtuple2
      (x: (Seq.lseq U64.t 4 & Seq.lseq U64.t 4){
        slab_vprop_aux2 size_class (fst x) /\
        slab_vprop_aux2 size_class (snd x)
      })
      (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
  )
  =
  admit ()
  //let aux (n1 n2:nat) (p:Seq.lseq U64.t n1 -> prop) : Lemma
  //    (requires n1 == n2)
  //    (ensures (x:Seq.lseq U64.t n1{p x}) == (x:Seq.lseq U64.t n2{p x}))
  //  = () in
  //  let aux2 (a a':Type) (b c:Type) : Lemma
  //    (requires a == a' /\ b == c)
  //    (ensures dtuple2 a (fun _ -> b) == dtuple2 a' (fun _ -> c))
  //  = () in
  //  // The SMT solver needs some help to prove type equality, with rewritings deep in the terms.
  //  // In particular, it does not seem to be able to apply the rewritings for aux and aux2 without
  //  // explicit calls to the lemmas when they occur under dtuple2
  //  assert_norm (
  //    t_of (vrefinedep
  //      (A.varray md `star` A.varray md_q)
  //      (fun (mds: _ & Seq.lseq U64.t 4) ->
  //        slab_vprop_aux2 size_class (fst mds) /\
  //        slab_vprop_aux2 size_class (snd mds))
  //      (fun (mds: _ & Seq.lseq U64.t 4) ->
  //        slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst mds))
  //    )
  //    ==
  //    dtuple2
  //      (x: (Seq.lseq U64.t (A.length md) & Seq.lseq U64.t (A.length md_q)){
  //        slab_vprop_aux2 size_class (fst x) /\
  //        slab_vprop_aux2 size_class (snd x)
  //      })
  //      (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class))))
  //        (Seq.length (SeqUtils.init_u32_refined (UInt32.v (nb_slots size_class)))))
  //  );
  // aux (A.length md) 4 (slab_vprop_aux2 size_class);
  // aux2
  //   (x:Seq.lseq U64.t (A.length md){slab_vprop_aux2 size_class x})
  //   (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
  //   (Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class))))
  //     (Seq.length (SeqUtils.init_u32_refined (UInt32.v (nb_slots size_class)))))
  //   (Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class))))
  //     (U32.v (nb_slots size_class)))

#push-options "--fuel 1 --ifuel 1"
let slab_vprop_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md md_q: slab_metadata)
  : Lemma
  (t_of (slab_vprop size_class arr md md_q)
  ==
    dtuple2
      (x: (Seq.lseq U64.t 4 & Seq.lseq U64.t 4){
        slab_vprop_aux2 size_class (fst x) /\
        slab_vprop_aux2 size_class (snd x)
      })
      (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
    &
    Seq.lseq U8.t (U32.v page_size - US.v (rounding size_class))
  )
  =
  slab_vprop_lemma_aux size_class arr md md_q;
  assert(A.length (A.split_r arr (rounding size_class)) == U32.v page_size - US.v (rounding size_class));
  assert(t_of (A.varray (A.split_r arr (rounding size_class))) == Seq.lseq U8.t (U32.v page_size - US.v (rounding size_class)))
#pop-options

#push-options "--fuel 2 --ifuel 2"
let elim_slab_vprop_aux
  (size_class: sc)
  (md md_q: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    slab_vprop size_class arr md md_q
  )) m)
  (ensures SM.interp (hp_of (
    vrefinedep
      (A.varray md `star` A.varray md_q)
      (fun (mds: _ & Seq.lseq U64.t 4) -> //Seq.lseq U64.t 4 & Seq.lseq U64.t 4) ->
        slab_vprop_aux2 size_class (fst mds) /\
        slab_vprop_aux2 size_class (snd mds))
      (fun (mds: _ & Seq.lseq U64.t 4) -> //Seq.lseq U64.t 4 & Seq.lseq U64.t 4) ->
        slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst mds))
    `star`
    A.varray (A.split_r arr (rounding size_class))
  )) m /\
  sel_of (
    vrefinedep
      (A.varray md `star` A.varray md_q)
      (fun (mds: _ & Seq.lseq U64.t 4) -> //Seq.lseq U64.t 4 & Seq.lseq U64.t 4) ->
        slab_vprop_aux2 size_class (fst mds) /\
        slab_vprop_aux2 size_class (snd mds))
      (fun (mds: _ & Seq.lseq U64.t 4) -> //Seq.lseq U64.t 4 & Seq.lseq U64.t 4) ->
        slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst mds))
    `star`
    A.varray (A.split_r arr (rounding size_class))
  ) m
  ==
  sel_of (slab_vprop size_class arr md md_q) m)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let intro_slab_vprop (#opened:_)
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md md_q: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  : SteelGhost unit opened
  (
    slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq) `star`
    (A.varray md `star`
    A.varray md_q `star`
    A.varray (A.split_r arr (rounding size_class)))
  )
  (fun _ -> slab_vprop size_class arr md md_q)
  (requires fun h0 ->
    G.reveal md_as_seq == A.asel md h0 /\
    slab_vprop_aux2 size_class md_as_seq /\
    slab_vprop_aux2 size_class (A.asel md_q h0)
  )
  (ensures fun h0 _ h1 ->
    let blob1 : t_of (slab_vprop size_class arr md md_q)
      = h1 (slab_vprop size_class arr md md_q) in
    let x1 : _ & Seq.lseq U64.t 4 = dfst (fst blob1) in
    fst x1 == A.asel md h0 /\
    snd x1 == A.asel md_q h0 /\
    dsnd (fst blob1) == h0 (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq)) /\
    snd blob1 == A.asel (A.split_r arr (rounding size_class)) h0
  )
  =
  intro_vrefinedep
    (A.varray md `star` A.varray md_q)
    (fun (mds: _ & Seq.lseq U64.t 4) ->
      slab_vprop_aux2 size_class (fst mds) /\
      slab_vprop_aux2 size_class (snd mds))
    (fun (mds: _ & Seq.lseq U64.t 4) ->
      slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst mds))
    (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq));
  admit ();
  change_equal_slprop
    (vrefinedep
      (A.varray md `star` A.varray md_q)
      (fun (mds: _ & Seq.lseq U64.t 4) ->
        slab_vprop_aux2 size_class (fst mds) /\
        slab_vprop_aux2 size_class (snd mds))
      (fun (mds: _ & Seq.lseq U64.t 4) ->
        slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst mds))
    `star`
    A.varray (A.split_r arr (rounding size_class)))
    (slab_vprop size_class arr md md_q)
#pop-options

// without compat_pre_typed_indexed_effects
// this fails in lax mode
#push-options "--fuel 2 --ifuel 2 --z3rlimit 30 --compat_pre_typed_indexed_effects"
let elim_slab_vprop (#opened:_)
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md md_q: slab_metadata)
  : SteelGhost (G.erased (Seq.lseq U64.t 4 & Seq.lseq U64.t 4)) opened
  (slab_vprop size_class arr md md_q)
  (fun r ->
    slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst r) `star`
    (A.varray md `star`
    A.varray md_q `star`
    A.varray (A.split_r arr (rounding size_class)))
  )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
    let blob0 : t_of (slab_vprop size_class arr md md_q)
      = h0 (slab_vprop size_class arr md md_q) in
    let x0 : _ & Seq.lseq U64.t 4 = dfst (fst blob0) in
    fst (G.reveal r) == fst x0 /\
    fst (G.reveal r) == A.asel md h1 /\
    snd (G.reveal r) == A.asel md_q h1 /\
    dsnd (fst blob0) == h1 (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (fst r)) /\
    slab_vprop_aux2 size_class (G.reveal (fst r)) /\
    slab_vprop_aux2 size_class (G.reveal (snd r)) /\
    snd blob0 == A.asel (A.split_r arr (rounding size_class)) h1
  )
  =
  sladmit ()
  //change_slprop_rel
  //  (slab_vprop size_class arr md)
  //  (vrefinedep
  //    (A.varray md)
  //    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
  //    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
  //  `star`
  //  A.varray (A.split_r arr (rounding size_class)))
  //  (fun x y -> x == y)
  //  (fun m -> elim_slab_vprop_aux size_class md arr m);
  //let md_as_seq
  //  : G.erased (t_of (vrefine
  //    (A.varray md)
  //    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
  //  ))
  //  = elim_vrefinedep
  //    (A.varray md)
  //    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux2 size_class md_as_seq)
  //    (fun (md_as_seq: Seq.lseq U64.t 4) -> slab_vprop_aux size_class (A.split_l arr (rounding size_class)) md_as_seq)
  //in
  //let md_as_seq2
  //  : G.erased (Seq.lseq U64.t 4)
  //  = G.hide (G.reveal md_as_seq <: Seq.lseq U64.t 4) in
  //change_equal_slprop
  //  (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq))
  //  (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq2));
  //md_as_seq2
#pop-options


val empty_md_is_properly_zeroed
  (size_class: sc)
  : Lemma
  (slab_vprop_aux2 size_class (Seq.create 4 0UL))


noextract
let a2bv = Bitmap4.array_to_bv2 #4

open Utils2

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



#push-options "--fuel 1 --ifuel 1"
let starseq_upd_aux_lemma3
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  //(md_q: G.erased (Seq.lseq U64.t 4))
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

open FStar.Mul
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
    bm2 == Seq.upd bm1 (Bitmap5.f #4 (U32.v pos)) (not v) /\
    True//TODO: ?
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
  //(md_q: G.erased (Seq.lseq U64.t 4))
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
  //(md_q: G.erased (Seq.lseq U64.t 4))
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
