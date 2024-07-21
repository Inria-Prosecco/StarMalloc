module SlotsAlloc

module FU = FStar.UInt
module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
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

open SlotsCommon

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

let apply_starseq_upd (#opened:_)
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq1: G.erased (Seq.lseq U64.t 4))
  (md_as_seq2: G.erased (Seq.lseq U64.t 4))
  //(md_q: G.erased (Seq.lseq U64.t 4))
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
let get_slot_as_returned_value
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  //(md_q: G.erased (Seq.lseq U64.t 4))
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
  //(md_q: G.erased (Seq.lseq U64.t 4))
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
  assert_norm (4 < FU.max_int U32.n);
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

open FStar.Mul
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
  (bitmap_q: slab_metadata)
  (i: U32.t)
  : Steel U32.t
  (A.varray bitmap `star` A.varray bitmap_q)
  (fun _ -> A.varray bitmap `star` A.varray bitmap_q)
  (requires fun h0 ->
    U32.v i < U32.v (nb_slots size_class) / 64 /\
    (let x = Seq.index (A.asel bitmap h0) (U32.v i) in
    let x_q = Seq.index (A.asel bitmap_q h0) (U32.v i) in
    (U64.logor x x_q) <> max64))
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    A.asel bitmap_q h1 == A.asel bitmap_q h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let bm_q = Bitmap4.array_to_bv2 (A.asel bitmap_q h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    //True)
    Seq.index bm idx = false /\
    Seq.index bm_q idx = false)
  )
  =
  let h0 = get () in
  assert (U32.v i <= 3);
  assert_norm (3 <= FU.max_int U32.n);
  let i2 = US.uint32_to_sizet i in
  let x = A.index bitmap i2 in
  let x_q = A.index bitmap i2 in
  let x_xor = U64.logor x x_q in
  assume (x_xor <> max64);
  max64_lemma x_xor;
  //TODO: FIXME, should be benign
  admit ();
  let r = ffs64 x_xor (G.hide 64ul) in
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
  (bitmap_q: slab_metadata)
  : Steel U32.t
  (A.varray bitmap `star` A.varray bitmap_q)
  (fun _ -> A.varray bitmap `star` A.varray bitmap_q)
  (requires fun h0 ->
    let x = Seq.index (A.asel bitmap h0) 0 in
    let x_q = Seq.index (A.asel bitmap_q h0) 0 in
    let x_xor = U64.logor x x_q in
    let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let bm_q = Bitmap4.array_to_bv2 (A.asel bitmap_q h0) in
    let bm_xor = Seq2.map_seq2 (fun x y -> x || y) bm bm_q in
    let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
    Seq2.map_seq2_len (fun x y -> x || y) bm bm_q;
    zf_b (Seq.slice bm_xor 0 (64 - U32.v bound2)) /\
    x_xor <> full_n bound2)
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    A.asel bitmap_q h1 == A.asel bitmap_q h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let bm_q = Bitmap4.array_to_bv2 (A.asel bitmap_q h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false /\
    Seq.index bm_q idx = false)
  )
  =
  let h0 = get () in
  let x = A.index bitmap 0sz in
  let x_q = A.index bitmap 0sz in
  let x_xor = U64.logor x x_q in
  let bound2 = G.hide (bound2_gen (nb_slots size_class) (G.hide size_class)) in
  assume (x_xor <> full_n bound2);
  let bm = G.hide (Bitmap4.array_to_bv2 (A.asel bitmap h0)) in
  array_to_bv_slice (A.asel bitmap h0) 0;
  assert (FU.to_vec (U64.v x) == Seq.slice bm 0 64);
  Seq.slice_slice bm 0 64 0 (64 - U32.v bound2);
  //TODO: FIXME, should be benign
  admit ();
  assert (zf_b (Seq.slice (FU.to_vec #64 (U64.v x)) 0 (64 - U32.v bound2)));
  full_n_lemma x bound2;
  assert (U32.lte bound2 (nb_slots size_class));
  let r = ffs64 x_xor bound2 in
  assert (x == Seq.index (A.asel bitmap h0) 0);
  assert (FU.nth (U64.v x) (U64.n - 1 - U32.v r) = false);
  assert (Seq.index (Seq.slice bm 0 64) (U64.n - 1 - U32.v r) = false);
  Seq.lemma_index_slice bm 0 64 (U32.v r);
  assert (Seq.index bm (U64.n - 1 - U32.v r) = false);
  f_lemma #4 0 (U32.v r) (U32.v r) (U64.n - 1 - U32.v r);
  r
#pop-options

let get_free_slot (size_class: sc)
  (bitmap: slab_metadata)
  (bitmap_q: slab_metadata)
  : Steel U32.t
  (A.varray bitmap `star` A.varray bitmap_q)
  (fun _ -> A.varray bitmap `star` A.varray bitmap_q)
  (requires fun h0 ->
    let s = A.asel bitmap h0 in
    let s_q = A.asel bitmap_q h0 in
    let s_or = seq_u64_or s s_q in
    let bm = Bitmap4.array_to_bv2 #4 s_or in
    let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
    zf_b (Seq.slice bm 0 (64 - U32.v bound2)) /\
    has_free_slot size_class s_or
  )
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let bm_q = Bitmap4.array_to_bv2 (A.asel bitmap_q h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false /\
    Seq.index bm idx = false)
  )
  =
  //TODO: FIXME, should be benign
  admit ();
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
        get_free_slot_aux size_class bitmap bitmap_q 3ul
      ) else (
        get_free_slot_aux size_class bitmap bitmap_q 2ul
      )
    ) else (
      get_free_slot_aux size_class bitmap bitmap_q 1ul
    )
  ) else (
    get_free_slot_aux2 size_class bitmap bitmap_q
  )

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

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let allocate_slot size_class arr md md_q
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  let mds : G.erased (Seq.lseq U64.t 4 & Seq.lseq U64.t 4)
    = elim_slab_vprop size_class arr md md_q in
  let md_or : G.erased (Seq.lseq U64.t 4)
    = G.hide (seq_u64_or (fst mds) (snd mds)) in
  assume (has_free_slot size_class (G.reveal md_or));
  let bm = G.hide (Bitmap4.array_to_bv2 #4 md_or) in
  let bound2 = G.hide (bound2_gen (nb_slots size_class) (G.hide size_class)) in
  assume (zf_b (Seq.slice bm 0 (64 - U32.v bound2)));
  let pos = get_free_slot size_class md md_q in
  let r = allocate_slot_aux
    size_class
    md
    (G.hide (fst (G.reveal mds)))
    //(G.hide (snd (G.reveal mds)))
    (A.split_l arr (rounding size_class))
    pos in
  set_lemma_nonempty size_class (fst mds) (Bitmap4.set (fst mds) pos) pos;
  bound2_inv size_class (fst mds) pos;
  let md_as_seq' : G.erased (Seq.lseq U64.t 4)
    = G.hide (Bitmap4.set (fst mds) pos) in
  change_equal_slprop
    (slab_vprop_aux
      size_class (A.split_l arr (rounding size_class))
      (Bitmap4.set (fst mds) pos))
    (slab_vprop_aux
      size_class (A.split_l arr (rounding size_class))
      md_as_seq');
  //let md_q = gget (A.varray md_q) in
  //TODO: admit roughly corresponding to the assume, should be benign
  //assume (slab_vprop_aux2 size_class md_q);
  admit ();
  intro_slab_vprop size_class arr md md_q md_as_seq';
  return r
#pop-options
