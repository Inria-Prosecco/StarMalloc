module Slots2

module FU = FStar.UInt
module FI = FStar.Int
module STU = SizeTUtils
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

let offset_diff (#a: Type)
  (ptr1: A.ptr a)
  (ptr2: A.ptr a{A.base ptr1 == A.base ptr2})
  : GTot int
  =
  A.offset ptr1 - A.offset ptr2

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
//TODO: check for spec
let deallocate_slot_aux0
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  (diff: U32.t)
  : Pure bool
  (requires (
    let diff2 = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array arr ptr /\
    0 <= diff2 /\
    diff2 < U32.v page_size /\
    U32.v diff == diff2
  ))
  (ensures
    fun r ->
      let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
      r = (diff % (U32.v size_class) = 0))
  =
  let rem = U32.rem diff size_class in
  assert (U32.v rem = U32.v diff % U32.v size_class);
  let b = rem = 0ul in
  b

let deallocate_slot_aux1
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  (diff: U32.t)
  : Pure U32.t
  (requires (
    let diff2 = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array arr ptr /\
    0 <= diff2 /\
    diff2 < U32.v page_size /\
    diff2 % (U32.v size_class) = 0 /\
    U32.v diff == diff2
  ))
  (ensures
    fun r ->
      let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
      U32.v r = diff / (U32.v size_class))
  =
  let div = U32.div diff size_class in
  div

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

let deallocate_slot_aux2
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  : Lemma
  (requires (
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array arr ptr /\
    0 <= diff /\
    diff <= U32.v page_size /\
    diff % (U32.v size_class) == 0
  ))
  (ensures (
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    let pos = diff / U32.v size_class in
    pos < U32.v (nb_slots size_class) /\
    ptr == slot_array size_class arr (U32.uint_to_t pos)
  ))
  =
  let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
  assume (US.fits_u32);
  let pos = diff / (U32.v size_class) in
  let rem = diff % (U32.v size_class) in
  assert (rem = 0);
  assert (diff = pos * (U32.v size_class));
  assume (pos < U32.v (nb_slots size_class));
  slot_array_offset_lemma size_class arr (U32.uint_to_t pos);
  let ptr' = slot_array size_class arr (U32.uint_to_t pos) in
  assert (A.offset (A.ptr_of ptr) == A.offset (A.ptr_of ptr'));
  A.ptr_base_offset_inj (A.ptr_of ptr) (A.ptr_of ptr');
  assert (A.ptr_of ptr == A.ptr_of ptr');
  // CAUTION: discuss with Aymeric, metaproperty
  // actually, will be removed (expected_length as ghost)
  assume (A.length ptr == U32.v size_class);
  assert (ptr == ptr')

let temp (b: bool)
  : SteelT unit
  (if b then emp else emp)
  (fun _ -> if b then emp else emp)
  =
  return ()

//TODO: check for spec
//CAUTION

#push-options "--z3rlimit 75"
let deallocate_slot'
  (size_class: sc)
  (md: slab_metadata)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = 4096})
  (ptr: array U8.t)
  : Steel bool
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
  (fun b ->
    A.varray md `star`
    (if b then emp else A.varray ptr) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    same_base_array ptr arr /\
    0 <= diff /\
    diff < U32.v page_size /\
    A.asel md h0 == G.reveal md_as_seq
  )
  (ensures fun _ _ _ -> True)
  =
  //TODO: ptr of length 0 as region start for ptrdiff
  rewrite_slprop
    (starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))))
    (A.varray arr)
    (fun _ -> admit ());
  let diff = ptrdiff ptr arr in
  //TODO: ptr of length 0 as region start for ptrdiff
  rewrite_slprop
    (A.varray arr)
    (starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq arr)
      (slab_vprop_aux_f_lemma size_class md_as_seq arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))))
    (fun _ -> admit ());
  assert (UP.v diff == A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr));
  let diff_sz = z_to_sz diff in
  assume (US.fits_u32);
  assert_norm (4 < FI.max_int 16);
  let diff_u32 = sz_to_u32 diff_sz in
  let b = deallocate_slot_aux0 size_class arr ptr diff_u32 in
  if b then (
    deallocate_slot_aux2 size_class arr ptr;
    let pos = deallocate_slot_aux1 size_class arr ptr diff_u32 in
    let b = Bitmap5.bm_get #4 md pos in
    if b then (
      // TODO: like Slots@returned_value admitted lemma
      //rewrite_slprop
      //  (A.varray ptr)
      //  ((slab_vprop_aux_f size_class md_as_seq arr)
      //    (Seq.index
      //      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
      //      (U32.v pos)))
      //  (fun _ -> admit ());
      // TODO: starseq upd reverse lemma
      sladmit ();
      deallocate_slot_aux size_class md md_as_seq arr pos;
      return true
    ) else (
      return false
    )
  ) else (
    return false
 )
#pop-options

#push-options "--compat_pre_typed_indexed_effects"
#push-options "--z3rlimit 50"
let deallocate_slot
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (ptr: array U8.t)
  : Steel bool
  //: Steel bool
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
    True)
    //not (is_empty size_class v0))
  (ensures fun _ _ _ -> True)
  =
  assert (t_of (A.varray md) == Seq.lseq U64.t 4);
  let md_as_seq : G.erased (t_of (A.varray md)) = elim_vdep
    (A.varray md)
    (fun (x: Seq.lseq U64.t 4) -> slab_vprop_aux size_class arr x)
  in
  let md_as_seq2 : G.erased (Seq.lseq U64.t 4) = G.hide ((G.reveal md_as_seq) <: Seq.lseq U64.t 4) in
  assert (G.reveal md_as_seq == G.reveal md_as_seq2);
  change_slprop_rel
    (slab_vprop_aux size_class arr (G.reveal md_as_seq))
    (slab_vprop_aux size_class arr (G.reveal md_as_seq2))
    (fun x y -> x == y)
    (fun _ -> ());
  let r = deallocate_slot' size_class md md_as_seq2 arr ptr in
  sladmit ();
  return r
#pop-options

(*)
- [ok] ptrdiff
- [ok] uintptr_t
- [ok-ish] deallocate_slot_aux
  - bv lemma
  - starseq lemma
- [ok-ish] deallocate_slot

sides:
- remove src/Slots remaining admit with src/Slots2 lemma
  - + c2 lemma on selectors?
- remove Slots2 admits + aux lemmas (some work ahead!)
  [ok] - remove dubious coercions
- merge extraction to main when extractable

roadmap:
[ok] - add has_free_slot & co extractable versions (with proper spec ofc)
[~ok] - add full_slabs list: src/Slabs, src/SizeClass
  [ok] - patch allocate_slab_aux_1
  [sk] - patch allocate_slab_aux_2 (later)
  [~ok] - allocate_slot_refined (src/Slabs):
    [ok] - improve spec
    postcond is is_partial \/ is_full (as nb_slots size_class > 1, exclusive for now)
    [ok-ish] - remove admit
    [sk] - prove Utils2 lemma

[!] - flattening lemma sketch (large ghost seq will be used to keep information for flattened state, hopefully no issue with starseq)
[!] - doubly-linked lists with additional predicate over arrayrefs...
- test Aymeric F* branch
- use within_bounds from src/Sizeclass2 to get a deallocate_sizeclass function
  => within_bounds should be a Steel function with live arrays
- free: expected_size requirement: refine starseq...
- ptrdiff: array requirement: add a ghost_split on region_start everywhere
- deallocation
- initialization to Steel
- sizeclass selection
- mmap flags check
