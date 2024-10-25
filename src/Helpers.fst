module Helpers

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
open SteelOptUtils
open SteelStarSeqUtils
open FStar.Mul
open SlotsAlloc

open FStar.Mul

#push-options "--fuel 0 --ifuel 0"

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let slot_array (#a: Type)
  (size: U32.t)
  (max: U32.t)
  (arr: array a)
  (pos: U32.t{U32.v pos < U32.v max})
  : Pure (array a)
  (requires
    (U32.v max) * (U32.v size) <= FI.max_int U32.n /\
    U32.v pos < U32.v max /\
    A.length arr = U32.v (U32.mul max size) /\
    U32.v size > 0)
  (ensures fun r ->
    A.length r == U32.v size /\
    same_base_array r arr)
  =
  let ptr = A.ptr_of arr in
  let shift = U32.mul pos size in
  assert (U32.v shift <= U32.v (U32.mul max size));
  //assert_norm (U32.v shift <= FI.max_int U32.n);
  assert (U32.v shift <= FI.max_int U32.n);
  assert (U32.v shift <= (U32.v max - 1) * (U32.v size));
  assert (U32.v shift + U32.v size <= A.length arr);
  let shift_sz = US.uint32_to_sizet shift in
  assert (US.v shift_sz < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift_sz in
  (| ptr_shifted, G.hide (U32.v size) |)
#pop-options

let slot_vprop (#a: Type)
  (size: U32.t{U32.v size > 0})
  (max: U32.t{U32.v max * U32.v size <= FI.max_int U32.n})
  (arr: array a{A.length arr = U32.v (U32.mul max size)})
  (pos: U32.t{U32.v pos < U32.v max})
  =
  A.varray (slot_array size max arr pos)

#push-options "--fuel 1 --ifuel 1"
let slot_vprop_lemma (#a: Type)
  (size: U32.t{U32.v size > 0})
  (max: U32.t{U32.v max * U32.v size <= FI.max_int U32.n})
  (arr: array a{A.length arr = U32.v (U32.mul max size)})
  (pos: U32.t{U32.v pos < U32.v max})
  : Lemma
  (t_of (slot_vprop size max arr pos) == Seq.lseq a (U32.v size))
  =
  ()
#pop-options

let starseq_to_singleton_s (#opened:_) (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a{Seq.length s > 0})
  : SteelGhost unit opened
  (starseq #a #b f f_lemma s)
  (fun _ ->
    f (Seq.index s 0)
  )
  (requires fun _ -> Seq.length s == 1)
  (ensures fun _ _ _ -> True)
  =
  starseq_unpack_s
    #_ #a #b
    f f_lemma s 0;
  starseq_empty_equiv_emp #a #b f f_lemma (Seq.slice s 0 0);
  assert (hp_of (starseq #a #b f f_lemma (Seq.slice s 0 0)) == hp_of emp);
  starseq_empty_equiv_emp #a #b f f_lemma (Seq.slice s 1 (Seq.length s));
  assert (hp_of (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s))) == hp_of emp);
  rewrite_slprop
    (starseq #a #b f f_lemma (Seq.slice s 0 0)) emp
    (fun _ -> ());
  rewrite_slprop
    (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s))) emp
    (fun _ -> ())

let starseq_from_singleton_s (#opened:_) (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a{Seq.length s > 0})
  : SteelGhost unit opened
  (f (Seq.index s 0))
  (fun _ ->
    starseq #a #b f f_lemma s
  )
  (requires fun _ -> Seq.length s == 1)
  (ensures fun _ _ _ -> True)
  =
  starseq_empty_equiv_emp #a #b f f_lemma (Seq.slice s 0 0);
  assert (hp_of (starseq #a #b f f_lemma (Seq.slice s 0 0)) == hp_of emp);
  starseq_empty_equiv_emp #a #b f f_lemma (Seq.slice s 1 (Seq.length s));
  assert (hp_of (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s))) == hp_of emp);
  rewrite_slprop
    emp (starseq #a #b f f_lemma (Seq.slice s 0 0))
    (fun _ -> ());
  rewrite_slprop
    emp (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s)))
    (fun _ -> ());
  starseq_pack_s
    #_ #a #b
    f f_lemma s 0

let starseq_add_singleton_s (#opened:_) (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{Seq.length s = n + 1})
  : SteelGhost unit opened
  (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
  f (Seq.index s n))
  (fun _ ->
    starseq #a #b f f_lemma s)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  starseq_empty_equiv_emp #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s));
  assert (hp_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) == hp_of emp);
  rewrite_slprop
    emp
    (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))
    (fun _ -> ());
  starseq_pack_s
    #_ #a #b
    f f_lemma s n

let starseq_remove_singleton_s (#opened:_) (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{Seq.length s = n + 1})
  : SteelGhost unit opened
  (starseq #a #b f f_lemma s)
  (fun _ -> starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
         f (Seq.index s n))
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  = starseq_unpack_s #_ #a #b f f_lemma s n;
    starseq_empty_equiv_emp #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s));
    assert (hp_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) == hp_of emp);
    rewrite_slprop (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) emp (fun _ -> ())

let init_u32_slice_lemma
  (n: U32.t{0 < U32.v n})
  (i: nat{i < U32.v n - 1})
  : Lemma
  (Seq.index (SeqUtils.init_u32_refined (U32.v (U32.sub n U32.one))) i
  ==
  Seq.index (Seq.slice (SeqUtils.init_u32_refined (U32.v n)) 0 (U32.v (U32.sub n U32.one))) i)
  =
  SeqUtils.init_u32_refined_index
    (U32.v (U32.sub n U32.one)) i;
  SeqUtils.lemma_index_slice
    (SeqUtils.init_u32_refined (U32.v n))
    0 (U32.v (U32.sub n U32.one)) i;
  SeqUtils.init_u32_refined_index
    (U32.v n) i

#push-options "--z3rlimit 50"
let rec array_to_pieces_rec (#opened:_)
  (#a: Type)
  (size: U32.t{U32.v size > 0})
  (max: U32.t{U32.v max > 0 /\ U32.v max * U32.v size <= FI.max_int U32.n})
  (arr: array a{A.length arr = U32.v (U32.mul max size)})
  : SteelGhostT unit opened
  (A.varray arr)
  (fun _ ->
    starseq
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))

      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max))
  )
  (decreases (U32.v max))
  =
  if (U32.eq max U32.one) then (
    let arr2 = slot_array size max arr 0ul in
    let p1 = A.ptr_of arr in
    let p2 = A.ptr_of arr2 in
    assert (A.base p1 == A.base p2);
    assert (A.offset p1 == A.offset p2);
    A.ptr_base_offset_inj p1 p2;
    assert (A.ptr_of arr == A.ptr_of arr2);
    assert (slot_array size max arr 0ul == arr);
    SeqUtils.init_u32_refined_index (U32.v max) 0;
    change_equal_slprop
      (A.varray arr)
      (slot_vprop #a size max arr (Seq.index (SeqUtils.init_u32_refined (U32.v max)) 0));
    starseq_from_singleton_s
      #_
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max))
  ) else (
    assert (U32.gt max U32.one);
    let max' = U32.sub max U32.one in
    assert_norm (FStar.UInt.size (U32.v max' * U32.v size) U32.n);
    assert (U32.v (U32.mul max' size) == U32.v max' * U32.v size);
    let index = U32.mul max' size in
    let index = US.uint32_to_sizet index in
    A.ghost_split arr index;
    array_to_pieces_rec size max' (A.split_l arr index);
    let arr1 = A.split_r arr index in
    let arr2 = slot_array size max arr max' in
    A.ptr_base_offset_inj (A.ptr_of arr1) (A.ptr_of arr2);
    assert (arr1 == arr2);
    SeqUtils.init_u32_refined_index (U32.v max) (U32.v max');
    change_equal_slprop
      (A.varray (A.split_r arr index))
      (slot_vprop size max arr
        (Seq.index (SeqUtils.init_u32_refined (U32.v max)) (U32.v max'))
      );
    Classical.forall_intro (init_u32_slice_lemma max);
    assert (forall i.
      Seq.index (SeqUtils.init_u32_refined (U32.v max')) i
      ==
      Seq.index (Seq.slice (SeqUtils.init_u32_refined (U32.v max)) 0 (U32.v max')) i);
    starseq_weakening_ref
      #_
      #(pos: U32.t{U32.v pos < U32.v max'})
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max' (A.split_l arr index))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max' (A.split_l arr index))
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max'))
      (Seq.slice (SeqUtils.init_u32_refined (U32.v max)) 0 (U32.v max'));
    starseq_add_singleton_s
      #_
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max))
      (U32.v max')
  )
#pop-options

let array_to_pieces (#opened:_)
  (#a: Type)
  (size: U32.t{U32.v size > 0})
  (max: U32.t{0 < U32.v max /\ U32.v max * U32.v size <= FI.max_int U32.n})
  (arr: array a{A.length arr = U32.v (U32.mul max size)})
  : SteelGhostT unit opened
  (A.varray arr)
  (fun _ ->
    starseq
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max))
  )
  =
  array_to_pieces_rec size max arr

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let rec pieces_to_array_rec (#opened:_)
  (#a: Type)
  (size: U32.t{U32.v size > 0})
  (max: U32.t{U32.v max > 0 /\ U32.v max * U32.v size <= FI.max_int U32.n})
  (arr: array a{A.length arr = U32.v (U32.mul max size)})
  : SteelGhostT unit opened
  (starseq
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max))
  )
  (fun _ -> A.varray arr)
  (decreases (U32.v max))
  =
  if (U32.eq max U32.one) then (
    let arr2 = slot_array size max arr 0ul in
    let p1 = A.ptr_of arr in
    let p2 = A.ptr_of arr2 in
    assert (A.base p1 == A.base p2);
    assert (A.offset p1 == A.offset p2);
    A.ptr_base_offset_inj p1 p2;
    assert (A.ptr_of arr == A.ptr_of arr2);
    assert (slot_array size max arr 0ul == arr);
    SeqUtils.init_u32_refined_index (U32.v max) 0;
    starseq_to_singleton_s
      #_
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max));
    change_equal_slprop
      (slot_vprop #a size max arr (Seq.index (SeqUtils.init_u32_refined (U32.v max)) 0))
      (A.varray arr)
  ) else (
    assert (U32.gt max U32.one);
    let max' = U32.sub max U32.one in
    assert_norm (FStar.UInt.size (U32.v max' * U32.v size) U32.n);
    assert (U32.v (U32.mul max' size) == U32.v max' * U32.v size);
    let index = U32.mul max' size in
    let index = US.uint32_to_sizet index in

    let arr1 = A.split_r arr index in
    let arr2 = slot_array size max arr max' in
    A.ptr_base_offset_inj (A.ptr_of arr1) (A.ptr_of arr2);
    assert (arr1 == arr2);
    SeqUtils.init_u32_refined_index (U32.v max) (U32.v max');
    Classical.forall_intro (init_u32_slice_lemma max);

    starseq_remove_singleton_s
      #_
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max))
      (U32.v max');
    starseq_weakening_ref
      #_
      #(pos: U32.t{U32.v pos < U32.v max})
      #(pos: U32.t{U32.v pos < U32.v max'})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop #a size max' (A.split_l arr index))
      (slot_vprop_lemma #a size max arr)
      (slot_vprop_lemma #a size max' (A.split_l arr index))
      (Seq.slice (SeqUtils.init_u32_refined (U32.v max)) 0 (U32.v max'))
      (SeqUtils.init_u32_refined (U32.v max'));

    change_equal_slprop
      (slot_vprop size max arr
        (Seq.index (SeqUtils.init_u32_refined (U32.v max)) (U32.v max'))
      )
      (A.varray (A.split_r arr index));
    pieces_to_array_rec size max' (A.split_l arr index);
    A.ghost_join (A.split_l arr index) (A.split_r arr index) ();
    change_equal_slprop (A.varray _) (A.varray _)
  )
#pop-options

let pieces_to_array (#opened:_)
  (#a: Type)
  (size: U32.t{U32.v size > 0})
  (max: U32.t{0 < U32.v max /\ U32.v max * U32.v size <= FI.max_int U32.n})
  (arr: array a{A.length arr = U32.v (U32.mul max size)})
  : SteelGhostT unit opened
  (starseq
      #(pos: U32.t{U32.v pos < U32.v max})
      #(Seq.lseq a (U32.v size))
      (slot_vprop #a size max arr)
      (slot_vprop_lemma #a size max arr)
      (SeqUtils.init_u32_refined (U32.v max))
  )
  (fun _ -> A.varray arr)
  = pieces_to_array_rec size max arr

module FU = FStar.UInt
module FBV = FStar.BitVector

let empty_md_lemma
  (idx: nat{idx < U64.n * 4})
  : Lemma
  (Seq.index (a2bv (Seq.create 4 0UL)) idx == false)
  =
  let s = Seq.create 4 0UL in
  let r = Seq.index (a2bv s) idx in
  Bitmap4.array_to_bv2_index #4 s idx;
  assert (Seq.index s (idx/U64.n) == 0UL);
  assert (r == FU.nth #U64.n (U64.v 0UL) (idx%U64.n));
  assert (r == Seq.index (FU.to_vec #U64.n 0) (idx%U64.n));
  assert (FU.to_vec #U64.n 0 == FU.to_vec #U64.n (FU.zero U64.n))

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let slab_to_slots_aux
  (size_class: sc)
  (arr: array U8.t{A.length arr = US.v (rounding size_class)})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : Lemma
  (slab_vprop_aux_f size_class (Seq.create 4 0UL) arr pos
  ==
  some_as_vp #(Seq.lseq U8.t (U32.v size_class)) (SlotsAlloc.slot_vprop size_class arr pos))
  =
  let bm = a2bv (Seq.create 4 0UL) in
  let idx = Bitmap5.f #4 (U32.v pos) in
  empty_md_lemma idx;
  SlotsAlloc.starseq_upd_aux_lemma3 size_class (Seq.create 4 0UL) arr pos;
  SeqUtils.init_u32_refined_index (U32.v (nb_slots size_class)) (U32.v pos);
  assert (
    (slab_vprop_aux_f size_class (Seq.create 4 0UL) arr pos)
    ==
    some_as_vp #(Seq.lseq U8.t (U32.v size_class))
      (SlotsAlloc.slot_vprop size_class arr pos)
  )
#pop-options

let slab_to_slots (#opened:_)
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : SteelGhostT unit opened
  (A.varray arr)
  (fun _ ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class (Seq.create 4 0UL)
        (A.split_l arr (rounding size_class)))
      (slab_vprop_aux_f_lemma size_class (Seq.create 4 0UL)
        (A.split_l arr (rounding size_class)))
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    `star`
    A.varray (A.split_r arr (rounding size_class))
  )
  =
  A.ghost_split arr (rounding size_class);
  array_to_pieces size_class (nb_slots size_class) (A.split_l arr (rounding size_class));
  starseq_weakening
    #_
    #(pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(Seq.lseq U8.t (U32.v size_class))
    (slot_vprop size_class (nb_slots size_class)
      (A.split_l arr (rounding size_class)))
    (SlotsAlloc.slot_vprop size_class
      (A.split_l arr (rounding size_class)))
    (slot_vprop_lemma size_class (nb_slots size_class)
      (A.split_l arr (rounding size_class)))
    (SlotsAlloc.slot_vprop_lemma size_class
      (A.split_l arr (rounding size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)));
  Classical.forall_intro (slab_to_slots_aux size_class
    (A.split_l arr (rounding size_class)));
  starseq_weakening_rel_some
    #_
    #(pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(Seq.lseq U8.t (U32.v size_class))
    (SlotsAlloc.slot_vprop size_class
      (A.split_l arr (rounding size_class)))
    (slab_vprop_aux_f size_class (Seq.create 4 0UL)
      (A.split_l arr (rounding size_class)))
    (SlotsAlloc.slot_vprop_lemma size_class
      (A.split_l arr (rounding size_class)))
    (slab_vprop_aux_f_lemma size_class (Seq.create 4 0UL)
      (A.split_l arr (rounding size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))

noextract
let zero_beyond_bound
  (size_class: sc)
  (md_as_seq: Seq.lseq U64.t 4)
  : prop
  =
  let bm = Bitmap4.array_to_bv2 md_as_seq in
  let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
  zf_b (Seq.slice bm 0 (64 - U32.v bound2))

#restart-solver

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let empty_not_bitmap
  (size_class:sc)
  (s:Seq.lseq U64.t 4)
  (i:U32.t{U32.v i < U32.v (nb_slots size_class)})
  : Lemma
  (requires is_empty size_class s /\ zero_beyond_bound size_class s)
  (ensures not (Bitmap4.get s i))
  =
  Bitmap4.get_lemma s i;
  let v = FStar.UInt.nth (U64.v (Seq.index s (U32.v i / U64.n))) (U64.n - (U32.v i % U64.n) - 1) in
  let idx = U32.v i / U64.n in
  let bv = Seq.index s idx in
  assert (bv == 0UL);
  Classical.move_requires (lemma_nth_nonzero bv) (U64.n - (U32.v i % U64.n) - 1)
#pop-options

let slots_to_slabs (#opened:_)
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: G.erased (Seq.lseq U64.t 4))
  : SteelGhost unit opened
  (
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md
        (A.split_l arr (rounding size_class)))
      (slab_vprop_aux_f_lemma size_class md
        (A.split_l arr (rounding size_class)))
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    `star`
    A.varray (A.split_r arr (rounding size_class))
  )
  (fun _ -> A.varray arr)
  (requires fun _ -> is_empty size_class md /\ zero_beyond_bound size_class md)
  (ensures fun _ _ _ -> True)
  =
  let s = SeqUtils.init_u32_refined (U32.v (nb_slots size_class)) in
  Classical.forall_intro (Classical.move_requires (empty_not_bitmap size_class md));
  assert (forall (k:nat{k < U32.v (nb_slots size_class)}).
    slab_vprop_aux_f size_class md (A.split_l arr (rounding size_class)) (Seq.index s k) ==
    some_as_vp #((Seq.lseq U8.t (U32.v size_class))) (SlotsAlloc.slot_vprop size_class (A.split_l arr (rounding size_class)) (Seq.index s k)));
  starseq_weakening_rel_from_some
    #_
    #(pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(Seq.lseq U8.t (U32.v size_class))
    (slab_vprop_aux_f size_class md
      (A.split_l arr (rounding size_class)))
    (SlotsAlloc.slot_vprop size_class
      (A.split_l arr (rounding size_class)))
    (slab_vprop_aux_f_lemma size_class md
      (A.split_l arr (rounding size_class)))
    (SlotsAlloc.slot_vprop_lemma size_class
      (A.split_l arr (rounding size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)));
  starseq_weakening
    #_
    #(pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
    #(Seq.lseq U8.t (U32.v size_class))
    (SlotsAlloc.slot_vprop size_class
      (A.split_l arr (rounding size_class)))
    (slot_vprop size_class (nb_slots size_class)
      (A.split_l arr (rounding size_class)))
    (SlotsAlloc.slot_vprop_lemma size_class
      (A.split_l arr (rounding size_class)))
    (slot_vprop_lemma size_class (nb_slots size_class)
      (A.split_l arr (rounding size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
    (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)));
  pieces_to_array size_class (nb_slots size_class)
    (A.split_l arr (rounding size_class));
  A.ghost_join
    (A.split_l arr (rounding size_class))
    (A.split_r arr (rounding size_class))
    ();
  change_equal_slprop
    (A.varray (A.merge
      (A.split_l arr (rounding size_class))
      (A.split_r arr (rounding size_class))))
    (A.varray arr)

#push-options "--fuel 1 --ifuel 1"
let intro_empty_slab_varray (#opened:_)
  (size_class: sc)
  (md_as_seq: G.erased (Seq.lseq U64.t 4))
  (arr: array U8.t{A.length arr = U32.v page_size})
  : SteelGhost unit opened
  (
    slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq) `star`
    A.varray (A.split_r arr (rounding size_class))
  )
  (fun _ -> A.varray arr)
  (requires fun h0 ->
    is_empty size_class (G.reveal md_as_seq) /\
    slab_vprop_aux2 size_class md_as_seq
  )
  (ensures fun h0 _ h1 -> True)
  =
  change_equal_slprop
    (slab_vprop_aux size_class (A.split_l arr (rounding size_class)) (G.reveal md_as_seq))
    (starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class md_as_seq
        (A.split_l arr (rounding size_class)))
      (slab_vprop_aux_f_lemma size_class md_as_seq
        (A.split_l arr (rounding size_class)))
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class))));
  slots_to_slabs size_class arr md_as_seq
#pop-options
