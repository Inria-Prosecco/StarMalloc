module Helpers

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


// TODO: to be removed/move apart ; use stdlib
// discussion
let u32_to_sz
  (x:U32.t)
  : Tot (y:US.t{US.v y == U32.v x})
  //: Pure US.t
  //(requires True)
  //(ensures fun y -> US.v y == U32.v x)
  =
  assume (US.fits_u32);
  US.uint32_to_sizet x

open FStar.Mul
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
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
  let shift_sz = u32_to_sz shift in
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
  A.varray (slot_array size max  arr pos)

let slot_vprop_lemma (#a: Type)
  (size: U32.t{U32.v size > 0})
  (max: U32.t{U32.v max * U32.v size <= FI.max_int U32.n})
  (arr: array a{A.length arr = U32.v (U32.mul max size)})
  (pos: U32.t{U32.v pos < U32.v max})
  : Lemma
  (t_of (slot_vprop size max arr pos) == Seq.lseq a (U32.v size))
  =
  ()

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
  assume (starseq #a #b f f_lemma (Seq.slice s 0 0) == emp);
  assume (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s)) == emp);
  change_equal_slprop
    (starseq #a #b f f_lemma (Seq.slice s 0 0)) emp;
  change_equal_slprop
    (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s))) emp

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
  assume (starseq #a #b f f_lemma (Seq.slice s 0 0) == emp);
  assume (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s)) == emp);
  change_equal_slprop
    emp (starseq #a #b f f_lemma (Seq.slice s 0 0));
  change_equal_slprop
    emp (starseq #a #b f f_lemma (Seq.slice s 1 (Seq.length s)));
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
  assume (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) == emp);
  change_equal_slprop
    emp
    (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)));
  starseq_pack_s
    #_ #a #b
    f f_lemma s n

assume val starseq_weakening_ref (#opened:_)
  (#a1 #a2 #b: Type0)
  (f1: a1 -> vprop)
  (f2: a2 -> vprop)
  (f1_lemma: (x:a1 -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a2 -> Lemma (t_of (f2 x) == b)))
  (s1: Seq.seq a1)
  (s2: Seq.seq a2)
  : SteelGhost unit opened
  (starseq #a1 #b f1 f1_lemma s1)
  (fun _ -> starseq #a2 #b f2 f2_lemma s2)
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)))
  (ensures fun h0 _ h1 ->
    Seq.length s1 = Seq.length s2 /\
    v_starseq #a1 #b f1 f1_lemma s1 h0
    ==
    v_starseq #a2 #b f2 f2_lemma s2 h1
  )

#push-options "--z3rlimit 30"
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
    admit ();
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
    let index = u32_to_sz index in
    A.ghost_split arr index;
    array_to_pieces_rec size max' (A.split_l arr index);
    assume (A.split_r arr index == slot_array size max arr max');
    SeqUtils.init_u32_refined_index (U32.v max) (U32.v max');
    change_equal_slprop
      (A.varray (A.split_r arr index))
      (slot_vprop size max arr
        (Seq.index (SeqUtils.init_u32_refined (U32.v max)) (U32.v max'))
      );
    admit ();
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

//array_to_pieces
//starseq_weakening_ref
//pieces_to_slots
//starseq_weakening_rel

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

let slab_to_slots (#opened:_)
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  : SteelGhost unit opened
  (A.varray arr)
  (fun _ ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v (nb_slots size_class)})
      #(option (Seq.lseq U8.t (U32.v size_class)))
      (slab_vprop_aux_f size_class (Seq.create 4 0UL) arr)
      (slab_vprop_aux_f_lemma size_class (Seq.create 4 0UL) arr)
      (SeqUtils.init_u32_refined (U32.v (nb_slots size_class)))
  )
  (requires fun h0 ->
    //(U32.v page_size) % (U32.v size_class) == 0 /\
    A.asel arr h0 == Seq.create (U32.v page_size) U8.zero
  )
  (ensures fun _ _ _ ->
    True
  )
  =
  sladmit ();
  admit ()
