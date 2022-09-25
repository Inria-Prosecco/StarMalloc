module Slabs

module L = FStar.List.Tot
open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module M = FStar.Math.Lib
module G = FStar.Ghost
module FU = FStar.UInt
open Seq2

let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr

open FStar.Mul
open Utils

let array_to_bv_slice
  (#n: nat)
  (s0: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires
    i < n
  )
  (ensures (
    let bm0 = Bitmap4.array_to_bv2 s0 in
    let x = Seq.index s0 i in
    Seq.slice bm0 (i*64) ((i+1)*64)
    =
    FU.to_vec #64 (U64.v x)))
  =
  Bitmap4.array_to_bv_lemma_upd_set_aux4 s0 (i*64)

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let get_free_slot_aux (bitmap: slab_metadata) (i: U32.t)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    U32.v i < 4 /\
    U64.v (Seq.index (A.asel bitmap h0) (U32.v i)) <> 0)
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r <= 255 /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false)
  )
  =
  let h0 = get () in
  let x = A.index bitmap i in
  let r = ffs64 x in
  let bm = G.hide (Bitmap4.array_to_bv2 (A.asel bitmap h0)) in
  let idx1 = G.hide ((U32.v i) * 64) in
  let idx2 = G.hide ((U32.v i + 1) * 64) in
  assert (x == Seq.index (A.asel bitmap h0) (U32.v i));
  assert (FU.nth (U64.v x) (U64.n - 1 - U32.v r) = false);
  array_to_bv_slice (A.asel bitmap h0) (U32.v i);
  assert (FU.to_vec (U64.v x) == Seq.slice bm ((U32.v i)*64) ((U32.v i + 1)*64));
  Seq.lemma_index_slice bm ((U32.v i)*64) ((U32.v i + 1)*64) (U32.v r);
  let r' = U32.mul 64ul i in
  U32.add r r'
#pop-options

noextract
let has_free_slot (s: Seq.lseq U64.t 4)
  : bool
  =
  (U64.v (Seq.index s 0) > 0) ||
  (U64.v (Seq.index s 1) > 0) ||
  (U64.v (Seq.index s 2) > 0) ||
  (U64.v (Seq.index s 3) > 0)


let get_free_slot (bitmap: slab_metadata)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    let s = A.asel bitmap h0 in
    has_free_slot s
  )
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r <= 255 /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false)
  )
  =
  let x1 = A.index bitmap 0ul in
  if U64.eq x1 0UL then (
    let x2 = A.index bitmap 1ul in
    if U64.eq x2 0UL then (
      let x3 = A.index bitmap 2ul in
      if U64.eq x3 0UL then (
        get_free_slot_aux bitmap 3ul
      ) else (
        get_free_slot_aux bitmap 2ul
      )
    ) else (
      get_free_slot_aux bitmap 1ul
    )
  ) else (
    get_free_slot_aux bitmap 0ul
  )

let starl (l: list vprop)
  : vprop
  =
  L.fold_left star emp l

//TODO
noextract
let page_size = 4096

noextract
let nb_slots (size_class: U32.t)
  : Pure nat
  (requires
    0 < U32.v size_class
  )
  (ensures fun _ -> True)
  =
  page_size / (U32.v size_class)

let slot_array (size_class: U32.t) (arr: array U8.t) (pos: U32.t)
  : Pure (array U8.t)
  (requires
    U32.v size_class > 0 /\
    U32.v pos < nb_slots size_class /\
    A.length arr = page_size)
  (ensures fun r ->
    A.length r = U32.v size_class /\
    same_base_array r arr /\
    True)
  =
  let ptr = A.ptr_of arr in
  let shift = U32.mul pos size_class in
  assert (U32.v shift < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift in
  (| ptr_shifted, G.hide (U32.v size_class) |)

let array_slot (size_class: U32.t) (arr: array U8.t) (slot: array U8.t)
  : Pure (G.erased int)
  (requires
     same_base_array arr slot /\
     U32.v size_class > 0)
  (ensures fun r -> True)
  =
  let ptr1 = A.ptr_of arr in
  assert (A.offset ptr1 <= A.base_len (A.base ptr1));
  let ptr2 = A.ptr_of slot in
  assert (A.offset ptr2 <= A.base_len (A.base ptr2));
  let offset_bytes = A.offset ptr2 - A.offset ptr1 in
  let offset_slot = offset_bytes / (U32.v size_class) in
  offset_slot

let lemma_div (x y z: nat)
  : Lemma
  (requires
    x = y * z /\
    z > 0
  )
  (ensures
    x / z = y
  )
  =
  FStar.Math.Lemmas.lemma_mod_plus 0 y z;
  assert ((y * z) % z = 0)

let array_slot_slot_array_bij (size_class: U32.t) (arr: array U8.t) (pos: U32.t)
  : Lemma
  (requires
    U32.v size_class > 0 /\
    U32.v pos < nb_slots size_class /\
    A.length arr = page_size)
  (ensures (
    let slot_as_array = slot_array size_class arr pos in
    let slot_as_pos = array_slot size_class arr slot_as_array in
    G.reveal slot_as_pos = U32.v pos))
  =
  let ptr = A.ptr_of arr in
  let shift = U32.mul pos size_class in
  assert (U32.v shift < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift in
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

let slab_vprop1 (size_class: U32.t{U32.v size_class > 0}) (arr: array U8.t{A.length arr = page_size})
  (s: Seq.seq (r:nat{r < nb_slots size_class}))
  : GTot (Seq.seq vprop)
  =
  let f = fun (k:nat{k < nb_slots size_class})
    -> A.varray (slot_array size_class arr (U32.uint_to_t k)) in
  Seq.map_seq_len f s;
  let s' = Seq.map_seq f s in
  s'

let slab_vprop2 (size_class: U32.t{U32.v size_class > 0}) (arr: array U8.t{A.length arr = page_size})
  (s: Seq.seq (r:nat{r < nb_slots size_class}))
  : GTot (list vprop)
  =
  let s' = slab_vprop1 size_class arr s in
  let r = Seq.seq_to_list s' in
  r

let slab_vprop3 (size_class: U32.t{U32.v size_class > 0}) (arr: array U8.t{A.length arr = page_size})
  (s: Seq.seq (r:nat{r < nb_slots size_class}))
  : GTot vprop
  =
  let r = slab_vprop2 size_class arr s in
  starl r

let lemma_seq_to_list_append (#a:Type) (s1 s2: Seq.seq a)
  : Lemma
  (Seq.seq_to_list (Seq.append s1 s2) == L.append (Seq.seq_to_list s1) (Seq.seq_to_list s2))
  =
  admit ()

let slab_vprop2_lemma
  (size_class: U32.t{U32.v size_class > 0}) (arr: array U8.t{A.length arr = page_size})
  (s1: Seq.seq (r:nat{r < nb_slots size_class}))
  (s2: Seq.seq (r:nat{r < nb_slots size_class}))
  : Lemma
  (slab_vprop2 size_class arr (Seq.append s1 s2)
  == L.append (slab_vprop2 size_class arr s1) (slab_vprop2 size_class arr s2))
  =
  let f = fun (k:nat{k < nb_slots size_class})
    -> A.varray (slot_array size_class arr (U32.uint_to_t k)) in
  Seq.map_seq_append f s1 s2;
  assert (
     slab_vprop1 size_class arr (Seq.append s1 s2)
  == Seq.append (slab_vprop1 size_class arr s1) (slab_vprop1 size_class arr s2));
  lemma_seq_to_list_append
    (slab_vprop1 size_class arr s1)
    (slab_vprop1 size_class arr s2)

// TODO @AF
let starl_append (l1 l2: list vprop)
  : Lemma
  (starl (L.append l1 l2) `equiv` (starl l1 `star` starl l2))
  = admit ()

let slab_vprop3_lemma
  (size_class: U32.t{U32.v size_class > 0}) (arr: array U8.t{A.length arr = page_size})
  (s1: Seq.seq (r:nat{r < nb_slots size_class}))
  (s2: Seq.seq (r:nat{r < nb_slots size_class}))
  : Lemma
  (slab_vprop3 size_class arr (Seq.append s1 s2)
  `equiv` (
         (slab_vprop3 size_class arr s1)
  `star` (slab_vprop3 size_class arr s2)))
  =
  let l1 = slab_vprop2 size_class arr s1 in
  let l2 = slab_vprop2 size_class arr s2 in
  slab_vprop2_lemma size_class arr s1 s2;
  starl_append l1 l2

let slab_vprop
  (size_class: U32.t{U32.v size_class > 0})
  (arr: array U8.t{A.length arr = page_size})
  (i:nat)
  (j:nat{i <= j /\ j <= nb_slots size_class})
  : Tot vprop
  =
  let s = Seq.slice (Seq.init (nb_slots size_class) (fun k -> k)) i j in
  slab_vprop3 size_class arr s

let lemma_index_slice (#a:Type) (s:Seq.seq a)
  (i:nat)
  (j:nat{i <= j /\ j <= Seq.length s})
  (k:nat{k < j - i})
  : Lemma
  (requires True)
  (ensures (Seq.index (Seq.slice s i j) k == Seq.index s (k + i)))
  =
  Seq.lemma_index_slice s i j k

let slab_vprop_lemma
  (size_class: U32.t{U32.v size_class > 0})
  (arr: array U8.t{A.length arr = page_size})
  (i:nat)
  (j:nat{i <= j /\ j <= nb_slots size_class})
  (k:nat{i <= k /\ k <= j})
  : Lemma
  (slab_vprop size_class arr i j
  `equiv` (
         (slab_vprop size_class arr i k)
  `star` (slab_vprop size_class arr k j)))
  =
  let s = Seq.init (nb_slots size_class) (fun k -> k) in
  let s1 = Seq.slice s i j in
  let s2, s3 = Seq.split s1 (k - i) in
  Seq.lemma_split s1 (k - i);
  assert (s2 == Seq.slice s1 0 (k - i));
  Classical.forall_intro (lemma_index_slice s1 0 (k - i));
  assert (s3 == Seq.slice s1 (k - i) (j - i));
  Classical.forall_intro (lemma_index_slice s1 (k - i) (j - i));
  slab_vprop3_lemma size_class arr s2 s3

module SM = Steel.Memory

let slab_vprop_sl_lemma
  (size_class: U32.t{U32.v size_class > 0})
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = page_size})
  (i:nat)
  (j:nat{i <= j /\ j <= nb_slots size_class})
  (k:nat{i <= k /\ k <= j})
  (m: SM.mem)
  : Lemma
  (requires SM.interp (hp_of (
    (slab_vprop size_class arr i j)
  )) m)
  (ensures SM.interp (hp_of (
    (slab_vprop size_class arr i k `star`
    slab_vprop size_class arr k j)
  )) m)
  =
  slab_vprop_lemma size_class arr i j k;
  let p = slab_vprop size_class arr i j in
  let q = (slab_vprop size_class arr i k) `star`
          (slab_vprop size_class arr k j) in
  assert (p `equiv` q);
  reveal_equiv p q;
  assert (hp_of p `SM.equiv` hp_of q);
  SM.reveal_equiv (hp_of p) (hp_of q)

let slab_vprop_singleton_lemma
  (size_class: U32.t{U32.v size_class > 0})
  (arr: array U8.t{A.length arr = page_size})
  (pos: U32.t{0 <= (U32.v pos) /\ (U32.v pos) < nb_slots size_class})
  : Lemma
  (slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)
  ==
  (emp `star` A.varray (slot_array size_class arr pos))
  )
  =
  let r = slab_vprop size_class arr (U32.v pos) (U32.v pos + 1) in
  let s = Seq.slice (Seq.init (nb_slots size_class) (fun k -> k))
    (U32.v pos) (U32.v pos + 1) in
  //lemma_index_slice s (U32.v pos) (U32.v pos + 1) 0;
  assert (r == slab_vprop3 size_class arr s);
  assert (r == starl (slab_vprop2 size_class arr s));
  assert (r == starl (Seq.seq_to_list (slab_vprop1 size_class arr s)));
  let f = fun (k:nat{k < nb_slots size_class})
    -> A.varray (slot_array size_class arr (U32.uint_to_t k)) in
  Seq.map_seq_len f s;
  assert (Seq.length (slab_vprop1 size_class arr s) == 1);
  Seq.map_seq_index f s 0;
  assert (r == starl ([A.varray (slot_array size_class arr pos)]));
  assert (r == emp `star` A.varray (slot_array size_class arr pos))

let allocate_slot_aux (#opened:_) (size_class: U32.t{U32.v size_class > 0})
  (md: slab_metadata) (arr: array U8.t{A.length arr = page_size})
  (pos: U32.t{U32.v pos < nb_slots size_class})
  : SteelGhostT unit opened
  (slab_vprop size_class arr 0 (nb_slots size_class) `star` A.varray md)
  (fun _ ->
    (slab_vprop size_class arr 0 (U32.v pos)) `star`
    A.varray (slot_array size_class arr pos) `star`
    (slab_vprop size_class arr (U32.v pos + 1) (nb_slots size_class) `star`
    A.varray md))
  =
  rewrite_slprop
    (slab_vprop size_class arr 0 (nb_slots size_class))
    ((slab_vprop size_class arr 0 (U32.v pos)) `star`
      (slab_vprop size_class arr (U32.v pos) (nb_slots size_class)))
    (slab_vprop_sl_lemma size_class md arr
      0 (nb_slots size_class) (U32.v pos));
  rewrite_slprop
    (slab_vprop size_class arr (U32.v pos) (nb_slots size_class))
    ((slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)) `star`
    (slab_vprop size_class arr (U32.v pos + 1) (nb_slots size_class)))
    (slab_vprop_sl_lemma size_class md arr
      (U32.v pos) (nb_slots size_class) (U32.v pos + 1));
  slab_vprop_singleton_lemma size_class arr pos;
  assert (
    slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)
    ==
    emp `star` A.varray (slot_array size_class arr pos)
    );
  change_slprop_rel
    (slab_vprop size_class arr (U32.v pos) (U32.v pos + 1))
    (emp `star` A.varray (slot_array size_class arr pos))
    (fun x y -> x == y)
    (fun _ -> ());
  ()

#set-options "--ide_id_info_off"

let allocate_slot (size_class: U32.t{U32.v size_class > 0})
  (md: slab_metadata) (arr: array U8.t{A.length arr = page_size})
  : Steel
    (r:(G.erased nat & array U8.t){
      G.reveal (fst r) < nb_slots size_class /\
      same_base_array (snd r) arr})
  (slab_vprop size_class arr 0 (nb_slots size_class) `star` A.varray md)
  (fun r ->
    (slab_vprop size_class arr 0 (fst r)) `star`
    A.varray (snd r) `star`
    (slab_vprop size_class arr (fst r + 1) (nb_slots size_class) `star`
    A.varray md)
  )
  (requires fun h0 -> has_free_slot (A.asel md h0))
  (ensures fun _ _ _ -> True)
  =
  let slot_pos = get_free_slot md in
  assume (U32.v slot_pos < nb_slots size_class);
  Bitmap5.bm_set #(G.hide 4) md slot_pos;
  let slot = slot_array size_class arr slot_pos in
  array_slot_slot_array_bij size_class arr slot_pos;
  allocate_slot_aux size_class md arr slot_pos;
  change_slprop_rel
    (A.varray (slot_array size_class arr slot_pos))
    (A.varray slot)
    (fun x y -> x == y)
    (fun _ -> ());
  return (G.hide (U32.v slot_pos), slot)

(*)
  let slab_vprop_sl_lemma (m: SM.mem)
    : Lemma
    (requires SM.interp (hp_of (
      (slab_vprop size_class arr 0 (nb_slots size_class) `star` A.varray md)
    )) m)
    (ensures SM.interp (hp_of (
      (slab_vprop size_class arr 0 i `star`
      slab_vprop size_class arr i (nb_slots size_class) `star`
      A.varray md)
    )) m)
    =
    slab_vprop_lemma size_class arr 0 i (nb_slots size_class)
  in
  rewrite_slprop
    (slab_vprop size_class arr 0 (nb_slots size_class) `star`
    A.varray md)
    (slab_vprop size_class arr 0 i `star`
    slab_vprop size_class arr i (nb_slots size_class) `star`
    A.varray md)
    (fun m -> slab_vprop_sl_lemma m);
  //slab_vprop_lemma size_class arr 0 (U32.v slot_pos) (nb_slots size_class);
  sladmit ();
  return slot

(*)


    (bm_to_vprop #128 32 md)
    (A.varray (get_slab_region ()) `star`
    A.varray md)
    (fun a -> A.varray (get_slab_region ()) `star`
    A.varray md)
    (fun _ -> U32.v len = 32)
    (fun _ r h1 ->
      True
    )
  =
  let a = get_slab_region () in
  let slot = get_free_slot md in
  Bitmap5.bm_set #4 md slot;
  let offset = U32.mul 32ul slot in
  let ptr_slab_region = A.ptr_of a in
      )
    ) else (
      let idx =
    )
  ) else (

  )
  admit ();
  0ul




let allocate_small (len: U32.t) (md: slab_metadata)
  : Steel (ptr U8.t)
    (A.varray (get_slab_region ()) `star`
    A.varray md)
    (fun a -> A.varray (get_slab_region ()) `star`
    A.varray md)
    (fun _ -> U32.v len = 32)
    (fun _ r h1 ->
      True
    )
  =
  let a = get_slab_region () in
  let slot = get_free_slot md in
  Bitmap5.bm_set #4 md slot;
  let offset = U32.mul 32ul slot in
  let ptr_slab_region = A.ptr_of a in
  let ptr = A.ptr_shift ptr_slab_region offset in
  return ptr

(*)
//noextract
//let size_classes : list nzn = [
//  //(* 0 *) 0;
//  (* 16 *) 16; 32; 48; 64; 80; 96; 112; 128;
//  (* 32 *) 160; 192; 224; 256;
//  (* 64 *) 320; 384; 448; 512;
//]
//
//
//noextract
//let size_class_slots : list nzn =
//  L.map nb_of_slots size_classes
//
//let f (_:unit) =
//  let v = L.nth size_class_slots 0 in
//  assert(Some?.v v == 256);
//  ()

let page_size = 4096ul

let nzn = x:U32.t{U32.v x > 0 /\ U32.v x <= U32.v page_size}
let slab = slab:array U8.t{A.length slab == U32.v page_size}

let nb_slots (x: nzn) : nzn = U32.div page_size x

let slab_metadata (size_class: nzn)
  = Seq.lseq bool (U32.v (nb_slots size_class))

// used outside of spec, hence the u32
let ptr_slot
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  (n: U32.t{U32.lt n (nb_slots size_class)})
  : A.ptr U8.t
  =
  let ptr_slab = dfst slab in
  let shift = U32.mul n size_class in
  let ptr_slot = A.ptr_shift ptr_slab shift in
  ptr_slot

let arr_slot
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  (n: U32.t{U32.lt n (nb_slots size_class)})
  : arr:array U8.t{A.length arr = U32.v size_class}
  =
  let ptr = ptr_slot size_class slab n in
  let length = G.hide (U32.v size_class) in
  (| ptr, length |)

//@Spec
noextract
let init_nat (len: nat)
  : Seq.lseq (k:nat{k < len}) len
  = Seq.init len (fun k -> k)
//@Spec
noextract
let init_u32 (len: U32.t)
  : Seq.lseq (k:U32.t{U32.v k < U32.v len}) (U32.v len)
  =
  let s : Seq.lseq (k:nat{k < U32.v len}) (U32.v len)
    = init_nat (U32.v len) in
  let f : k:nat{k < U32.v len} -> k':U32.t{U32.v k' < U32.v len}
    = fun k -> U32.uint_to_t k in
  Seq.map_seq_len f s;
  Seq.map_seq f s
//@Spec
noextract
let slab_to_slots
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  : Seq.lseq
    (arr:array U8.t{A.length arr = U32.v size_class})
    (U32.v (nb_slots size_class))
  =
  let n = nb_slots size_class in
  let s = init_u32 n in
  let f = fun (k:U32.t{U32.v k < U32.v n})
          -> arr_slot size_class slab k in
  Seq.map_seq_len f s;
  Seq.map_seq f s
//@Spec
noextract
let sl_state
  (size_class: nzn)
  (slab: slab{A.is_full_array slab})
  (slab_md: slab_metadata size_class)
  : Seq.lseq vprop (U32.v (nb_slots size_class))
  =
  let f : bool -> array U8.t -> vprop
    = fun b arr -> if b then A.varray arr else emp in
  let s1 = slab_md in
  let s2 = slab_to_slots size_class slab
  in
  map_seq2_len f s1 s2;
  map_seq2 f s1 s2
//@Spec
let set_alloc
  (size_class: nzn)
  (slab_md: slab_metadata size_class)
  (i:nat{i < Seq.length slab_md})
  : Pure (slab_metadata size_class)
  (requires Seq.index slab_md i = false)
  (ensures fun slab_md' ->
    Seq.index slab_md' i = true /\
    (forall j. j <> i ==> Seq.index slab_md' j == Seq.index slab_md j)
  )
  = Seq.upd slab_md i true
//@Spec
let set_free
  (size_class: nzn)
  (slab_md: slab_metadata size_class)
  (i:nat{i < Seq.length slab_md})
  : Pure (slab_metadata size_class)
  (requires Seq.index slab_md i = true)
  (ensures fun slab_md' ->
    Seq.index slab_md' i = false /\
    (forall j. j <> i ==> Seq.index slab_md' j == Seq.index slab_md j)
  )
  = Seq.upd slab_md i false

let div_nbn_is_n (x y: int)
  : Lemma
  (requires x >= 0 /\ y > 0)
  (ensures x / y >= 0)
  = ()

noextract
let spec_smd_index_op0
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: Seq.lseq U64.t 4)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : U64.t
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  let bucket_pos = U32.v i / 64 in
  assert (bucket_pos < 4);
  let bucket = Seq.index slab_md bucket_pos in
  bucket

//@Spec
//open FStar.UInt
let uint64_to_uint32 (x: U64.t) (bound: nat)
  : Pure U32.t
  (requires U64.v x < bound /\ bound < FStar.UInt.max_int 32)
  (ensures fun r -> U32.v r == U64.v x /\ U32.v r < bound)
  = FStar.Int.Cast.uint64_to_uint32 x
open BVL

let smd_index_op0
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Steel U64.t
  (A.varray slab_md)
  (fun _ -> A.varray slab_md)
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    A.asel slab_md h1 == A.asel slab_md h0 /\
    x == spec_smd_index_op0 size_class (A.asel slab_md h1) i
  )
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  assert (U32.v i < 256);
  let i64 = uint32_to_uint64 i in
  let bucket_pos = div64_shift i64 in
  assert (U64.v bucket_pos < 4);
  let bucket_pos = uint64_to_uint32 bucket_pos 4 in
  let bucket = A.index slab_md bucket_pos in
  bucket

//@Spec
open FStar.Mul
noextract
let spec_smd_index_op1
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : nat
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  assert (U32.v i < 256);
  let bucket_pos = U32.v i / 64 in
  assert (bucket_pos < 4);
  let mask_shift : nat = U32.v i - (bucket_pos * 64) in
  assert (mask_shift = U32.v i % 64);
  mask_shift

let smd_index_op1
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : r:U32.t{U32.v r < 64}
  =
  assert (U32.lte (nb_slots size_class) 256ul);
  assert (U32.v i < 256);
  let i64 = uint32_to_uint64 i in
  assert (U64.v i64 == U32.v i);
  let bucket_pos = div64_shift i64 in
  assert (U64.v bucket_pos = U32.v i / 64);
  assert (U64.v bucket_pos < 4);
  let mask_shift_aux = mul64_shift bucket_pos in
  assert (U64.v mask_shift_aux = 64 * U64.v bucket_pos);
  let mask_shift = U64.sub i64 mask_shift_aux in
  assert (U64.v mask_shift = (U32.v i) % 64);
  assert (U64.v mask_shift < 64);
  let mask_shift32 : k:U32.t{U32.v k < 64}
    = uint64_to_uint32 mask_shift 64 in
  mask_shift32

let equiv_smd_index_op1
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Lemma
  (
  let r11 = spec_smd_index_op1 size_class bucket i in
  let r21 = smd_index_op1 size_class bucket i in
  r11 = U32.v r21)
  = ()

noextract
let spec_smd_index_op2
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: nat)
  : bool
  =
  div_nbn_is_n (U64.v bucket) (pow2  mask_shift);
  let r : nat = (U64.v bucket) / (pow2 mask_shift) in
  if r % 2 = 1
  then true
  else false

let smd_index_op2
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: U32.t{U32.v mask_shift < 64})
  : bool
  =
  let r = div64_shift2 bucket mask_shift in
  assert (U64.v r == (U64.v bucket) / (pow2 (U32.v mask_shift)));
  let r = U64.logand r 1UL in
  if U64.eq r 1UL
  then true
  else false

let equiv_smd_index_op2
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: U32.t{U32.v mask_shift < 64})
  : Lemma
  (
  let r11 = spec_smd_index_op2 size_class bucket (U32.v mask_shift) in
  let r21 = smd_index_op2 size_class bucket mask_shift in
  r11 = r21)
  =
  Classical.forall_intro logand1

noextract
let spec_smd_index_op3
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: nat)
  : nat
  =
  let r = (U64.v bucket) + (pow2 mask_shift) in
  r

let smd_index_op3
  (size_class: nzn{U32.v size_class >= 16})
  (bucket: U64.t)
  (mask_shift: U32.t{U32.v mask_shift < 64})
  : U64.t
  =
  let shifted_one = mul64_shift2 mask_shift in
  assert (U64.v shifted_one ==  pow2 (U32.v mask_shift));
  let r = U64.logor bucket shifted_one in
  r



//@Spec
noextract
let spec_smd_index
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: Seq.lseq U64.t 4)
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : bool
  =
  let bucket = spec_smd_index_op0 size_class slab_md i in
  let mask_shift = spec_smd_index_op1 size_class bucket i in
  let r = spec_smd_index_op2 size_class bucket mask_shift in
  r

let smd_index
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Steel bool
  (A.varray slab_md)
  (fun _ -> A.varray slab_md)
  (requires fun h0 -> True)
  (ensures fun h0 b h1 ->
      b == spec_smd_index size_class (A.asel slab_md h1) i /\
      A.asel slab_md h1 == A.asel slab_md h0
  )
  =
  let bucket = smd_index_op0 size_class slab_md i in
  let mask_shift = smd_index_op1 size_class bucket i in
  equiv_smd_index_op1 size_class bucket i;
  let r = smd_index_op2 size_class bucket mask_shift in
  equiv_smd_index_op2 size_class bucket mask_shift;
  return r

//@Spec
noextract
let smd2b
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: Seq.lseq U64.t 4)
  : (Seq.lseq bool (U32.v (nb_slots size_class)))
  =
  let f = spec_smd_index size_class slab_md in
  let s1 = init_u32 (nb_slots size_class) in
  Seq.map_seq_len f s1;
  Seq.map_seq f s1

[@@__steel_reduce__]
noextract
let v_smd
  (#vp:vprop)
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (h:rmem vp{
    FStar.Tactics.with_tactic selector_tactic
      (can_be_split vp (A.varray slab_md) /\ True)
  })
  : GTot (Seq.lseq bool (U32.v (nb_slots size_class)))
  =
  let s : G.erased (Seq.lseq U64.t 4) = h (A.varray slab_md) in
  G.hide (smd2b size_class (G.reveal s))

(*)


let slab_md_array_set_alloc
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  (i: U32.t{U32.lt i (nb_slots size_class)})
  : Steel unit
  (A.varray slab_md)
  (fun _ -> A.varray slab_md)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 ->

  )



(*)

let slab_md_array_to_seq
  (size_class: nzn{U32.v size_class >= 16})
  (slab_md: array U64.t{A.length slab_md == 4})
  //: slab_metadata size_class
  : unit
  = ()


(*)
let get_slot (page: array U8.t) (size_class: nat) (pos: nat)
  : Steel (array U8.t)
    (A.varray page)
    (fun r -> A.varray r)
    (fun h0 ->
      A.length page == page_size
    )
    (fun h0 r h1 -> A.length r == size_class)
    =
    return page
