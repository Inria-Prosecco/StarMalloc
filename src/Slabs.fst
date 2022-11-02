module Slabs

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module G = FStar.Ghost
module FU = FStar.UInt
module L = FStar.List.Tot

let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr

open FStar.Mul
open Utils

//TODO: should not be hardcoded
let page_size = 4096ul
let slab_max_number = 4096ul

noextract
let min_sc = 16
noextract
let max_sc = 64

//TODO: second constraint should be relaxed
//currently does not support size classes with <64 slots
//that require a subtle loop to read only possible
//corresponding slots in the bitmap
let sc = x:U32.t{min_sc <= U32.v x /\ U32.v x <= max_sc}

let slab_region_len : U32.t = normalize_term (U32.mul page_size slab_max_number)
unfold let slab_region
  = r:array U8.t{A.length r = U32.v slab_region_len}

let slab_md_region_len : U32.t = normalize_term (U32.mul 40ul slab_max_number)
unfold let slab_md_region
  = r:array U8.t{A.length r = U32.v slab_md_region_len}

// C binding, no top-level Steel initialization
assume val get_slab_region (_:unit)
  : slab_region

// C binding, no top-level Steel initialization
assume val get_slab_md_region (_:unit)
  : slab_md_region

let nb_slots (size_class: sc)
  : Pure U32.t
  (requires True)
  (ensures fun r ->
    U32.v r >= 1 /\
    U32.v r <= 256
  )
  =
  U32.div page_size size_class

//TODO
noextract
let slab_md_bitmap_length = nb_slots (U32.uint_to_t min_sc)

unfold let slab_metadata = r:array U64.t{A.length r = 4}

#push-options "--z3rlimit 30"
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
    U64.v (Seq.index (A.asel bitmap h0) (U32.v i)) <> 0)
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
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
let has_free_slot
  (size_class: sc)
  (s: Seq.lseq U64.t 4)
  : bool
  =
  let bound = U32.v (nb_slots size_class) / 64 in
  (U64.v (Seq.index s 0) > 0) ||
  (bound > 1 && (U64.v (Seq.index s 1) > 0)) ||
  (bound > 2 && (U64.v (Seq.index s 2) > 0)) ||
  (bound > 3 && (U64.v (Seq.index s 3) > 0))

let get_free_slot (size_class: sc) (bitmap: slab_metadata)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    let s = A.asel bitmap h0 in
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
  let bound = U32.div (nb_slots size_class) (U32.uint_to_t U64.n) in
  assert (U32.v bound == U32.v (nb_slots size_class) / 64);
  let x1 = A.index bitmap 0ul in
  if (U64.eq x1 0UL && U32.gt bound 1ul) then (
    let x2 = A.index bitmap 1ul in
    if (U64.eq x2 0UL && U32.gt bound 2ul) then (
      let x3 = A.index bitmap 2ul in
      if (U64.eq x3 0UL && U32.gt bound 3ul) then (
        get_free_slot_aux size_class bitmap 3ul
      ) else (
        get_free_slot_aux size_class bitmap 2ul
      )
    ) else (
      get_free_slot_aux size_class bitmap 1ul
    )
  ) else (
    get_free_slot_aux size_class bitmap 0ul
  )

#push-options "--z3rlimit 20"
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
  assert (U32.v shift < A.length arr);
  let ptr_shifted = A.ptr_shift ptr shift in
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

let slab_vprop1 (size_class: sc) (arr: array U8.t{A.length arr = U32.v page_size})
  (s: Seq.seq (r:nat{r < U32.v (nb_slots size_class)}))
  : GTot (Seq.seq vprop)
  =
  let f = fun (k:nat{k < U32.v (nb_slots size_class)})
    -> A.varray (slot_array size_class arr (U32.uint_to_t k)) in
  Seq.map_seq_len f s;
  let s' = Seq.map_seq f s in
  s'

let slab_vprop2 (size_class: sc) (arr: array U8.t{A.length arr = U32.v page_size})
  (s: Seq.seq (r:nat{r < U32.v (nb_slots size_class)}))
  : GTot (list vprop)
  =
  let s' = slab_vprop1 size_class arr s in
  let r = Seq.seq_to_list s' in
  r

let slab_vprop3 (size_class: sc) (arr: array U8.t{A.length arr = U32.v page_size})
  (s: Seq.seq (r:nat{r < U32.v (nb_slots size_class)}))
  : GTot vprop
  =
  let r = slab_vprop2 size_class arr s in
  starl r

let slab_vprop2_lemma
  (size_class: sc) (arr: array U8.t{A.length arr = U32.v page_size})
  (s1 s2: Seq.seq (r:nat{r < U32.v (nb_slots size_class)}))
  : Lemma
  (slab_vprop2 size_class arr (Seq.append s1 s2)
  == L.append (slab_vprop2 size_class arr s1) (slab_vprop2 size_class arr s2))
  =
  let f = fun (k:nat{k < U32.v (nb_slots size_class)})
    -> A.varray (slot_array size_class arr (U32.uint_to_t k)) in
  Seq.map_seq_append f s1 s2;
  assert (
     slab_vprop1 size_class arr (Seq.append s1 s2)
  == Seq.append (slab_vprop1 size_class arr s1) (slab_vprop1 size_class arr s2));
  lemma_seq_to_list_append
    (slab_vprop1 size_class arr s1)
    (slab_vprop1 size_class arr s2)

let slab_vprop3_lemma
  (size_class: sc) (arr: array U8.t{A.length arr = U32.v page_size})
  (s1 s2: Seq.seq (r:nat{r < U32.v (nb_slots size_class)}))
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
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (i:nat)
  (j:nat{i <= j /\ j <= U32.v (nb_slots size_class)})
  : Tot vprop
  =
  let s = Seq.slice (Seq.init (U32.v (nb_slots size_class)) (fun k -> k)) i j in
  slab_vprop3 size_class arr s

let slab_vprop_lemma
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (i:nat)
  (j:nat{i <= j /\ j <= U32.v (nb_slots size_class)})
  (k:nat{i <= k /\ k <= j})
  : Lemma
  (slab_vprop size_class arr i j
  `equiv` (
         (slab_vprop size_class arr i k)
  `star` (slab_vprop size_class arr k j)))
  =
  let s = Seq.init (U32.v (nb_slots size_class)) (fun k -> k) in
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
  (size_class: sc)
  (md: slab_metadata)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (i:nat)
  (j:nat{i <= j /\ j <= U32.v (nb_slots size_class)})
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
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{0 <= (U32.v pos) /\ (U32.v pos) < U32.v (nb_slots size_class)})
  : Lemma
  (slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)
  ==
  (A.varray (slot_array size_class arr pos) `star` emp)
  )
  =
  let r = slab_vprop size_class arr (U32.v pos) (U32.v pos + 1) in
  let s = Seq.slice (Seq.init (U32.v (nb_slots size_class)) (fun k -> k))
    (U32.v pos) (U32.v pos + 1) in
  assert (r == slab_vprop3 size_class arr s);
  assert (r == starl (slab_vprop2 size_class arr s));
  assert (r == starl (Seq.seq_to_list (slab_vprop1 size_class arr s)));
  let f = fun (k:nat{k < U32.v (nb_slots size_class)})
    -> A.varray (slot_array size_class arr (U32.uint_to_t k)) in
  Seq.map_seq_len f s;
  assert (Seq.length (slab_vprop1 size_class arr s) == 1);
  Seq.map_seq_index f s 0;
  assert (r == starl ([A.varray (slot_array size_class arr pos)]));
  assert (r == A.varray (slot_array size_class arr pos) `star` emp)

let allocate_slot_aux (#opened:_)
  (size_class: sc)
  (md: slab_metadata) (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : SteelGhostT unit opened
  (slab_vprop size_class arr 0 (U32.v (nb_slots size_class)) `star` A.varray md)
  (fun _ ->
    (slab_vprop size_class arr 0 (U32.v pos)) `star`
    A.varray (slot_array size_class arr pos) `star`
    (slab_vprop size_class arr (U32.v pos + 1) (U32.v (nb_slots size_class)) `star`
    A.varray md))
  =
  rewrite_slprop
    (slab_vprop size_class arr 0 (U32.v (nb_slots size_class)))
    ((slab_vprop size_class arr 0 (U32.v pos)) `star`
      (slab_vprop size_class arr (U32.v pos) (U32.v (nb_slots size_class))))
    (slab_vprop_sl_lemma size_class md arr
      0 (U32.v (nb_slots size_class)) (U32.v pos));
  rewrite_slprop
    (slab_vprop size_class arr (U32.v pos) (U32.v (nb_slots size_class)))
    ((slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)) `star`
    (slab_vprop size_class arr (U32.v pos + 1) (U32.v (nb_slots size_class))))
    (slab_vprop_sl_lemma size_class md arr
      (U32.v pos) (U32.v (nb_slots size_class)) (U32.v pos + 1));
  slab_vprop_singleton_lemma size_class arr pos;
  assert (
    slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)
    ==
    A.varray (slot_array size_class arr pos) `star` emp
    );
  change_slprop_rel
    (slab_vprop size_class arr (U32.v pos) (U32.v pos + 1))
    (A.varray (slot_array size_class arr pos) `star` emp)
    (fun x y -> x == y)
    (fun _ -> ());
  ()

#set-options "--ide_id_info_off"

let allocate_slot (size_class: sc)
  (md: slab_metadata) (arr: array U8.t{A.length arr = U32.v page_size})
  : Steel
    (r:(G.erased nat & array U8.t){
      G.reveal (fst r) < U32.v (nb_slots size_class) /\
      same_base_array (snd r) arr})
  (slab_vprop size_class arr 0 (U32.v (nb_slots size_class)) `star` A.varray md)
  (fun r ->
    (slab_vprop size_class arr 0 (fst r)) `star`
    A.varray (snd r) `star`
    (slab_vprop size_class arr (fst r + 1) (U32.v (nb_slots size_class)) `star`
    A.varray md)
  )
  (requires fun h0 -> has_free_slot size_class (A.asel md h0))
  (ensures fun _ _ _ -> True)
  =
  let slot_pos = get_free_slot size_class md in
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
