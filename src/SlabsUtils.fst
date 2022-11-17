module SlabsUtils

module U64 = FStar.UInt64
module U32 = FStar.UInt32
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


open Utils
open Utils2

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
