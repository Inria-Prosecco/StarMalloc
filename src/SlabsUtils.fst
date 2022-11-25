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


open Utils
open Utils2
open SteelUtils

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
  (pos: nat{pos < U32.v (nb_slots size_class)})
  =
  A.varray (slot_array size_class arr (U32.uint_to_t pos))

let slab_vprop_aux
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md_as_seq: Seq.lseq U64.t 4)
  : vprop
  =
  let incr_seq = SeqUtils.init_u32_refined (U32.v (nb_slots size_class))
  in
  let f = fun (i: U32.t{U32.v i < U32.v (nb_slots size_class)}) ->
    if Bitmap4.get md_as_seq i
    then slot_vprop size_class arr (U32.v i)
    else emp
  in
  Seq.map_seq_len f incr_seq;
  let vprop_seq
    : Seq.lseq vprop (U32.v (nb_slots size_class))
    = Seq.map_seq f incr_seq in
  let vprop_list = Seq.seq_to_list vprop_seq in
  starl vprop_list

let slab_vprop
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  =
  A.varray md `vdep` (fun md_as_seq -> slab_vprop_aux size_class arr md_as_seq)
