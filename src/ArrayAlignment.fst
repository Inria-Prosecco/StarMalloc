module ArrayAlignment

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module A = Steel.Array

let array (a: Type) = Steel.ST.Array.array a
let ptr (a: Type) = Steel.ST.Array.ptr a

noextract
unfold let same_base_array (#a: Type) (arr1 arr2: array a)
  =
  A.base (A.ptr_of arr1) == A.base (A.ptr_of arr2)

/// src/ArrayAlignment.fst contains axiomatization of array alignments.

// abstract property that the underlying pointer v-bytes aligned
assume val array_u8_alignment (arr: array U8.t) (v: U32.t{U32.v v > 0}): prop

// no model for the memory considered as the "root" array in a tree-like representation
// thus, this *axiom* is required
// to convey that if arr (of type uint8_t*) is v1-bytes aligned,
// that v1 is a multiple of v2,
// then forall k,
// then arr[k * v2] is v2-bytes aligned
assume val array_u8_alignment_lemma
  (arr1 arr2: array U8.t)
  (v1 v2: (v:U32.t{U32.v v > 0}))
  : Lemma
  (requires
    same_base_array arr1 arr2 /\
    array_u8_alignment arr1 v1 /\
    (U32.v v1) % (U32.v v2) == 0 /\
    (A.offset (A.ptr_of arr2) - A.offset (A.ptr_of arr1)) % (U32.v v2) == 0)
  (ensures
    array_u8_alignment arr2 v2)
