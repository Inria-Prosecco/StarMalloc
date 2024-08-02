module Impl.Trees.Cast.M

module US = FStar.SizeT
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module FU = FStar.UInt

module R = Steel.Reference
module A = Steel.Array
open Steel.Effect.Atomic
open Steel.Effect

module G = FStar.Ghost

open Constants
open Utils2

/// lib_avl_mono/Impl.Trees.Cast.M.fst contains axiomatization that is required to reuse the slab allocator for the allocation of the large allocation metadata AVL tree's nodes. In particular, it consists mostly of corresponding casts.

// this is a compilation-time assert, see c/utils.c static_assert usage
assume val avl_data_size_aux : v:U32.t{U32.v v <= 128}

let avl_data_size : v:sc{U32.v avl_data_size_aux <= U32.v v} = 128ul

noeq
type data' = {
  //user_ptr = ptr + shift
  //if alignment > 0, then user_ptr is alignment-bytes aligned
  //size of ptr = size, thus size of user_ptr can be < size
  user_ptr: array U8.t;
  ptr: array U8.t;
  size: US.t;
  shift: US.t;
  alignment: U32.t;
}

let is_data (x: data')
  =
  (
    US.v x.size > 0 /\
    US.v x.size > U32.v page_size /\
    A.length x.ptr == US.v x.size /\
    A.is_full_array x.ptr /\
    US.v x.shift < US.v x.size /\
    x.user_ptr == A.split_r x.ptr x.shift /\
    (
      x.alignment = 0ul \/
      array_u8_alignment x.user_ptr x.alignment
    )
  )
  \/
  x.size = 0sz

type data = x:data'{is_data x}

open Impl.Core
let node = node data

// CAUTION:
// the refinement implies that the injectivity
// of the cast uint8_t* -> uintptr_t
// over:
// - valid pointers of large allocations
// (that is the set contained by the AVL tree)
// - those supplied by the user to free and realloc functions
// is part of the model
assume val cmp
  : f:Impl.Common.cmp data{
    forall (x y: data). I64.v (f x y) == 0 ==> x.user_ptr == y.user_ptr
  }

assume val ref_node__to__array_u8_tot
  (x: R.ref node)
  : Pure (G.erased (array U8.t))
  (requires not (R.is_null x))
  (ensures fun r ->
    not (A.is_null (G.reveal r)) /\
    A.length (G.reveal r) == U32.v avl_data_size
  )

assume val ref_node__to__array_u8
  (x: R.ref node)
  : Steel (array U8.t)
  (R.vptr x)
  (fun r -> A.varray r)
  (requires fun _ -> not (R.is_null x))
  (ensures fun _ r _ ->
    not (R.is_null x) /\
    not (A.is_null r) /\
    A.length r == U32.v avl_data_size /\
    r == G.reveal (ref_node__to__array_u8_tot x)
  )

assume val array_u8__to__ref_node_tot
  (arr: array U8.t)
  : Pure (G.erased (R.ref node))
  (requires A.length arr == U32.v avl_data_size)
  (ensures fun r ->
    not (R.is_null (G.reveal r))
  )

assume val array_u8__to__ref_node
  (arr: array U8.t)
  : Steel (R.ref node)
  (A.varray arr)
  (fun r -> R.vptr r)
  (requires fun _ -> A.length arr == U32.v avl_data_size)
  (ensures fun _ r _ ->
    not (R.is_null r) /\
    A.length arr == U32.v avl_data_size /\
    r == G.reveal (array_u8__to__ref_node_tot arr)
  )

assume val array_u8__to__ref_node_bijectivity
  (ptr: array U8.t)
  : Lemma
  (requires A.length ptr == U32.v avl_data_size)
  (ensures (
    let x_cast1 = G.reveal (array_u8__to__ref_node_tot ptr) in
    let x_cast2 = G.reveal (ref_node__to__array_u8_tot x_cast1) in
    ptr == x_cast2
  ))
