module Impl.Trees.Cast.M

module US = FStar.SizeT
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64

module R = Steel.Reference
module A = Steel.Array
open Steel.Effect.Atomic
open Steel.Effect

module G = FStar.Ghost

open Constants
open Utils2

/// lib_avl_mono/Impl.Trees.Cast.M.fst contains axiomatization that is required to reuse the slab allocator for the allocation of the large allocation metadata AVL tree's nodes. In particular, it consists mostly of corresponding casts.

// this is a compilation-time assert, see c/utils.c static_assert usage
assume val avl_data_size_aux : v:U32.t{U32.v v <= 64}

let avl_data_size : v:sc{U32.v avl_data_size_aux <= U32.v v} = 64ul

type data = x: (array U8.t * US.t){
  (
    US.v (snd x) > 0 /\
    US.v (snd x) > U32.v max_slab_size /\
    A.length (fst x) == US.v (snd x) /\
    A.is_full_array (fst x)
  )
  \/
  US.v (snd x) == 0
}

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
    forall (x y: data). I64.v (f x y) == 0 ==> fst x == fst y
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
