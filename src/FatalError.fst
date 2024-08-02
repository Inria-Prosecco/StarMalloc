module FatalError

open Steel.Effect.Atomic
open Steel.Effect
module U8 = FStar.UInt8
module A = Steel.Array
module R = Steel.Reference

module G = FStar.Ghost

open Config
open Utils2
open NullOrVarray

/// src/FatalError.fst contains context-specific wrappers of the C fatal_error function.

open Impl.Trees.Cast.M
open Impl.Trees.Types

// caller: LargeAlloc.trees_malloc2_aux
assume val die_from_avl_node_malloc_failure (x: node) (ptr: array U8.t)
  : Steel (R.ref node)
  (if A.is_null ptr then emp else A.varray ptr)
  (fun r -> R.vptr r)
  (requires fun _ ->
    A.is_null ptr
  )
  (ensures fun _ r h1 ->
    R.sel r h1 == x /\
    not (R.is_null r) /\
    (G.reveal pred) r
  )

// caller: LargeAlloc.trees_free2_aux
assume val die_from_avl_node_free_failure (ptr: array U8.t)
  : SteelT unit
  (A.varray ptr)
  (fun _ -> emp)

// callers: StarMalloc.{malloc,calloc}
assume val die_from_malloc_zeroing_check_failure (ptr: array U8.t)
  : Steel unit
  (A.varray ptr)
  (fun _ -> emp)
  (requires fun _ -> enable_zeroing_malloc)
  (ensures fun _ _ _ -> True)

// caller: StarMalloc.realloc
assume val die_from_realloc_invalid_previous_alloc (ptr: array U8.t)
  : SteelT unit
  (A.varray ptr)
  (fun _ -> emp)

// caller: StarMalloc.realloc
assume val die_from_realloc_free_failure (ptr: array U8.t)
  : SteelT unit
  (A.varray ptr)
  (fun _ -> emp)
