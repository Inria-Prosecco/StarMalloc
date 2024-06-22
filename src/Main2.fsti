module Main2

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT
module UP = FStar.PtrdiffT
module G = FStar.Ghost
module L = FStar.List.Tot

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module A = Steel.Array
module TLA = Steel.TLArray
module SAA = Steel.ArrayArith

open Constants
open Config
open Utils2
open NullOrVarray

open Main.Meta

val slab_malloc
  (arena_id: US.t{US.v arena_id < US.v nb_arenas})
  (bytes: U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ ->
    (enable_slab_canaries_malloc ==> U32.v bytes <= U32.v page_size - 2) /\
    (not enable_slab_canaries_malloc ==> U32.v bytes <= U32.v page_size)
  )
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16ul /\
      Seq.length s >= 2 /\
      (enable_slab_canaries_malloc ==>
        Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length r - 1) == slab_canaries_magic2
      )
    )
  )

val slab_aligned_alloc (arena_id:US.t{US.v arena_id < US.v nb_arenas}) (alignment:U32.t) (bytes:U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ ->
    U32.v alignment > 0 /\
    (U32.v page_size) % (U32.v alignment) = 0
  )
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    U32.v alignment > 0 /\
    (U32.v page_size) % (U32.v alignment) = 0 /\
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16ul /\
      array_u8_alignment r alignment /\
      Seq.length s >= 2 /\
      (enable_slab_canaries_malloc ==>
        Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length r - 1) == slab_canaries_magic2
      )
    )
  )

val within_size_classes_pred (ptr:A.array U8.t) : prop

inline_for_extraction noextract
let slab_region_size = Main.slab_region_size

val slab_getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (fun _ ->
   A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (requires fun _ ->
    within_size_classes_pred ptr /\
    SAA.within_bounds
      (A.split_l (G.reveal sc_all.slab_region) 0sz)
      ptr
      (A.split_r (G.reveal sc_all.slab_region) slab_region_size)
  )
  (ensures fun h0 r h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    (r <> 0sz ==>
      (enable_slab_canaries_malloc ==>
        A.length ptr == US.v r + 2
      ) /\
      (not enable_slab_canaries_malloc ==>
        A.length ptr == US.v r
      )
    )
  )

val slab_free (ptr:array U8.t)
  : Steel bool
  (A.varray ptr `star`
    A.varray (A.split_l sc_all.slab_region 0sz))
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    A.varray (A.split_l sc_all.slab_region 0sz))
  (requires fun _ ->
    within_size_classes_pred ptr /\
    SAA.within_bounds
      (A.split_l (G.reveal sc_all.slab_region) 0sz)
      ptr
      (A.split_r (G.reveal sc_all.slab_region) slab_region_size)
  )
  (ensures fun h0 r _ ->
    let s = A.asel ptr h0 in
    enable_slab_canaries_free ==>
      (r ==>
        A.length ptr >= 2 /\
        Seq.index s (A.length ptr - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length ptr - 1) == slab_canaries_magic2
      )
  )
