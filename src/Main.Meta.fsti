module Main.Meta

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT
module UP = FStar.PtrdiffT
module G = FStar.Ghost

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module A = Steel.Array
module AL = ArrayList
module SAA = Steel.ArrayArith
module L = Steel.SpinLock
module TLA = Steel.TLArray

open Prelude
open SlabsCommon
open SizeClass
open Main
open Mman
open Config
open Utils2
open NullOrVarray
open ROArray
open Main


/// The total number of size classes in the allocator, across all arenas.
/// Used as an abbreviation for specification purposes
inline_for_extraction noextract
val total_nb_sc: x:nat{US.fits x}

inline_for_extraction noextract
val arena_sc_list : (l:list sc{List.length l == total_nb_sc /\ Cons? l})

let sizes_t = r:TLA.t sc{
  TLA.length r == total_nb_sc /\
  (forall (k:US.t{US.v k < total_nb_sc}).
    TLA.get r k == List.Tot.index arena_sc_list (US.v k))
}

val sizes : sizes_t

/// This gathers all the data for small allocations.
/// In particular, it contains an array with all size_classes data,
/// as well as the slab_region containing the actual memory
noeq
type size_classes_all =
  { size_classes : sc:array size_class{length sc == total_nb_sc}; // The array of size_classes
    //sizes : sz:TLA.t sc{TLA.length sz == total_nb_sc}; // An array of the sizes of [size_classes]
    g_size_classes: Ghost.erased (Seq.lseq size_class (length size_classes)); // The ghost representation of size_classes
    //g_sizes: Ghost.erased (Seq.lseq sc (length sizes)); // The ghost representation of sizes
    ro_perm: ro_array size_classes g_size_classes; // The read-only permission on size_classes
    //ro_sizes: ro_array sizes g_sizes;
    slab_region: arr:array U8.t{ // The region of memory handled by this size class
      synced_sizes total_nb_sc sizes g_size_classes /\
      A.length arr == US.v slab_region_size /\
      (forall (i:nat{i < Seq.length g_size_classes}).
        size_class_pred arr (Seq.index g_size_classes i) i)
    }
  }

val sc_all : size_classes_all

module T = FStar.Tactics

/// A variant of the normalization, with a zeta full to reduce under
/// matches (and if/then/else). To use with care, as zeta_full can
/// loop and lead to stack overflows
noextract
let norm_full () : T.Tac unit =
  T.norm [zeta_full; iota; primops; delta_attr [`%reduce_attr]];
  T.trefl ()

[@@ T.postprocess_with norm_full]
val slab_malloc
  (arena_id: US.t{US.v arena_id < US.v nb_arenas})
  (bytes: U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
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

[@@ T.postprocess_with norm_full]
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
