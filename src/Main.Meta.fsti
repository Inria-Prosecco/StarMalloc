module Main.Meta

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT
module G = FStar.Ghost
module L = FStar.List.Tot

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module A = Steel.Array
module TLA = Steel.TLArray

open Prelude
open Constants
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
val total_nb_sc: x:nat{
  US.fits x
}

open FStar.Mul
val total_nb_sc_lemma (_: unit)
  : Lemma
  (total_nb_sc == US.v nb_size_classes * US.v nb_arenas)

inline_for_extraction noextract
val arena_sc_list : (l:list sc{List.length l == total_nb_sc /\ Cons? l})

val sizes_t_pred (r: TLA.t sc) : prop

unfold type sizes_t = r:TLA.t sc{
  TLA.length r == total_nb_sc /\
  sizes_t_pred r
}

val sizes_t_pred_elim (r: sizes_t)
  : Lemma
  (
    (forall (k:US.t{US.v k < total_nb_sc}).
      TLA.get r k == L.index arena_sc_list (US.v k) /\
      TLA.get r k == L.index sc_list (US.v k % US.v nb_size_classes))
  )

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

inline_for_extraction noextract
val slab_malloc_one (i:US.t{US.v i < total_nb_sc}) (bytes: U32.t)
  : Steel
  (array U8.t)
  emp (fun r -> null_or_varray r)
  (requires fun _ ->
    U32.v bytes <= U32.v (Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size
  )
  (ensures fun _ r _ ->
    let size = (Seq.index sc_all.g_size_classes (US.v i)).data.size in
    U32.v size > 0 /\
    not (is_null r) ==> (
      A.length r == U32.v (Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size /\
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16ul /\
      ((U32.v page_size) % (U32.v size) == 0 ==> array_u8_alignment r size)
    )
  )

inline_for_extraction noextract
val set_canary
  (ptr: array U8.t)
  (size: sc)
  : Steel unit
  (null_or_varray ptr) (fun _ -> null_or_varray ptr)
  (requires fun _ ->
    not (is_null ptr) ==> A.length ptr = U32.v size)
  (ensures fun _ _ h1 ->
    let s : t_of (null_or_varray ptr)
      = h1 (null_or_varray ptr) in
    not (is_null ptr) ==> (
      Seq.length s >= 2 /\
      Seq.index s (A.length ptr - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length ptr - 1) == slab_canaries_magic2
    )
  )

module T = FStar.Tactics

/// A variant of the normalization, with a zeta full to reduce under
/// matches (and if/then/else). To use with care, as zeta_full can
/// loop and lead to stack overflows
noextract
let norm_full () : T.Tac unit =
  T.norm [zeta_full; iota; primops; delta_attr [`%reduce_attr]];
  T.trefl ()

[@@ T.postprocess_with norm_full]
inline_for_extraction noextract
val slab_malloc_generic_nocanary
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  bytes
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
      Seq.length s >= 2
    )
  )

[@@ T.postprocess_with norm_full]
inline_for_extraction noextract
val slab_malloc_generic_canary
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  bytes
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
      Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length r - 1) == slab_canaries_magic2
    )
  )

[@@ T.postprocess_with norm_full]
inline_for_extraction noextract
val slab_aligned_alloc_generic_nocanary
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (alignment: (v:U32.t{U32.v v > 0 /\ (U32.v page_size) % (U32.v v) = 0}))
  bytes
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
      array_u8_alignment r alignment /\
      Seq.length s >= 2
    )
  )

[@@ T.postprocess_with norm_full]
inline_for_extraction noextract
val slab_aligned_alloc_generic_canary
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (alignment: (v:U32.t{U32.v v > 0 /\ (U32.v page_size) % (U32.v v) = 0}))
  bytes
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
      array_u8_alignment r alignment /\
      Seq.length s >= 2 /\
      Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length r - 1) == slab_canaries_magic2
    )
  )
