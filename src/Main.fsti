module Main

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

module TLA = Steel.TLArray

open FStar.Mul
open Steel.Effect.Atomic
open Steel.Effect
//open Steel.Array
module A = Steel.Array
//module R = Steel.Reference
//module L = Steel.SpinLock
module AL = ArrayList
//module ALG = ArrayListGen
//module SAA = Steel.ArrayArith

//open Prelude
//open SizeClass
//open SteelVRefineDep
//open SteelStarSeqUtils

//open Utils2
//open Mman

val metadata_max_ex: US.t
val slab_size: US.t
val sc_slab_region_size: US.t

open Constants
open Config
open SizeClass
open Utils2

noextract inline_for_extraction
val init_struct_aux
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region == U32.v page_size * US.v metadata_max})
  (md_bm_region: array U64.t{A.length md_bm_region == US.v 4sz * US.v metadata_max})
  (md_region: array AL.cell{A.length md_region == US.v metadata_max})
  : Steel size_class_struct_sc
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop_sc scs)
  (requires fun h0 ->
    array_u8_alignment slab_region page_size /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0)
  )
  (ensures fun _ r h1 ->
    r.size == Sc sc /\
    //zf_u8 (A.asel (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) (US.sub n 1sz))) h1) /\
    //zf_u64 (A.asel (A.split_l md_bm_region (US.mul (US.mul metadata_max 4sz) (US.sub n 1sz))) h1) /\
    r.slab_region == slab_region /\
    r.md_bm_region == md_bm_region /\
    r.md_region == md_region /\
    True
  )

/// An attribute, that will indicate that the annotated functions should be unfolded at compile-time
irreducible let reduce_attr : unit = ()

open Mman

//unfold
val size_class_pred (slab_region:array U8.t) (sc:size_class) (i:nat) : prop

module UP = FStar.PtrdiffT
val slab_region_size
  : v:US.t{
    US.v v == US.v metadata_max * U32.v page_size * US.v nb_size_classes * US.v nb_arenas /\
    UP.fits (US.v v)
  }


/// A logical predicate indicating that a list of sizes corresponds
/// to the sizes of a list of size_classes
val synced_sizes
  //(nb_arenas: US.t)
  //(n: US.t)
  (offset: US.t)
  (size_classes: Seq.seq size_class)
  (sizes:TLA.t sc_union)
  (k:nat{
    k <= Seq.length size_classes /\
    k + US.v offset <= TLA.length sizes
  })
  : prop

val hidden_pred
  (l1: list sc)
  (l2: list sc_ex)
  (n n1 n2 s1 s2 s3: US.t)
  : prop

val hidden_pred2
  (n s1: US.t)
  : prop

noextract inline_for_extraction
val init_all_arenas
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0 /\
    US.fits (US.v n * US.v nb_arenas) /\
    US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_region_size * US.v nb_arenas)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size * US.v nb_arenas
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size * US.v nb_arenas
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size * US.v nb_arenas
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size * US.v nb_arenas
  })
  (size_classes: array size_class{
    A.length size_classes == US.v n * US.v nb_arenas
  })
  (sizes: TLA.t sc_union{
    TLA.length sizes == US.v n * US.v nb_arenas
  })
  : Steel unit
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_bm_region_b `star`
    A.varray md_region `star`
    A.varray size_classes
  )
  (fun _ ->
    A.varray size_classes
  )
  (requires fun h0 ->
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size 0sz)) (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0) /\
    zf_b (A.asel md_bm_region_b h0) /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size /\
    hidden_pred2 n arena_slab_region_size /\
    US.fits (US.v n * US.v nb_arenas) /\
    True
  )
  (ensures fun _ _ h1 ->
    hidden_pred2 n arena_slab_region_size /\
    US.fits (US.v n * US.v nb_arenas) /\
    synced_sizes 0sz
      (A.asel size_classes h1) sizes (US.v nb_arenas * US.v n) /\
    (forall (i:nat{i < US.v nb_arenas * US.v n}).
      size_class_pred slab_region (Seq.index (A.asel size_classes h1) i) i
    ) /\
    True
  )

open NullOrVarray

inline_for_extraction noextract
val return_null ()
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> A.is_null r)

/// Wrapper around allocate_size_class, that does not return a pair, and instead
/// always returns a valid permission on the new pointer if it is not null
inline_for_extraction noextract
val allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r -> null_or_varray r `star` size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    not (A.is_null r) ==> (
      A.length r == U32.v (get_u32 scs.size) /\
      array_u8_alignment r 16ul /\
      ((U32.v (get_u32 scs.size) > 0 /\ (U32.v page_size) % (U32.v (get_u32 scs.size)) == 0) ==> array_u8_alignment r (get_u32 scs.size))
    )
  )
