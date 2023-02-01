module SizeClass

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module US = FStar.SizeT

module G = FStar.Ghost

module AL = ArrayList

module P = Steel.FractionalPermission
module SM = Steel.Memory
module A = Steel.Array

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

open Utils2
open Slabs

#push-options "--ide_id_info_off"

//TODO: remove blob, use ptrdiff style
//TODO: improve max_sc bound, use better spec'ed ffs64

open FStar.Mul
noeq
type size_class_struct' = {
  size: sc;
  // empty
  empty_slabs: ref US.t;
  // partial
  partial_slabs: ref US.t;
  // full
  full_slabs: ref US.t;
  md_count: ref U32.t;
  slab_region: array U8.t;
  //TODO: due to karamel extraction issue + sl proof workaround
  md_bm_region: array U64.t;
  md_region: array (AL.cell status);
  //lock: ref bool;
}

type size_class_struct = s:size_class_struct'{
  A.length s.slab_region == U32.v metadata_max * U32.v page_size /\
  A.length s.md_bm_region == U32.v metadata_max * 4 /\
  A.length s.md_region == U32.v metadata_max
}

[@@erasable]
noeq
type blob2 = {
  scs_v: size_class_struct;
  partial_slabs_v: US.t;
  empty_slabs_v: US.t;
  full_slabs_v: US.t;
  md_count_v: U32.t;
  slab_region_v: Seq.seq U8.t;
  md_bm_region_v: Seq.seq U64.t;
  md_region_v: Seq.seq (AL.cell status);
}

open SteelVRefineDep

let size_class_vprop
  (scs: size_class_struct)
  : vprop
  =
  vrefinedep
    (vptr scs.md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
       // left part
       left_vprop scs.size scs.slab_region scs.md_bm_region v scs.md_region
         scs.empty_slabs scs.partial_slabs scs.full_slabs `star`
       // right part
       right_vprop scs.slab_region scs.md_bm_region scs.md_region v)

let allocate_size_class_sl_lemma1
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (size_class_vprop scs)) m
  )
  (ensures
    SM.interp (hp_of (
      vrefinedep
        (vptr scs.md_count)
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
           // left part
           left_vprop scs.size scs.slab_region scs.md_bm_region v scs.md_region
             scs.empty_slabs scs.partial_slabs scs.full_slabs `star`
           // right part
           right_vprop scs.slab_region scs.md_bm_region scs.md_region v)
    )) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      vrefinedep
        (vptr scs.md_count)
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
           // left part
           left_vprop scs.size scs.slab_region scs.md_bm_region v scs.md_region
             scs.empty_slabs scs.partial_slabs scs.full_slabs `star`
           // right part
           right_vprop scs.slab_region scs.md_bm_region scs.md_region v)
    ) m
  )
  = ()

let allocate_size_class_sl_lemma2
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      vrefinedep
        (vptr scs.md_count)
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
           // left part
           left_vprop scs.size scs.slab_region scs.md_bm_region v scs.md_region
             scs.empty_slabs scs.partial_slabs scs.full_slabs `star`
           // right part
           right_vprop scs.slab_region scs.md_bm_region scs.md_region v)
    )) m
  )
  (ensures
    SM.interp (hp_of (size_class_vprop scs)) m /\
    sel_of (size_class_vprop scs) m
    ==
    sel_of (
      vrefinedep
        (vptr scs.md_count)
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
           // left part
           left_vprop scs.size scs.slab_region scs.md_bm_region v scs.md_region
             scs.empty_slabs scs.partial_slabs scs.full_slabs `star`
           // right part
           right_vprop scs.slab_region scs.md_bm_region scs.md_region v)
    ) m
  )
  = ()

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
let allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r ->
    (if (A.is_null r) then A.varray r else emp) `star`
    size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  change_slprop_rel
    (size_class_vprop_aux scs)
    (vrefinedep
      (vptr scs.md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         // left part
         left_vprop scs.size scs.slab_region scs.md_bm_region v scs.md_region
           scs.empty_slabs scs.partial_slabs scs.full_slabs `star`
         // right part
         right_vprop scs.slab_region scs.md_bm_region scs.md_region v))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  assume ((U32.v page_size) % (U32.v scs.size) == 0);
  let result = allocate_slab
    scs.size
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count
    scs.empty_slabs scs.partial_slabs scs.full_slabs in
  change_slprop_rel
    (vrefinedep
      (vptr scs.md_count)
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
         // left part
         left_vprop scs.size scs.slab_region scs.md_bm_region v scs.md_region
           scs.empty_slabs scs.partial_slabs scs.full_slabs `star`
         // right part
         right_vprop scs.slab_region scs.md_bm_region scs.md_region v))
    (size_class_vprop_aux scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  return result
