module Impl.Trees.Types

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

open Impl.Core

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

noextract inline_for_extraction
let array (a: Type) = Steel.ST.Array.array a

open Constants
open Config
open Utils2

open SizeClass
open Main

open Impl.Trees.Cast.M

inline_for_extraction noextract
let data = data

inline_for_extraction noextract
let node = node

inline_for_extraction noextract
let cmp = cmp

inline_for_extraction noextract
let avl_data_size = avl_data_size

inline_for_extraction noextract
val init_avl_scs (slab_region: array U8.t)
  : Steel (size_class_struct_sc)
  (A.varray slab_region)
  (fun r -> size_class_vprop_sc r)
  (requires fun h0 ->
    A.is_full_array slab_region /\
    A.length slab_region = US.v metadata_max `FStar.Mul.op_Star` U32.v page_size /\
    array_u8_alignment slab_region page_size /\
    zf_u8 (A.asel slab_region h0)
  )
  (ensures fun _ r _ ->
    get_u32 r.size = avl_data_size /\
    r.slab_region == slab_region /\
    A.is_full_array r.slab_region
  )

open Mman
let init_avl_scs (slab_region: array U8.t)
  =
  let md_bm_region_size = US.mul metadata_max 4sz in
  let md_region_size = metadata_max in
  let md_bm_region = mmap_u64_init md_bm_region_size in
  let md_region = mmap_cell_status_init md_region_size in
  let scs = init_struct_aux avl_data_size slab_region md_bm_region md_region in
  return scs

module L = Steel.SpinLock

noeq
type mmap_md_slabs =
  {
    slab_region: array U8.t;
    scs: v:size_class_struct_sc{
      get_u32 v.size = avl_data_size /\
      v.slab_region == A.split_r slab_region 0sz /\
      A.is_full_array v.slab_region
    };
    lock : L.lock (
      size_class_vprop_sc scs `star`
      A.varray (A.split_l slab_region 0sz)
    );
  }

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let init_mmap_md_slabs (_:unit)
  : SteelTop mmap_md_slabs false (fun _ -> emp) (fun _ _ _ -> True)
  =
  let slab_region = mmap_u8_init sc_slab_region_size in
  A.ghost_split slab_region 0sz;
  A.ptr_shift_zero (A.ptr_of slab_region);
  A.ptr_base_offset_inj
    (A.ptr_of slab_region)
    (A.ptr_of (A.split_r slab_region 0sz));
  assert (A.split_r slab_region 0sz == slab_region);
  let scs = init_avl_scs (A.split_r slab_region 0sz) in
  let lock = L.new_lock (size_class_vprop_sc scs `star` A.varray (A.split_l slab_region 0sz)) in
  return { slab_region; scs; lock; }
#pop-options

// intentional top-level effect for initialization
// corresponding warning temporarily disabled
#push-options "--warn_error '-272'"
let metadata_slabs : mmap_md_slabs = init_mmap_md_slabs ()
#pop-options

#restart-solver

module G = FStar.Ghost

module UP = FStar.PtrdiffT

#push-options "--fuel 0 --ifuel 0"
let p : hpred data
  =
  G.hide (fun (x: ref node) ->
    is_null x \/
    (not (is_null x) /\
      (let ptr = Impl.Trees.Cast.M.ref_node__to__array_u8_tot x in
      same_base_array ptr metadata_slabs.scs.slab_region /\
      UP.fits (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of metadata_slabs.scs.slab_region)) /\
      A.offset (A.ptr_of ptr) - A.offset (A.ptr_of metadata_slabs.scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of ptr) - A.offset (A.ptr_of metadata_slabs.scs.slab_region)) % U32.v page_size) % U32.v (get_u32 metadata_slabs.scs.size) = 0)
    )
  )
#pop-options

let t = x:(t data){(G.reveal p) x}

unfold type f_malloc
  = (x: node) -> Steel (ref node)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    sel r h1 == x /\
    not (is_null r) /\
    (G.reveal p) r
  )

unfold type f_free
  = (r: ref node) -> Steel unit
  (vptr r)
  (fun _ -> emp)
  (requires fun _ ->
    (G.reveal p) r
  )
  (ensures fun _ _ _-> True)
