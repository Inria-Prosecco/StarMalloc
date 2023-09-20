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
module I64 = FStar.Int64

noextract inline_for_extraction
let array = Steel.ST.Array.array

open Config
open Utils2

//TODO: add a static assert about avl_data_size_aux bound
assume val avl_data_size_aux : v:U32.t{U32.v v <= 64}

let avl_data_size : v:sc{U32.v avl_data_size_aux <= U32.v v} = 64ul

open SizeClass
open Main

inline_for_extraction noextract
val init_avl_scs (slab_region: array U8.t)
  : Steel (size_class_struct)
  (A.varray slab_region)
  (fun r -> size_class_vprop r)
  (requires fun h0 ->
    A.is_full_array slab_region /\
    A.length slab_region = US.v metadata_max `FStar.Mul.op_Star` U32.v Config.page_size /\
    array_u8_proper_alignment slab_region /\
    zf_u8 (A.asel slab_region h0)
  )
  (ensures fun _ r _ ->
    r.size = avl_data_size /\
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
    scs: v:size_class_struct{
      v.size = avl_data_size /\
      v.slab_region == A.split_r slab_region 0sz /\
      A.is_full_array v.slab_region
    };
    lock : L.lock (
      size_class_vprop scs `star`
      A.varray (A.split_l slab_region 0sz)
    );
  }

let init_mmap_md_slabs (_:unit)
  : SteelTop mmap_md_slabs false (fun _ -> emp) (fun _ _ _ -> True)
  =
  let slab_region_size = US.mul metadata_max (US.uint32_to_sizet Config.page_size) in
  let slab_region = mmap_u8_init slab_region_size in
  A.ghost_split slab_region 0sz;
  A.ptr_base_offset_inj
    (A.ptr_of slab_region)
    (A.ptr_of (A.split_r slab_region 0sz));
  let scs = init_avl_scs (A.split_r slab_region 0sz) in
  let lock = L.new_lock (size_class_vprop scs `star` A.varray (A.split_l slab_region 0sz)) in
  return { slab_region; scs; lock; }

// intentional top-level effect for initialization
// corresponding warning temporarily disabled
#push-options "--warn_error '-272'"
let metadata_slabs : mmap_md_slabs = init_mmap_md_slabs ()
#pop-options

#restart-solver

type data = x: (array U8.t * US.t){
  (
    US.v (snd x) > 0 /\
    (enable_slab_canaries_malloc ==>
      A.length (fst x) == US.v (snd x) + 2) /\
    (not enable_slab_canaries_malloc ==>
      A.length (fst x) == US.v (snd x)) /\
    A.is_full_array (fst x)
  )
  \/
  US.v (snd x) == 0
}

let node = node data

module G = FStar.Ghost

assume val ref_node__to__array_u8_tot
  (x: ref node)
  : Pure (G.erased (array U8.t))
  (requires True)
  (ensures fun r ->
    A.is_null (G.reveal r) = is_null x /\
    A.length (G.reveal r) == U32.v avl_data_size
  )

assume val ref_node__to__array_u8
  (x: ref node)
  : Steel (array U8.t)
  (vptr x)
  (fun r -> A.varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ ->
    A.is_null r = is_null x /\
    A.length r == U32.v avl_data_size /\
    r == G.reveal (ref_node__to__array_u8_tot x)
  )

assume val array_u8__to__ref_node_tot
  (arr: array U8.t)
  : Pure (G.erased (ref node))
  (requires A.length arr == U32.v avl_data_size)
  (ensures fun r ->
    A.is_null arr = is_null (G.reveal r)
  )

assume val array_u8__to__ref_node
  (arr: array U8.t)
  : Steel (ref node)
  (A.varray arr)
  (fun r -> vptr r)
  (requires fun _ -> A.length arr == U32.v avl_data_size)
  (ensures fun _ r _ ->
    A.is_null arr = is_null r /\
    A.length arr == U32.v avl_data_size /\
    r == G.reveal (array_u8__to__ref_node_tot arr)
  )

//CAUTION
assume val array_u8__to__ref_node_bijectivity
  (ptr: array U8.t)
  : Lemma
  (requires A.length ptr == U32.v avl_data_size)
  (ensures (
    let x_cast1 = G.reveal (array_u8__to__ref_node_tot ptr) in
    let x_cast2 = G.reveal (ref_node__to__array_u8_tot x_cast1) in
    ptr == x_cast2
  ))

module UP = FStar.PtrdiffT

#push-options "--fuel 0 --ifuel 0"
let p : hpred data
  =
  G.hide (fun (x: ref node) ->
    let ptr = ref_node__to__array_u8_tot x in
    is_null x \/
    (same_base_array ptr metadata_slabs.scs.slab_region /\
    UP.fits (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of metadata_slabs.scs.slab_region)) /\
    A.offset (A.ptr_of ptr) - A.offset (A.ptr_of metadata_slabs.scs.slab_region) >= 0 /\
    ((A.offset (A.ptr_of ptr) - A.offset (A.ptr_of metadata_slabs.scs.slab_region)) % U32.v page_size) % U32.v metadata_slabs.scs.size = 0)
  )
#pop-options

let t = t data

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
