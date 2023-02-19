module LargeAlloc

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8
module US = FStar.SizeT

let array = Steel.ST.Array.array

open Impl.Mono
open Map.M
open Impl.Core

#set-options "--ide_id_info_off"

// machine representation
unfold let a = Aux.a

let t = Impl.Core.t
unfold let linked_tree = Impl.Core.linked_tree #a

noextract inline_for_extraction
let mmap = Mman.mmap_s
  //= Mman.mmap 0UL len prot 33l (-1l) 0ul
  //MAP_PRIVATE instead of MAP_ANON (avoid filling the disk...)
  //34l = MAP_PRIVATE|MAP_ANON

let munmap (ptr: array U8.t) (size: US.t)
  : Steel bool
    (A.varray ptr)
    (fun b -> if b then emp else A.varray ptr)
    (requires fun _ ->
      //A.length a == U64.v size_t /\
      A.is_full_array ptr
    )
    (ensures fun _ _ _ -> True)
  = Mman.munmap ptr size

unfold let ptr_t = Aux.ptr_t
unfold let size_t = Aux.size_t
noextract
assume val ptr_to_u64 (x: ptr_t) : U64.t
noextract
assume val u64_to_ptr (x: U64.t) : ptr_t

let cmp (x y: a) : I64.t
  =
  let x = fst x in
  let y = fst y in
  let x = ptr_to_u64 x in
  let y = ptr_to_u64 y in
  if U64.gt x y then 1L
  else if U64.eq x y then 0L
  else -1L

let create_leaf = Impl.Trees.M.create_leaf

inline_for_extraction noextract
let insert = Impl.Mono.insert_avl
inline_for_extraction noextract
let delete = Impl.Mono.delete_avl

inline_for_extraction noextract
let get_size = Impl.Mono.sot_wds
//let mem = Impl.Mono.member
inline_for_extraction noextract
let find = Map.M.find

open Steel.Reference

let is_avl (x: wdm a) : prop
  = Spec.is_avl (spec_convert cmp) x == true

let linked_avl_tree (tree: t a)
  = linked_tree tree `vrefine` is_avl

let ind_linked_avl_tree (metadata: ref (t a))
  = vptr metadata `vdep` linked_avl_tree

assume
val mmap_ptr_metadata (_:unit)
  : SteelT (ref (t a))
  emp
  (fun r -> vptr r)

module L = Steel.SpinLock

noeq
type mmap_md =
  {
    data: ref (t a);
    lock : L.lock (ind_linked_avl_tree data);
  }

let init_mmap_md (_:unit)
  : SteelTop mmap_md false (fun _ -> emp) (fun _ _ _ -> True)
  =
  let ptr = mmap_ptr_metadata () in
  let tree = create_leaf () in
  write ptr tree;
  (**) intro_vrefine (linked_tree tree) is_avl;
  (**) intro_vdep (vptr ptr) (linked_avl_tree tree) linked_avl_tree;
  let lock = L.new_lock (ind_linked_avl_tree ptr) in
  { data=ptr; lock=lock }

// intentional top-level effect for initialization
// corresponding warning temporarily disabled
#push-options "--warn_error '-272'"
let metadata : mmap_md = init_mmap_md ()
#pop-options

let large_malloc' (metadata: ref (t a)) (size: size_t)
  : Steel (ptr_t)
  (ind_linked_avl_tree metadata)
  (fun r -> A.varray r `star` ind_linked_avl_tree metadata)
  (requires fun h0 ->
    let blob0 : t_of (ind_linked_avl_tree metadata)
      = h0 (ind_linked_avl_tree metadata) in
    let t : wdm a = dsnd blob0 in
    Spec.size_of_tree t < c
  )
  (ensures fun _ r h1 ->
    A.length r == U64.v size /\
    A.is_full_array r /\
    A.asel r h1 == Seq.create (U64.v size) U8.zero)
  =
  (**) let t = elim_vdep (vptr metadata) linked_avl_tree in
  (**) elim_vrefine (linked_tree t) is_avl;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree t)
    (linked_tree md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree md_v h0);
  assume (US.fits_u64);
  let size' = US.uint64_to_sizet size in
  let ptr = mmap size' in
  let md_v' = insert false cmp md_v (ptr, size) in
  write metadata md_v';
  (**) intro_vrefine (linked_tree md_v') is_avl;
  (**) intro_vdep (vptr metadata) (linked_avl_tree md_v') linked_avl_tree;
  return ptr

inline_for_extraction noextract
let _size (metadata: ref (t a)) : Steel U64.t
  (ind_linked_avl_tree metadata)
  (fun _ -> ind_linked_avl_tree metadata)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let blob0 : t_of (ind_linked_avl_tree metadata)
      = h0 (ind_linked_avl_tree metadata) in
    let t : wdm a = dsnd blob0 in
    h1 (ind_linked_avl_tree metadata)
    ==
    h0 (ind_linked_avl_tree metadata) /\
    U64.v r == Spec.size_of_tree t
  )
  =
  (**) let t = elim_vdep (vptr metadata) linked_avl_tree in
  (**) elim_vrefine (linked_tree t) is_avl;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree t)
    (linked_tree md_v);
  let size = get_size md_v in
  (**) intro_vrefine (linked_tree md_v) is_avl;
  (**) intro_vdep (vptr metadata) (linked_avl_tree md_v) linked_avl_tree;
  return size

let large_free' (metadata: ref (t a)) (ptr: ptr_t)
  : Steel bool
  (A.varray ptr `star` ind_linked_avl_tree metadata)
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    ind_linked_avl_tree metadata
  )
  (requires fun h0 -> A.is_full_array ptr)
  (ensures fun _ _ _ -> True)
  =
  (**) let t = elim_vdep (vptr metadata) linked_avl_tree in
  (**) elim_vrefine (linked_tree t) is_avl;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree t)
    (linked_tree md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree md_v h0);
  let size = find cmp md_v (ptr, 0UL) in
  if Some? size then (
    let size = Some?.v size in
    assume (US.fits_u64);
    let size' = US.uint64_to_sizet size in
    let b = munmap ptr size' in
    if b then (
      let md_v' = delete cmp md_v (ptr, size) in
      write metadata md_v';
      (**) intro_vrefine (linked_tree md_v') is_avl;
      (**) intro_vdep (vptr metadata) (linked_avl_tree md_v') linked_avl_tree;
      return b
    ) else (
      (**) intro_vrefine (linked_tree md_v) is_avl;
      (**) intro_vdep (vptr metadata) (linked_avl_tree md_v) linked_avl_tree;
      return b
    )
  ) else (
    (**) intro_vrefine (linked_tree md_v) is_avl;
    (**) intro_vdep (vptr metadata) (linked_avl_tree md_v) linked_avl_tree;
    let b = false in
    change_equal_slprop
      (A.varray ptr)
      (if b then emp else A.varray ptr);
    return b
  )

let large_malloc (size: size_t)
  : Steel (ptr_t)
  emp (fun r -> A.varray r)//if is_null r then emp else A.varray r)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  L.acquire metadata.lock;
  let md_size = _size metadata.data in
  //TODO: refine check with max size_t uint
  if U64.lte md_size 100UL then (
    //TODO: large_malloc' can return NULL due to mmap
    let ptr = large_malloc' metadata.data size in
    L.release metadata.lock;
    return ptr
  ) else (
    L.release metadata.lock;
    sladmit ();
    return (A.null #U8.t)
  )

let large_free (ptr: ptr_t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun _ -> A.is_full_array ptr)
  (ensures fun _ _ _ -> True)
  =
  L.acquire metadata.lock;
  let b = large_free' metadata.data ptr in
  L.release metadata.lock;
  return b

(*)
- mmap/munmap: some improvements ahead? (better spec)
  - mmap can fail -> null_or_varray instead of varray
    - add a check in malloc
    - what about initialization? could be a bit cumbersome...
  - munmap better modelization
- convert AVL lib to use size_t instead of u64

- find: some improvements ahead? (better spec)
- use a large vdep between avl and mmap'ed allocations?
