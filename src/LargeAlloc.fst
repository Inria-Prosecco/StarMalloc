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

module P = Steel.FractionalPermission

open Impl.Mono
open Map.M
open Impl.Core
open Impl.Trees.Types

open Utils2
open NullOrVarray

#set-options "--ide_id_info_off"

open Steel.Reference

// is well-formed (AVL + content)
let is_wf (x: wdm data) : prop
  =
  (Spec.is_avl (spec_convert cmp) x &&
  Spec.forall_keys x (fun x -> US.v (snd x) <> 0))
  == true

let linked_wf_tree (tree: t)
  = linked_tree tree `vrefine` is_wf

let ind_linked_wf_tree (metadata: ref t)
  = vptr metadata `vdep` linked_wf_tree

assume val mmap_ptr_metadata (_:unit)
  : SteelT (ref t)
  emp
  (fun r -> vptr r)

open Config

//assume val get_sizeof_avl_data_as_bytes (_:unit) : sc

//assume val get_sizeof_avl_data_as_bytes (_:unit)
//  : Pure US.t
//  (requires True)
//  (fun r ->
//    US.v r <= FStar.UInt.max_int 32 /\
//    US.v r == 16 \/
//    US.v r == 32 \/
//    (
//      US.v r <= 64 /\
//      US.v r <= U32.v page_size /\
//      (U32.v page_size) % (US.v r) == 0
//    )
//  )

assume val avl_data_size : sc
//= get_sizeof_avl_data_as_bytes ()

open SizeClass
open Main

inline_for_extraction noextract
val init_avl_scs (_:unit)
  : Steel (size_class_struct)
  emp
  (fun r -> size_class_vprop r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> r.size = avl_data_size)

let init_avl_scs (_:unit)
  =
  let slab_region_size = US.mul metadata_max (US.uint32_to_sizet Config.page_size) in
  let md_bm_region_size = US.mul metadata_max 4sz in
  let md_region_size = metadata_max in
  let slab_region = mmap_u8 slab_region_size in
  let md_bm_region = mmap_u64 md_bm_region_size in
  let md_region = mmap_cell_status md_region_size in
  let scs = init_struct_aux avl_data_size slab_region md_bm_region md_region in
  return scs

let avl_vprop (metadata: ref t) (scs: size_class_struct)
  = ind_linked_wf_tree metadata `star` size_class_vprop scs

module L = Steel.SpinLock

noeq
type mmap_md =
  {
    data: ref t;
    scs: v:size_class_struct{v.size = avl_data_size};
    lock : L.lock (ind_linked_wf_tree data);
    lock2 : L.lock (size_class_vprop scs);
  }

let init_mmap_md (_:unit)
  : SteelTop mmap_md false (fun _ -> emp) (fun _ _ _ -> True)
  =
  let ptr = mmap_ptr_metadata () in
  let tree = create_leaf () in
  let scs = init_avl_scs () in
  write ptr tree;
  (**) intro_vrefine (linked_tree tree) is_wf;
  (**) intro_vdep (vptr ptr) (linked_wf_tree tree) linked_wf_tree;
  let lock = L.new_lock (ind_linked_wf_tree ptr) in
  let lock2 = L.new_lock (size_class_vprop scs) in
  //change_equal_slprop
  //  (ind_linked_wf_tree ptr `star` size_class_vprop scs)
  //  (avl_vprop ptr scs);
  //let lock = L.new_lock (avl_vprop ptr scs) in
  { data=ptr; scs=scs; lock=lock; lock2=lock2 }

// intentional top-level effect for initialization
// corresponding warning temporarily disabled
#push-options "--warn_error '-272'"
let metadata : mmap_md = init_mmap_md ()
#pop-options

open Steel.Reference

//TODO: discussion with Aymeric and Jonathan
//generalizing the slabs allocator type should allow
//to remove this cast
//but polymorphic assumes are unsupported
assume val array_u8__to__ref_node
  (arr: array U8.t)
  : Steel (ref node)
  (A.varray arr)
  (fun r -> vptr r)
  (requires fun _ -> A.length arr >= U32.v avl_data_size)
  (ensures fun _ r _ ->
    A.is_null arr = is_null r
  )

let trees_malloc2 (x: node)
  : Steel (ref node)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))
  =
  L.acquire metadata.lock2;
  let r = SizeClass.allocate_size_class metadata.scs in
  if A.is_null r
  then (
    // this should trigger a fatal error
    sladmit ();
    L.release metadata.lock2;
    return null
  ) else (
    change_equal_slprop
      (if (A.is_null r) then emp else A.varray r)
      (A.varray r);
    let r' = array_u8__to__ref_node r in
    L.release metadata.lock2;
    write r' x;
    return r'
  )

let trees_free2 (r: ref node)
  : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
  =
  sladmit ()

// machine representation
inline_for_extraction noextract
unfold
let linked_tree = Impl.Core.linked_tree #data

noextract inline_for_extraction
let mmap = Mman.mmap_noinit

noextract inline_for_extraction
let munmap = Mman.munmap_u8

let create_leaf = Impl.Trees.M.create_leaf

inline_for_extraction noextract
let insert = Impl.Mono.insert_avl trees_malloc2 trees_free2
inline_for_extraction noextract
let delete = Impl.Mono.delete_avl trees_malloc2 trees_free2

inline_for_extraction noextract
let get_size = Impl.Mono.sot_wds
//let mem = Impl.Mono.member
inline_for_extraction noextract
let find = Map.M.find

#restart-solver

open Config

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
inline_for_extraction noextract
let large_malloc_aux
  (metadata_ptr: ref t)
  (size: US.t)
  : Steel (array U8.t)
  (
    ind_linked_wf_tree metadata_ptr
  )
  (fun r ->
    null_or_varray r `star`
    ind_linked_wf_tree metadata_ptr
  )
  (requires fun h0 ->
    let blob0
      : t_of (ind_linked_wf_tree metadata_ptr)
      = h0 (ind_linked_wf_tree metadata_ptr) in
    let t : wdm data = dsnd blob0 in
    Spec.size_of_tree t < c /\
    US.v size > 0 /\
    (enable_slab_canaries_malloc ==> US.fits (US.v size + 2))
  )
  (ensures fun h0 r h1 ->
    let blob0
      : t_of (ind_linked_wf_tree metadata_ptr)
      = h0 (ind_linked_wf_tree metadata_ptr) in
    let t : wdm data = dsnd blob0 in
    let blob1
      : t_of (ind_linked_wf_tree metadata_ptr)
      = h1 (ind_linked_wf_tree metadata_ptr) in
    let t' : wdm data = dsnd blob1 in
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    Spec.is_avl (spec_convert cmp) t /\
    (not (A.is_null r) ==> (
      (enable_slab_canaries_malloc ==> A.length r == US.v size + 2) /\
      (not enable_slab_canaries_malloc ==> A.length r == US.v size) /\
      A.is_full_array r /\
      zf_u8 s /\
      not (Spec.mem (spec_convert cmp) t (r, size)) /\
      Spec.mem (spec_convert cmp) t' (r, size)
    ))
  )
  =
  (**) let t = elim_vdep (vptr metadata_ptr) linked_wf_tree in
  (**) elim_vrefine (linked_tree t) is_wf;
  let md_v = read metadata_ptr in
  (**) change_equal_slprop
    (linked_tree t)
    (linked_tree md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree md_v h0);
  let size' = if enable_slab_canaries_malloc then US.add size 2sz else size in
  let ptr = mmap size' in
  if (A.is_null ptr) then (
    (**) intro_vrefine (linked_tree md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    return ptr
  ) else (
    let b = mem md_v (ptr, size) in
    if b then (
      (**) intro_vrefine (linked_tree md_v) is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
      //TODO: add a die()
      drop (null_or_varray ptr);
      let r = intro_null_null_or_varray #U8.t in
      return r
    ) else (
      let h0 = get () in
      let md_v' = insert false md_v (ptr, size) in
      Spec.lemma_insert false (spec_convert cmp) (v_linked_tree md_v h0) (ptr, size);
      Spec.lemma_insert2 (spec_convert cmp) (v_linked_tree md_v h0) (ptr, size) (fun x -> US.v (snd x) <> 0);
      write metadata_ptr md_v';
      (**) intro_vrefine (linked_tree md_v') is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v') linked_wf_tree;
      return ptr
    )
  )

inline_for_extraction noextract
let _size (metadata: ref t) : Steel U64.t
  (ind_linked_wf_tree metadata)
  (fun _ -> ind_linked_wf_tree metadata)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let blob0 : t_of (ind_linked_wf_tree metadata)
      = h0 (ind_linked_wf_tree metadata) in
    let t : wdm data = dsnd blob0 in
    h1 (ind_linked_wf_tree metadata)
    ==
    h0 (ind_linked_wf_tree metadata) /\
    U64.v r == Spec.size_of_tree t
  )
  =
  (**) let t = elim_vdep (vptr metadata) linked_wf_tree in
  (**) elim_vrefine (linked_tree t) is_wf;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree t)
    (linked_tree md_v);
  let size = get_size md_v in
  (**) intro_vrefine (linked_tree md_v) is_wf;
  (**) intro_vdep (vptr metadata) (linked_wf_tree md_v) linked_wf_tree;
  return size

#restart-solver

inline_for_extraction noextract
let large_free_aux
  (metadata_ptr: ref t)
  (ptr: array U8.t)
  : Steel bool
  (
    A.varray ptr `star`
    ind_linked_wf_tree metadata_ptr
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    ind_linked_wf_tree metadata_ptr
  )
  (requires fun h0 -> True)
  (ensures fun h0 b h1 ->
    let blob0
      : t_of (ind_linked_wf_tree metadata_ptr)
      = h0 (ind_linked_wf_tree metadata_ptr) in
    let t : wdm data = dsnd blob0 in
    let blob1
      : t_of (ind_linked_wf_tree metadata_ptr)
      = h1 (ind_linked_wf_tree metadata_ptr) in
    let t' : wdm data = dsnd blob1 in
    b ==> (
      US.fits (A.length ptr) /\
      A.length ptr >= 2 /\
      A.is_full_array ptr /\
      (let size = if enable_slab_canaries_malloc
        then US.uint_to_t (A.length ptr - 2)
        else US.uint_to_t (A.length ptr) in
        Spec.mem (spec_convert cmp) t
          (ptr, size) /\
        not (Spec.mem (spec_convert cmp) t'
          (ptr, size))
      )
    ) /\
    not b ==> (
      not (Spec.mem (spec_convert cmp) t
        (ptr, 0sz)) /\
      blob0 == blob1
    )
  )
  =
  (**) let t = elim_vdep (vptr metadata_ptr) linked_wf_tree in
  (**) elim_vrefine (linked_tree t) is_wf;
  let md_v = read metadata_ptr in
  (**) change_equal_slprop
    (linked_tree t)
    (linked_tree md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree md_v h0);
  let k_elem : data = (ptr, 0sz) in
  let size = find md_v k_elem in
  if Some? size then (
    let size = Some?.v size in
    A.length_fits ptr;
    assert (US.fits (A.length ptr));
    assert (
      (enable_slab_canaries_malloc ==>
        A.length ptr == US.v size + 2) /\
      (not enable_slab_canaries_malloc ==>
        A.length ptr == US.v size)
    );
    let size' = if enable_slab_canaries_malloc
      then US.add size 2sz
      else size in
    munmap ptr size';
    let h0 = get () in
    let md_v' = delete md_v (ptr, size) in
    Spec.lemma_delete (spec_convert cmp) (v_linked_tree md_v h0) (ptr, size);
    Spec.lemma_delete2 (spec_convert cmp) (v_linked_tree md_v h0) (ptr, size) (fun x -> US.v (snd x) <> 0);
    write metadata_ptr md_v';
    (**) intro_vrefine (linked_tree md_v') is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v') linked_wf_tree;
    [@inline_let] let b = true in
    change_equal_slprop
      emp
      (if b then emp else A.varray ptr);
    return b
  ) else (
    (**) intro_vrefine (linked_tree md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    [@inline_let] let b = false in
    change_equal_slprop
      (A.varray ptr)
      (if b then emp else A.varray ptr);
    return b
  )
#pop-options

let large_malloc (size: US.t)
  : Steel (array U8.t)
  emp
  (fun ptr -> null_or_varray ptr)
  (requires fun _ ->
    US.v size > 0 /\
    (enable_slab_canaries_malloc ==> US.fits (US.v size + 2)))
  (ensures fun _ ptr h1 ->
    let s : (t_of (null_or_varray ptr))
      = h1 (null_or_varray ptr) in
    not (A.is_null ptr) ==> (
      (enable_slab_canaries_malloc ==> A.length ptr == US.v size + 2) /\
      (not enable_slab_canaries_malloc ==> A.length ptr == US.v size) /\
      A.is_full_array ptr /\
      zf_u8 s
    )
  )
  =
  L.acquire metadata.lock;
  let md_size = _size metadata.data in
  [@inline_let] let max = 18446744073709551615UL in
  assert (U64.v max = Impl.Core.c);
  if U64.lt md_size max then (
    //TODO: large_malloc' can return NULL due to mmap
    let ptr = large_malloc_aux metadata.data size in
    L.release metadata.lock;
    return ptr
  ) else (
    L.release metadata.lock;
    let r = intro_null_null_or_varray #U8.t in
    return r
  )

let large_free (ptr: array U8.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  L.acquire metadata.lock;
  let b = large_free_aux metadata.data ptr in
  L.release metadata.lock;
  return b

let large_getsize_aux (metadata: ref t) (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr `star` ind_linked_wf_tree metadata)
  (fun _ -> A.varray ptr `star` ind_linked_wf_tree metadata)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    h1 (ind_linked_wf_tree metadata)
    ==
    h0 (ind_linked_wf_tree metadata) /\
    (US.v r > 0 ==>
      (enable_slab_canaries_malloc ==> A.length ptr == US.v r + 2) /\
      (not enable_slab_canaries_malloc ==> A.length ptr == US.v r)
    )
  )
  =
  (**) let t = elim_vdep (vptr metadata) linked_wf_tree in
  (**) elim_vrefine (linked_tree t) is_wf;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree t)
    (linked_tree md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree md_v h0);
  let size = find md_v (ptr, 0sz) in
  if Some? size then (
    let size = Some?.v size in
    (**) intro_vrefine (linked_tree md_v) is_wf;
    (**) intro_vdep (vptr metadata) (linked_wf_tree md_v) linked_wf_tree;
    return size
  ) else (
    (**) intro_vrefine (linked_tree md_v) is_wf;
    (**) intro_vdep (vptr metadata) (linked_wf_tree md_v) linked_wf_tree;
    return 0sz
  )

let large_getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr) (fun _ -> A.varray ptr)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    (US.v r > 0 ==>
      (enable_slab_canaries_malloc ==> A.length ptr == US.v r + 2) /\
      (not enable_slab_canaries_malloc ==> A.length ptr == US.v r)
    )
  )
  =
  L.acquire metadata.lock;
  let size = large_getsize_aux metadata.data ptr in
  L.release metadata.lock;
  return size


(*)
- mmap/munmap: some improvements ahead? (better spec)
  - mmap can fail -> null_or_varray instead of varray
    - add a check in malloc
    - what about initialization? could be a bit cumbersome...
  - munmap better modelization
- convert AVL lib to use size_t instead of u64

- find: some improvements ahead? (better spec)
- use a large vdep between avl and mmap'ed allocations?
