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

#set-options "--ide_id_info_off"

// machine representation
inline_for_extraction noextract
unfold
let linked_tree = Impl.Core.linked_tree #data

noextract inline_for_extraction
let mmap = Mman.mmap_noinit

noextract inline_for_extraction
let munmap = Mman.munmap

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

module L = Steel.SpinLock

noeq
type mmap_md =
  {
    data: ref t;
    lock : L.lock (ind_linked_wf_tree data);
  }

let init_mmap_md (_:unit)
  : SteelTop mmap_md false (fun _ -> emp) (fun _ _ _ -> True)
  =
  let ptr = mmap_ptr_metadata () in
  let tree = create_leaf () in
  write ptr tree;
  (**) intro_vrefine (linked_tree tree) is_wf;
  (**) intro_vdep (vptr ptr) (linked_wf_tree tree) linked_wf_tree;
  let lock = L.new_lock (ind_linked_wf_tree ptr) in
  { data=ptr; lock=lock }

// intentional top-level effect for initialization
// corresponding warning temporarily disabled
#push-options "--warn_error '-272'"
let metadata : mmap_md = init_mmap_md ()
#pop-options

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
inline_for_extraction noextract
let large_malloc_aux
  (metadata_ptr: ref t)
  (size: US.t)
  : Steel (array U8.t)
  (
    //vptr metadata_ptr `star`
    //linked_tree metadata
    ind_linked_wf_tree metadata_ptr
  )
  (fun r ->
    //null_or_varray r `star`
    A.varray r `star`
    ind_linked_wf_tree metadata_ptr
    //vptr metadata_ptr `star`
    //linked_tree metadata
  )
  (requires fun h0 ->
    let blob0
      : t_of (ind_linked_wf_tree metadata_ptr)
      = h0 (ind_linked_wf_tree metadata_ptr) in
    let t : wdm data = dsnd blob0 in
    Spec.size_of_tree t < c /\
    US.v size > 0
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
    A.length r == US.v size /\
    A.is_full_array r /\
    A.asel r h1 == Seq.create (US.v size) U8.zero /\
    Spec.is_avl (spec_convert cmp) t /\
    (not (A.is_null r) ==> (
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
  //TODO: improve null_or_varray (should be the result of mmap)
  let ptr = mmap size in
  if (A.is_null ptr) then (
    (**) intro_vrefine (linked_tree md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    //TODO: improve null_or_varray
    sladmit ();
    return (A.null #U8.t)
  ) else (
    let b = mem md_v (ptr, size) in
    if b then (
      //TODO: add a die()
      sladmit ();
      return (A.null #U8.t)
    ) else (
      A.varrayp_not_null ptr P.full_perm;
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
      A.is_full_array ptr /\
      Spec.mem (spec_convert cmp) t
        (ptr, US.uint_to_t (A.length ptr)) /\
      not (Spec.mem (spec_convert cmp) t'
        (ptr, US.uint_to_t (A.length ptr)))
    ) /\
    True
    //not b ==> (
    //  //TODO: refine find
    //  //not (Spec.mem (spec_convert cmp) t
    //  //  (ptr, US.uint_to_t (A.length ptr))) /\
    //  blob0 == blob1
    //)
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
    let b = munmap ptr size in
    change_equal_slprop
      (if b then A.varray ptr else emp)
      (if (not b) then emp else A.varray ptr);
    if b then (
      //TODO: die(), munmap has failed, something must be wrong
      (**) intro_vrefine (linked_tree md_v) is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
      // return false
      return (not b)
    ) else (
      let h0 = get () in
      let md_v' = delete md_v (ptr, size) in
      Spec.lemma_delete (spec_convert cmp) (v_linked_tree md_v h0) (ptr, size);
      Spec.lemma_delete2 (spec_convert cmp) (v_linked_tree md_v h0) (ptr, size) (fun x -> US.v (snd x) <> 0);
      write metadata_ptr md_v';
      (**) intro_vrefine (linked_tree md_v') is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v') linked_wf_tree;
      // return true
      return (not b)
    )
  ) else (
    (**) intro_vrefine (linked_tree md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    let b = false in
    change_equal_slprop
      (A.varray ptr)
      (if b then emp else A.varray ptr);
    return b
  )
#pop-options

let large_malloc (size: US.t)
  : Steel (array U8.t)
  emp (fun r -> if A.is_null r then emp else A.varray r)
  (requires fun _ -> US.v size > 0)
  (ensures fun _ r _ ->
    not (A.is_null r) ==> A.length r == US.v size
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
    A.varrayp_not_null ptr P.full_perm;
    change_equal_slprop
      (A.varray ptr)
      (if A.is_null ptr then emp else A.varray ptr);
    return ptr
  ) else (
    L.release metadata.lock;
    [@inline_let] let r = A.null #U8.t in
    change_equal_slprop
      emp
      (if A.is_null r then emp else A.varray r);
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
    (US.v r > 0 ==> A.length ptr == US.v r)
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
    (US.v r > 0 ==> A.length ptr == US.v r)
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
