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
module G = FStar.Ghost

open Impl.Mono
open Map.M
open Impl.Core
open Impl.Trees.Types

open Prelude
open Utils2
open NullOrVarray

#set-options "--ide_id_info_off"

#push-options "--fuel 0 --ifuel 0"

open Steel.Reference

assume val mmap_ptr_metadata (_:unit)
  : SteelT (ref t)
  emp
  (fun r -> vptr r)

// is well-formed (AVL + content)
let is_wf (x: wdm data) : prop
  =
  (Spec.is_avl (spec_convert cmp) x &&
  Spec.forall_keys x (fun x -> US.v (snd x) <> 0))
  == true

let linked_wf_tree (tree: t)
  = linked_tree p tree `vrefine` is_wf

let ind_linked_wf_tree (metadata: ref t)
  = vptr metadata `vdep` linked_wf_tree

open Config

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
  (**) intro_vrefine (linked_tree p tree) is_wf;
  (**) intro_vdep (vptr ptr) (linked_wf_tree tree) linked_wf_tree;
  let lock = L.new_lock (ind_linked_wf_tree ptr) in
  return { data=ptr; lock=lock; }

// intentional top-level effect for initialization
// corresponding warning temporarily disabled
#push-options "--warn_error '-272'"
let metadata : mmap_md = init_mmap_md ()
#pop-options

open Steel.Reference

module UP = FStar.PtrdiffT

let up_fits_propagation (ptr1 ptr2: array U8.t)
  : Lemma
  (requires
    same_base_array ptr1 ptr2 /\
    UP.fits (A.base_len (A.base (A.ptr_of ptr1)))
  )
  (ensures
    UP.fits (A.length ptr1)
  )
  = ()

open SizeClass

open FStar.Mul

#push-options "--z3rlimit 50"
inline_for_extraction noextract
let trees_malloc2_aux (x: node)
  : Steel (ref node)
  (size_class_vprop metadata_slabs.scs)
  (fun r -> size_class_vprop metadata_slabs.scs `star` vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    sel r h1 == x /\
    not (is_null r) /\
    (G.reveal p) r
  )
  =
  let ptr = SizeClass.allocate_size_class metadata_slabs.scs in
  if A.is_null ptr
  then (
    // this should trigger a fatal error
    sladmit ();
    return null
  ) else (
    change_equal_slprop
      (if (A.is_null ptr) then emp else A.varray ptr)
      (A.varray ptr);
    metadata_max_up_fits ();
    FStar.Math.Lemmas.lemma_mult_le_left
      (US.v metadata_max * U32.v page_size)
      1
      (US.v nb_size_classes * US.v nb_arenas);
    assert
      (A.length metadata_slabs.scs.slab_region
      <=
      (US.v metadata_max * U32.v page_size) * US.v nb_size_classes * US.v nb_arenas);
    up_fits_propagation ptr metadata_slabs.scs.slab_region;
    let r' = array_u8__to__ref_node ptr in
    array_u8__to__ref_node_bijectivity ptr;
    write r' x;
    return r'
  )
#pop-options

open WithLock

let trees_malloc2 (x: node)
  : Steel (ref node)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    sel r h1 == x /\
    not (is_null r) /\
    (G.reveal p) r
  )
  =
  let r = with_lock
    unit
    unit
    (ref node)
    (fun v0 ->
      size_class_vprop metadata_slabs.scs `star`
      A.varray (A.split_l metadata_slabs.slab_region 0sz))
    (fun v1 -> emp)
    (fun _ r -> vptr r)
    ()
    ()
    metadata_slabs.lock
    (fun _ r (vr: t_of (vptr r)) ->
      x == vr /\
      not (is_null r) /\
      (G.reveal p) r
    )
    (fun _ -> trees_malloc2_aux x) 
  in
  return r

module UP = FStar.PtrdiffT

inline_for_extraction noextract
let trees_free2_aux (r: ref node)
  : Steel unit
  (
    size_class_vprop metadata_slabs.scs `star`
    A.varray (A.split_l metadata_slabs.slab_region 0sz) `star`
    vptr r
  )
  (fun _ ->
    size_class_vprop metadata_slabs.scs `star`
    A.varray (A.split_l metadata_slabs.slab_region 0sz)
  )
  (requires fun _ -> (G.reveal p) r)
  (ensures fun _ _ _-> True)
  =
  vptr_not_null r;
  let ptr = ref_node__to__array_u8 r in
  let diff = A.ptrdiff ptr (A.split_l metadata_slabs.slab_region 0sz) in
  let diff_sz = UP.ptrdifft_to_sizet diff in
  assert (US.v diff_sz = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of metadata_slabs.scs.slab_region));
  let b = SizeClass.deallocate_size_class metadata_slabs.scs ptr diff_sz in
  if b
  then (
    change_equal_slprop
      (if b then emp else A.varray ptr)
      emp;
    return ()
  ) else (
    // this should trigger a fatal error
    sladmit ();
    return ()
  )

let trees_free2 (r: ref node)
  : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> (G.reveal p) r)
  (ensures fun _ _ _-> True)
  =
  let r = with_lock
    unit
    (ref node)
    unit
    (fun v0 ->
      size_class_vprop metadata_slabs.scs `star`
      A.varray (A.split_l metadata_slabs.slab_region 0sz))
    (fun v1 -> vptr v1)
    (fun _ _ -> emp)
    ()
    r
    metadata_slabs.lock
    (fun _ _ _ -> True)
    (fun _ -> trees_free2_aux r)
  in
  return r

// machine representation
inline_for_extraction noextract
unfold
let linked_tree = Impl.Core.linked_tree #data

noextract inline_for_extraction
let mmap = Mman.mmap_u8

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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let mmap_actual_size (size: US.t)
  : Pure US.t
  (requires
    US.v size >= U32.v page_size /\
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun r ->
    US.v r == Mman.spec_mmap_actual_size (US.v size)
  )
  =
  let rem = US.rem size (u32_to_sz page_size) in
  if rem <> 0sz
  then US.add (US.sub size rem) (u32_to_sz page_size)
  else size
#pop-options

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
    US.fits (US.v size + U32.v page_size) /\
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
      array_u8_alignment r page_size /\
      zf_u8 s /\
      not (Spec.mem (spec_convert cmp) t (r, size)) /\
      Spec.mem (spec_convert cmp) t' (r, size)
    ))
  )
  =
  (**) let t = elim_vdep (vptr metadata_ptr) linked_wf_tree in
  (**) elim_vrefine (linked_tree p t) is_wf;
  let md_v = read metadata_ptr in
  (**) change_equal_slprop
    (linked_tree p t)
    (linked_tree p md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree p md_v h0);
  let size' = if enable_slab_canaries_malloc then US.add size 2sz else size in
  let ptr = mmap size' in
  if (A.is_null ptr) then (
    (**) intro_vrefine (linked_tree p md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    return ptr
  ) else (
    let b = mem md_v (ptr, size) in
    if b then (
      (**) intro_vrefine (linked_tree p md_v) is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
      //TODO: add a die()
      drop (null_or_varray ptr);
      let r = intro_null_null_or_varray #U8.t in
      return r
    ) else (
      let h0 = get () in
      let size_r = mmap_actual_size size in
      let md_v' = insert false md_v (ptr, size) in
      Spec.lemma_insert false (spec_convert cmp) (v_linked_tree p md_v h0) (ptr, size);
      Spec.lemma_insert2 (spec_convert cmp) (v_linked_tree p md_v h0) (ptr, size) (fun x -> US.v (snd x) <> 0);
      write metadata_ptr md_v';
      (**) intro_vrefine (linked_tree p md_v') is_wf;
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
  (**) elim_vrefine (linked_tree p t) is_wf;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree p t)
    (linked_tree p md_v);
  let size = get_size md_v in
  (**) intro_vrefine (linked_tree p md_v) is_wf;
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
  (**) elim_vrefine (linked_tree p t) is_wf;
  let md_v = read metadata_ptr in
  (**) change_equal_slprop
    (linked_tree p t)
    (linked_tree p md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree p md_v h0);
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
    Spec.lemma_delete (spec_convert cmp) (v_linked_tree p md_v h0) (ptr, size);
    Spec.lemma_delete2 (spec_convert cmp) (v_linked_tree p md_v h0) (ptr, size) (fun x -> US.v (snd x) <> 0);
    write metadata_ptr md_v';
    (**) intro_vrefine (linked_tree p md_v') is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v') linked_wf_tree;
    [@inline_let] let b = true in
    change_equal_slprop
      emp
      (if b then emp else A.varray ptr);
    return b
  ) else (
    (**) intro_vrefine (linked_tree p md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    [@inline_let] let b = false in
    change_equal_slprop
      (A.varray ptr)
      (if b then emp else A.varray ptr);
    return b
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let large_malloc (size: US.t)
  : Steel (array U8.t)
  emp
  (fun ptr -> null_or_varray ptr)
  (requires fun _ ->
    US.v size > 0 /\
    US.fits (US.v size + U32.v page_size) /\
    (enable_slab_canaries_malloc ==> US.fits (US.v size + 2)))
  (ensures fun _ ptr h1 ->
    let s : (t_of (null_or_varray ptr))
      = h1 (null_or_varray ptr) in
    not (A.is_null ptr) ==> (
      (enable_slab_canaries_malloc ==> A.length ptr == US.v size + 2) /\
      (not enable_slab_canaries_malloc ==> A.length ptr == US.v size) /\
      array_u8_alignment ptr page_size /\
      A.is_full_array ptr /\
      zf_u8 s
    )
  )
  =
  let r = with_lock
    unit
    unit
    (array U8.t)
    (fun v0 -> ind_linked_wf_tree metadata.data)
    (fun _ -> emp)
    (fun _ r -> null_or_varray r)
    ()
    ()
    metadata.lock
    (fun _ ptr s ->
      not (A.is_null ptr) ==> (
        (enable_slab_canaries_malloc ==> A.length ptr == US.v size + 2) /\
        (not enable_slab_canaries_malloc ==> A.length ptr == US.v size) /\
        array_u8_alignment ptr page_size /\
        A.is_full_array ptr /\
        zf_u8 s
      )
    )
    (fun _ ->
      let md_size = _size metadata.data in
      [@inline_let] let max = 18446744073709551615UL in
      assert (U64.v max = Impl.Core.c);
      if U64.lt md_size max then (
        //TODO: large_malloc' can return NULL due to mmap
        let ptr = large_malloc_aux metadata.data size in
        return ptr
      ) else (
        let r = intro_null_null_or_varray #U8.t in
        return r
      )
    )
  in
  return r

let large_free (ptr: array U8.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  let b = with_lock
    (ref t)
    (array U8.t)
    bool
    (fun v0 -> ind_linked_wf_tree v0)
    (fun v1 -> A.varray v1)
    (fun v1 v2 -> if v2 then emp else A.varray v1)
    metadata.data
    ptr
    metadata.lock
    (fun _ _ _ -> True)
    (fun _ -> large_free_aux metadata.data ptr) in
  return b

let large_getsize_aux (metadata: ref t) (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr `star` ind_linked_wf_tree metadata)
  (fun _ -> A.varray ptr `star` ind_linked_wf_tree metadata)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    h0 (A.varray ptr `star` ind_linked_wf_tree metadata)
    ==
    h1 (A.varray ptr `star` ind_linked_wf_tree metadata) /\
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
  (**) elim_vrefine (linked_tree p t) is_wf;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree p t)
    (linked_tree p md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree p md_v h0);
  let size = find md_v (ptr, 0sz) in
  if Some? size then (
    let size = Some?.v size in
    (**) intro_vrefine (linked_tree p md_v) is_wf;
    (**) intro_vdep (vptr metadata) (linked_wf_tree md_v) linked_wf_tree;
    return size
  ) else (
    (**) intro_vrefine (linked_tree p md_v) is_wf;
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
  let r = with_lock
    (ref t)
    (array U8.t)
    US.t
    (fun v0 -> ind_linked_wf_tree v0)
    (fun v1 -> A.varray v1)
    (fun v1 _ -> A.varray v1)
    metadata.data
    ptr
    metadata.lock
    (fun (x0: t_of (A.varray ptr))
         (r: US.t)
         (x1: t_of (A.varray ptr)) ->
      x0 `Seq.equal` x1 /\
      (US.v r > 0 ==>
        (enable_slab_canaries_malloc ==> A.length ptr == US.v r + 2) /\
        (not enable_slab_canaries_malloc ==> A.length ptr == US.v r)
      )
    )
    (fun _ -> large_getsize_aux metadata.data ptr)
  in
  return r

(*)
- convert AVL lib to use size_t instead of u64
- find: some improvements ahead? (better spec)
- use a large vdep between avl and mmap'ed allocations?
