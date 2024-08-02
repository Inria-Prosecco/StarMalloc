module LargeAlloc

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

open Prelude
open Constants
open Utils2
open NullOrVarray

#push-options "--fuel 0 --ifuel 0"

open Steel.Reference

open Mman2

open Impl.Trees.Types

inline_for_extraction noextract
unfold
let linked_tree = Impl.Core.linked_tree #data

// is well-formed (AVL + content)
let is_wf (x: wdm data) : prop
  =
  (Spec.is_avl (spec_convert cmp) x &&
  Spec.forall_keys x (fun x -> US.v x.size <> 0))
  == true

let linked_wf_tree (tree: t)
  = linked_tree pred p tree `vrefine` is_wf

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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let init_mmap_md (_:unit)
  : SteelTop mmap_md false (fun _ -> emp) (fun _ _ _ -> True)
  =
  let ptr = mmap_ptr_metadata_init () in
  let tree = create_leaf () in
  write ptr tree;
  (**) intro_vrefine (linked_tree pred p tree) is_wf;
  (**) intro_vdep (vptr ptr) (linked_wf_tree tree) linked_wf_tree;
  let lock = L.new_lock (ind_linked_wf_tree ptr) in
  return { data=ptr; lock=lock; }
#pop-options

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
    (G.reveal pred) r
  )
  =
  let ptr = SizeClass.allocate_size_class metadata_slabs.scs in
  if A.is_null ptr
  then (
    let r = FatalError.die_from_avl_node_malloc_failure x ptr in
    return r
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
    let r' = Impl.Trees.Cast.M.array_u8__to__ref_node ptr in
    Impl.Trees.Cast.M.array_u8__to__ref_node_bijectivity ptr;
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
    (G.reveal pred) r
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
      (G.reveal pred) r
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
  (requires fun _ -> (G.reveal pred) r)
  (ensures fun _ _ _-> True)
  =
  vptr_not_null r;
  let ptr = Impl.Trees.Cast.M.ref_node__to__array_u8 r in
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
    change_equal_slprop
      (if b then emp else A.varray ptr)
      (A.varray ptr);
    FatalError.die_from_avl_node_free_failure ptr;
    return ()
  )

let trees_free2 (r: ref node)
  : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> (G.reveal pred) r)
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
[@@ __steel_reduce__]
let v_ind_tree
  (#vp:vprop)
  (ptr: ref t)
  (h:rmem vp{
    FStar.Tactics.with_tactic selector_tactic (can_be_split vp (ind_linked_wf_tree ptr) /\ True)
  })
  : GTot (wdm data)
  =
  let x
    : t_of (ind_linked_wf_tree ptr)
    = h (ind_linked_wf_tree ptr) in
  assert_norm (vdep_payload (vptr ptr) linked_wf_tree (dfst x) == (x: wdm data{is_wf x}));
  dsnd x
#pop-options

open PtrdiffWrapper

#push-options "--print_implicits"

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
inline_for_extraction noextract
let large_malloc_aux
  (metadata_ptr: ref t)
  (size: US.t)
  : Steel (array U8.t)
  (
    ind_linked_wf_tree metadata_ptr
  )
  (fun r ->
    ind_linked_wf_tree metadata_ptr `star`
    null_or_varray r
  )
  (requires fun h0 ->
    let t : wdm data = v_ind_tree metadata_ptr h0 in
    Spec.size_of_tree t < c /\
    US.v size > 0 /\
    US.v size > U32.v page_size /\
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun h0 r h1 ->
    let t : wdm data = v_ind_tree metadata_ptr h0 in
    let t' : wdm data = v_ind_tree metadata_ptr h1 in
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    US.fits (US.v size + U32.v page_size) /\
    US.v size > U32.v page_size /\
    Spec.is_avl (spec_convert cmp) t /\
    (not (A.is_null r) ==> (
      (let size' = mmap_actual_size size in
      let d : data' = {
        user_ptr = r;
        ptr = r;
        size = size';
        shift = 0sz;
        alignment = 0ul;
      } in
      is_data d /\
      A.length r == US.v size' /\
      A.is_full_array r /\
      array_u8_alignment r page_size /\
      zf_u8 s /\
      not (Spec.mem (spec_convert cmp) t d) /\
      Spec.mem (spec_convert cmp) t' d /\
      True
    )))
  )
  =
  (**) let t = elim_vdep (vptr metadata_ptr) linked_wf_tree in
  (**) elim_vrefine (linked_tree pred p t) is_wf;
  let md_v = read metadata_ptr in
  (**) change_equal_slprop
    (linked_tree pred p t)
    (linked_tree pred p md_v);
  (**) let h0 = get () in
  (**) let tree : G.erased (x:wdm data{is_wf x}) = G.hide (v_linked_tree pred p md_v h0) in
  assert (Spec.forall_keys tree (fun x -> US.v x.size <> 0));
  (**) Spec.height_lte_size tree;
  let ptr = mmap size in
  if (A.is_null ptr) then (
    (**) intro_vrefine (linked_tree pred p md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    return ptr
  ) else (
    let size' = mmap_actual_size size in
    [@inline_let] let r : data' = {
      user_ptr = ptr;
      ptr;
      size = size';
      shift = 0sz;
      alignment = 0ul;
    } in
    assume (r.user_ptr == A.split_r r.ptr r.shift);
    assert (is_data r);
    let b = mem md_v r in
    if b then (
      (**) intro_vrefine (linked_tree pred p md_v) is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
      //TODO: add a die()/refactor, including insert_avl
      drop (null_or_varray ptr);
      let r = intro_null_null_or_varray #U8.t in
      return r
    ) else (
      let h0 = get () in
      change_equal_slprop emp (p r);
      let md_v' = insert false md_v r in
      Spec.lemma_insert false (spec_convert cmp) tree r;
      Spec.lemma_insert2 #data (spec_convert cmp) tree r (fun x -> US.v x.size <> 0);
      write metadata_ptr md_v';
      (**) intro_vrefine (linked_tree pred p md_v') is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v') linked_wf_tree;
      return ptr
    )
  )

module FU = FStar.UInt

assume val f
  (size: US.t)
  (alignment: U32.t)
  (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr)
  (fun _ -> A.varray ptr)
  (requires fun _ ->
    A.length ptr >= US.v size + U32.v alignment /\
    US.v size > 0 /\
    U32.v alignment > 0 /\
    U32.v alignment % U32.v page_size = 0
  )
  (ensures fun h0 pos h1 ->
    US.v pos < A.length ptr /\
    (let ptr' = A.split_r ptr pos in
    U32.v alignment > 0 /\
    array_u8_alignment ptr' alignment /\
    A.length ptr' >= US.v size /\
    A.asel ptr h1 == A.asel ptr h0
  ))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
inline_for_extraction noextract
val large_aligned_alloc_aux
  (metadata_ptr: ref t)
  (size: US.t)
  (alignment: U32.t)
  : Steel (array U8.t & G.erased data)
  (
    ind_linked_wf_tree metadata_ptr
  )
  (fun r ->
    ind_linked_wf_tree metadata_ptr `star`
    null_or_varray (fst r)
  )
  (requires fun h0 ->
    let t : wdm data = v_ind_tree metadata_ptr h0 in
    Spec.size_of_tree t < c /\
    US.v size > 0 /\
    US.v size > U32.v page_size /\
    US.fits (US.v size + U32.v alignment + U32.v page_size) /\
    U32.v alignment > 0 /\
    U32.v alignment % U32.v page_size = 0
  )
  (ensures fun h0 r h1 ->
    let t : wdm data = v_ind_tree metadata_ptr h0 in
    let t' : wdm data = v_ind_tree metadata_ptr h1 in
    let s : t_of (null_or_varray (fst r))
      = h1 (null_or_varray (fst r)) in
    US.fits (US.v size + U32.v page_size) /\
    US.fits (US.v size + U32.v alignment + U32.v page_size) /\
    U32.v alignment > 0 /\
    U32.v alignment % U32.v page_size = 0 /\
    US.v size > U32.v page_size /\
    Spec.is_avl (spec_convert cmp) t /\
    (not (A.is_null (fst r)) ==> (
      let size' = mmap_actual_size (US.add size (US.uint32_to_sizet alignment)) in
      (G.reveal (snd r)).size = size' /\
      A.length (G.reveal (snd r)).ptr == US.v size' /\
      fst r == (G.reveal (snd r)).user_ptr /\
      fst r == A.split_r (G.reveal (snd r)).ptr (G.reveal (snd r)).shift /\
      A.is_full_array (G.reveal (snd r)).ptr /\
      //TODO: that would be overspec of the used axiomatised function
      //array_u8_alignment ptr page_size /\
      array_u8_alignment (fst r) alignment /\
      zf_u8 s /\
      not (Spec.mem (spec_convert cmp) t (G.reveal (snd r))) /\
      Spec.mem (spec_convert cmp) t' (G.reveal (snd r)) /\
      True
    ))
  )

let large_aligned_alloc_aux metadata_ptr size alignment
  =
  (**) let t = elim_vdep (vptr metadata_ptr) linked_wf_tree in
  (**) elim_vrefine (linked_tree pred p t) is_wf;
  let md_v = read metadata_ptr in
  (**) change_equal_slprop
    (linked_tree pred p t)
    (linked_tree pred p md_v);
  (**) let h0 = get () in
  (**) let tree : G.erased (x:wdm data{is_wf x}) = G.hide (v_linked_tree pred p md_v h0) in
  assert (Spec.forall_keys tree (fun x -> US.v x.size <> 0));
  (**) Spec.height_lte_size tree;
  let ptr = mmap (US.add size (US.uint32_to_sizet alignment)) in
  if (A.is_null ptr) then (
    (**) intro_vrefine (linked_tree pred p md_v) is_wf;
    (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    return (ptr, G.hide null_data)
  ) else (
    let size' = mmap_actual_size (US.add size (US.uint32_to_sizet alignment)) in
    elim_live_null_or_varray ptr;
    let pos = f size alignment ptr in
    let ptr' = A.split_r ptr pos in
    [@inline_let] let r : data' = {
      user_ptr = ptr';
      ptr;
      size = size';
      shift = pos;
      alignment;
    } in
    assert (is_data r);
    let b = mem md_v r in
    if b then (
      (**) intro_vrefine (linked_tree pred p md_v) is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
      //TODO: add a die()/refactor, including insert_avl
      drop (A.varray ptr);
      let r = intro_null_null_or_varray #U8.t in
      return (r, G.hide null_data)
    ) else (
      let s0 = gget (A.varray ptr) in
      zf_u8_split s0 (US.v pos);
      A.ghost_split ptr pos;
      change_equal_slprop
        (A.varray (A.split_l ptr pos))
        (p r);
      //array_u8_alignment_lemma ptr (A.split_r ptr pos) page_size page_size;
      intro_live_null_or_varray (A.split_r ptr pos);
      let md_v' = insert false md_v r in
      Spec.lemma_insert false (spec_convert cmp) tree r;
      Spec.lemma_insert2 #data (spec_convert cmp) tree r (fun x -> US.v x.size <> 0);
      write metadata_ptr md_v';
      (**) intro_vrefine (linked_tree pred p md_v') is_wf;
      (**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v') linked_wf_tree;
      return (A.split_r ptr pos, G.hide r)
    )
  )

inline_for_extraction noextract
let _size (metadata: ref t) : Steel U64.t
  (ind_linked_wf_tree metadata)
  (fun _ -> ind_linked_wf_tree metadata)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let t : wdm data = v_ind_tree metadata h0 in
    h1 (ind_linked_wf_tree metadata)
    ==
    h0 (ind_linked_wf_tree metadata) /\
    U64.v r == Spec.size_of_tree t
  )
  =
  (**) let t = elim_vdep (vptr metadata) linked_wf_tree in
  (**) elim_vrefine (linked_tree pred p t) is_wf;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree pred p t)
    (linked_tree pred p md_v);
  let size = get_size md_v in
  (**) intro_vrefine (linked_tree pred p md_v) is_wf;
  (**) intro_vdep (vptr metadata) (linked_wf_tree md_v) linked_wf_tree;
  return size

#restart-solver

inline_for_extraction noextract
val large_free_aux
  (metadata_ptr: ref t)
  (ptr: array U8.t)
  : Steel (bool & G.erased data)
  (
    A.varray ptr `star`
    ind_linked_wf_tree metadata_ptr
  )
  (fun r ->
    (if (fst r) then emp else A.varray ptr) `star`
    ind_linked_wf_tree metadata_ptr
  )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let t : wdm data = v_ind_tree metadata_ptr h0 in
    let t' : wdm data = v_ind_tree metadata_ptr h1 in
    (fst r ==> (
      A.is_full_array ptr /\
      A.length ptr > U32.v page_size /\
      US.fits (A.length ptr) /\
      (let size = US.uint_to_t (A.length ptr) in
        size == (G.reveal (snd r)).size /\
        Spec.mem (spec_convert cmp) t (snd r) /\
        not (Spec.mem (spec_convert cmp) t' (snd r))
      )
    )) /\
    (not (fst r) ==> (
      let d : data' = {
        user_ptr = ptr;
        ptr = A.null #U8.t;
        size = 0sz;
        shift = 0sz;
        alignment = 0ul
      } in
      is_data d /\
      not (Spec.mem (spec_convert cmp) t d) /\
      h1 (ind_linked_wf_tree metadata_ptr)
      ==
      h0 (ind_linked_wf_tree metadata_ptr)
    ))
  )

#restart-solver

#restart-solver

let large_free_aux metadata_ptr ptr
  =
  (**) let t = elim_vdep (vptr metadata_ptr) linked_wf_tree in
  (**) elim_vrefine (linked_tree pred p t) is_wf;
  let md_v = read metadata_ptr in
  (**) change_equal_slprop
    (linked_tree pred p t)
    (linked_tree pred p md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree pred p md_v h0);
  let k_elem : data' = {
    user_ptr = ptr;
    ptr = A.null #U8.t;
    size = 0sz;
    shift = 0sz;
    alignment = 0ul
  } in
  assert (is_data k_elem);
  let r = find md_v k_elem in
  if not (A.is_null r.ptr) then (
    let h0 = get () in
    let r' : result = delete md_v r in
    if A.is_null r'.data.ptr then (
      //error
      sladmit ();
      return (false, G.hide null_data)
    ) else (
      slassert (p r'.data);
      let d = r'.data in
      assume (d == r);
      assume (ptr == d.user_ptr);
      assert (is_data d);
      assert (d.size <> 0sz);
      assert (US.v d.shift < US.v d.size);
      assert (US.v d.size == A.length d.ptr);
      if d.alignment <> 0ul then (
        change_equal_slprop
          (p r'.data)
          (A.varray (A.split_l d.ptr d.shift));
        change_equal_slprop
          (A.varray ptr)
          (A.varray (A.split_r d.ptr d.shift));
        A.ghost_join (A.split_l d.ptr d.shift) (A.split_r d.ptr d.shift) ();
        change_equal_slprop
          (A.varray (A.merge (A.split_l d.ptr d.shift) (A.split_r d.ptr d.shift)))
          (A.varray d.ptr);
        assert (US.v d.size == A.length d.ptr)
      ) else (
        change_equal_slprop
          (p r'.data)
          emp;
        rewrite_slprop
          (A.varray ptr)
          (A.varray d.ptr)
          (fun _ -> admit ())
      );
      munmap d.ptr d.size;
      write metadata_ptr r'.ptr;
      sladmit ();
      //Spec.lemma_delete (spec_convert cmp) (v_linked_tree pred p md_v h0) r;
      //Spec.lemma_delete2 #data (spec_convert cmp) (v_linked_tree pred p md_v h0) r (fun x -> US.v x.size <> 0);
      //(**) intro_vrefine (linked_tree pred p r'.ptr) is_wf;
      //(**) intro_vdep (vptr metadata_ptr) (linked_wf_tree r'.ptr) linked_wf_tree;
      //[@inline_let] let b = true in
      //change_equal_slprop
      //  emp
      //  (if b then emp else A.varray ptr);
      return (true, G.hide null_data)
    )
  ) else (
    sladmit ();
    return (false, G.hide null_data)
    //(**) intro_vrefine (linked_tree pred p md_v) is_wf;
    //(**) intro_vdep (vptr metadata_ptr) (linked_wf_tree md_v) linked_wf_tree;
    //[@inline_let] let b = false in
    //change_equal_slprop
    //  (A.varray ptr)
    //  (if b then emp else A.varray ptr);
    //return (b, G.hide null_data)
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let large_malloc (size: US.t)
  : Steel (array U8.t)
  emp
  (fun ptr -> null_or_varray ptr)
  (requires fun _ ->
    US.v size > 0 /\
    US.v size > U32.v page_size /\
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun _ ptr h1 ->
    let s : (t_of (null_or_varray ptr))
      = h1 (null_or_varray ptr) in
    not (A.is_null ptr) ==> (
      US.fits (US.v size + U32.v page_size) /\
      (let size' = mmap_actual_size size in
      A.length ptr == US.v size' /\
      A.is_full_array ptr /\
      array_u8_alignment ptr page_size /\
      zf_u8 s
    ))
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
        (let size' = mmap_actual_size size in
        A.length ptr == US.v size' /\
        array_u8_alignment ptr page_size /\
        A.is_full_array ptr /\
        zf_u8 s
      ))
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

let large_aligned_alloc size alignment
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
        U32.v alignment > 0 /\
        A.length ptr >= US.v size /\
        array_u8_alignment ptr alignment /\
        zf_u8 s
      )
    )
    (fun _ ->
      let md_size = _size metadata.data in
      [@inline_let] let max = 18446744073709551615UL in
      assert (U64.v max = Impl.Core.c);
      if U64.lt md_size max then (
        //TODO: large_malloc' can return NULL due to mmap
        let ptr = large_aligned_alloc_aux metadata.data size alignment in
        assume (A.length (fst ptr) >= US.v size);
        return (fst ptr)
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
  let r = with_lock
    (ref t)
    (array U8.t)
    (bool & G.erased data)
    (fun v0 -> ind_linked_wf_tree v0)
    (fun v1 -> A.varray v1)
    (fun v1 v2 -> if (fst v2) then emp else A.varray v1)
    metadata.data
    ptr
    metadata.lock
    (fun _ _ _ -> True)
    (fun _ -> large_free_aux metadata.data ptr) in
  let b = fst r in
  change_equal_slprop
    (if (fst r) then emp else A.varray ptr)
    (if b then emp else A.varray ptr);
  return b

let large_getsize_aux (metadata: ref t) (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr `star` ind_linked_wf_tree metadata)
  (fun _ -> A.varray ptr `star` ind_linked_wf_tree metadata)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    h0 (A.varray ptr)
    ==
    h1 (A.varray ptr) /\
    A.asel ptr h1 == A.asel ptr h0 /\
    //h1 (ind_linked_wf_tree metadata)
    //==
    //h0 (ind_linked_wf_tree metadata) /\
    (US.v r > 0 ==>
      A.length ptr == US.v r /\
      US.v r > U32.v page_size
    )
  )
  =
  (**) let t = elim_vdep (vptr metadata) linked_wf_tree in
  (**) elim_vrefine (linked_tree pred p t) is_wf;
  let md_v = read metadata in
  (**) change_equal_slprop
    (linked_tree pred p t)
    (linked_tree pred p md_v);
  (**) let h0 = get () in
  (**) Spec.height_lte_size (v_linked_tree pred p md_v h0);
  let k_elem : data' = {
    user_ptr = ptr;
    ptr = A.null #U8.t;
    size = 0sz;
    shift = 0sz;
    alignment = 0ul;
  } in
  assert (is_data k_elem);
  let d = find md_v k_elem in
  if not (A.is_null d.ptr) then (
    admit ();
    let size = US.sub d.size d.shift in
    (**) intro_vrefine (linked_tree pred p md_v) is_wf;
    (**) intro_vdep (vptr metadata) (linked_wf_tree md_v) linked_wf_tree;
    return size
  ) else (
    (**) intro_vrefine (linked_tree pred p md_v) is_wf;
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
      A.length ptr == US.v r /\
      US.v r > U32.v page_size
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
        A.length ptr == US.v r /\
        US.v r > U32.v page_size
      )
    )
    (fun _ -> large_getsize_aux metadata.data ptr)
  in
  return r

(*)
- use a large vdep between avl and mmap'ed allocations?
