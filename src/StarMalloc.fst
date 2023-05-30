module StarMalloc

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

open FStar.Mul
open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module R = Steel.Reference
module SAA = Steel.ArrayArith

open Prelude
open Utils2
open Config
open NullOrVarray

// slab allocator
open Main
// AVL+mmap allocator
open LargeAlloc

#push-options "--fuel 0 --ifuel 0"

val malloc (size: US.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ ->
    //null_or_varray_t ptr;
    //let s
    //  : normal (t_of (null_or_varray #U8.t ptr))
    //  = h1 (null_or_varray ptr) in
    //let s
    //  : option (Seq.lseq U8.t (A.length ptr))
    //  = s in
    not (A.is_null r) ==> A.length r >= US.v size
  )

let malloc size =
  if US.lte size (US.uint32_to_sizet page_size)
  then slab_malloc (US.sizet_to_uint32 size)
  else large_malloc size

val free (ptr: array U8.t)
  : Steel bool
  (
    null_or_varray ptr `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let free ptr =
  if A.is_null ptr then (
    sladmit ();
    return true
  ) else (
    rewrite_slprop
      (null_or_varray ptr)
      (A.varray ptr)
      (fun _ -> admit ());
    let b = SAA.within_bounds_intro
      (A.split_l sc_all.slab_region 0sz)
      ptr
      (A.split_r sc_all.slab_region slab_region_size) in
    if b then (
      slab_free ptr
    ) else (
      large_free ptr
    )
  )

let getsize (ptr: array U8.t)
  : Steel US.t
  (
    A.varray ptr `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (fun _ ->
    A.varray ptr `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel ptr h1 == A.asel ptr h0
  )
  =
  let b = SAA.within_bounds_intro
    (A.split_l sc_all.slab_region 0sz)
    ptr
    (A.split_r sc_all.slab_region slab_region_size) in
  if b then (
    slab_getsize ptr
  ) else (
    large_getsize ptr
  )

assume val memcpy_u8 (dest src: array U8.t) (n: US.t)
  : Steel (array U8.t)
  (A.varray dest `star` A.varray src)
  (fun _ -> A.varray dest `star` A.varray src)
  (requires fun _ ->
    A.length dest >= US.v n /\
    A.length src >= US.v n
  )
  (ensures fun h0 r h1 ->
    A.length dest >= US.v n /\
    A.length src >= US.v n /\
    Seq.slice (A.asel dest h1) 0 (US.v n)
    ==
    Seq.slice (A.asel src h0) 0 (US.v n) /\
    A.asel src h1 == A.asel src h0
  )

module G = FStar.Ghost

let return_status = x:nat{x < 3}

let realloc_vp (status: return_status)
  (ptr: array U8.t)
  (new_ptr: array U8.t)
  (r: array U8.t)
  : vprop
  = match status with
  // success
  | 0 -> null_or_varray r
  // new allocation fails, cannot memcpy,
  // returning previous allocation
  | 1 -> null_or_varray ptr
  // new_allocation succeeds, freeing old allocation fails
  // returning null
  | 2 -> null_or_varray ptr `star` null_or_varray new_ptr

#restart-solver

#push-options "--z3rlimit 150 --compat_pre_typed_indexed_effects"
let realloc (ptr: array U8.t) (new_size: US.t)
  : Steel (array U8.t & G.erased (return_status & array U8.t))
  (
    null_or_varray ptr `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (fun r ->
    realloc_vp (fst (G.reveal (snd r))) ptr (snd (G.reveal (snd r))) (fst r) `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (requires fun _ -> True)
  (ensures fun _ r _ ->
    not (A.is_null (fst r)) ==> A.length (fst r) >= US.v new_size
  )
  =
  //TODO: fixme
  admit ();
  if A.is_null ptr then (
    // In case that ptr is a null pointer, the function behaves
    // like malloc, assigning a new block of size bytes and
    // returning a pointer to its beginning.
    rewrite_slprop
      (null_or_varray ptr)
      emp
      (fun _ -> admit ());
    let new_ptr = malloc new_size in
    change_equal_slprop
      (null_or_varray new_ptr)
      (realloc_vp 0 (A.null #U8.t) (A.null #U8.t) new_ptr);
    return (new_ptr, G.hide (0, A.null #U8.t))
  ) else (
    rewrite_slprop
      (null_or_varray ptr)
      (A.varray ptr)
      (fun _ -> admit ());
    //change_equal_slprop (null_or_varray ptr) (A.varray ptr);
    let new_ptr = malloc new_size in
    if (A.is_null new_ptr) then (
      // If the function fails to allocate the requested block
      // of memory, a null pointer is returned, and the memory
      // block pointed to by argument ptr is not deallocated
      // (it is still valid, and with its contents unchanged).
      rewrite_slprop
        (null_or_varray new_ptr `star` A.varray ptr)
        (null_or_varray ptr)
        (fun _ -> admit ());
      change_equal_slprop
        (null_or_varray ptr)
        (realloc_vp 1 ptr (A.null #U8.t) (A.null #U8.t));
      return (A.null #U8.t, G.hide (1, A.null #U8.t))
    ) else (
      // The content of the memory block is preserved up to the
      // lesser of the new and old sizes, even if the block is
      // moved to a new location. If the new size is larger, the
      // value of the newly allocated portion is indeterminate.
      rewrite_slprop
        (null_or_varray new_ptr)
        (A.varray new_ptr)
        (fun _ -> admit ());
      let old_size = getsize ptr in
      // TODO: to be removed, refine large_getsize + add slab_getsize precondition
      assume (US.v old_size == A.length ptr);
      assert (A.length new_ptr >= US.v new_size);
      let min_of_sizes =
        if US.lte new_size old_size
        then new_size
        else old_size in
      let _ = memcpy_u8 new_ptr ptr min_of_sizes in
      rewrite_slprop
        (A.varray new_ptr `star` A.varray ptr)
        (null_or_varray new_ptr `star` null_or_varray ptr)
        (fun _ -> admit ());
      let b = free ptr in
      if b then (
        change_equal_slprop
          (if b then emp else A.varray ptr) emp;
        change_equal_slprop
          (null_or_varray new_ptr)
          (realloc_vp 0 ptr (A.null #U8.t) new_ptr);
        return (new_ptr, G.hide (0, A.null #U8.t))
      ) else (
        change_equal_slprop
          (if b then emp else A.varray ptr) (null_or_varray ptr);
        change_equal_slprop
          (null_or_varray ptr `star` null_or_varray new_ptr)
          (realloc_vp 2 ptr new_ptr (A.null #U8.t));
        return (A.null #U8.t, G.hide (2, new_ptr))
      )
    )
  )

assume val memset_u8 (dest: array U8.t) (c: U8.t) (n: US.t)
  : Steel (array U8.t)
  (A.varray dest)
  (fun _ -> A.varray dest)
  (requires fun _ ->
    A.length dest >= US.v n
  )
  (ensures fun h0 r h1 ->
    A.length dest >= US.v n /\
    Seq.slice (A.asel dest h1) 0 (US.v n)
    ==
    Seq.create (US.v n) c
  )

//TODO: there should be defensive checks and no precondition
//TODO: add zeroing postcondition
let calloc (size1 size2: US.t)
  : Steel (array U8.t)
  (
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (fun r ->
    null_or_varray r `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (requires fun _ -> US.fits (US.v size1 * US.v size2))
  (ensures fun _ r h1 ->
    let size = US.v size1 * US.v size2 in
    not (A.is_null r) ==> A.length r >= size /\
    True
    //not (snd r) ==> zf_u8 (Seq.slice (A.asel (fst r) h1) 0 size)
  )
  =
  let size = US.mul size1 size2 in
  let ptr = malloc size in
  if A.is_null ptr
  then (
    return ptr
  ) else (
    rewrite_slprop
      (null_or_varray ptr)
      (A.varray ptr)
      (fun _ -> admit ());
    let _ = memset_u8 ptr 0z size in
    rewrite_slprop
      (A.varray ptr)
      (null_or_varray ptr)
      (fun _ -> admit ());
    return ptr
  )
