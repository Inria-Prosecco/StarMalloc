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

#push-options "--fuel 1 --ifuel 1"
val malloc (arena_id:US.t{US.v arena_id < US.v nb_arenas}) (size: US.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (A.is_null r) ==> (
      A.length r >= US.v size /\
      (enable_zeroing ==> zf_u8 (Seq.slice s 0 (US.v size)))
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let malloc arena_id size =
  if US.lte size (US.uint32_to_sizet page_size)
  then (
    let ptr = slab_malloc arena_id (US.sizet_to_uint32 size) in
    if (A.is_null ptr) then (
      return ptr
    ) else (
      elim_live_null_or_varray ptr;
      let _ = memset_u8 ptr 0z size in
      intro_live_null_or_varray ptr;
      return ptr
    )
  ) else (
    large_malloc size
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val aligned_alloc (arena_id:US.t{US.v arena_id < US.v nb_arenas}) (alignment:US.t) (size: US.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (A.is_null r) ==> (
      A.length r >= US.v size /\
      (enable_zeroing ==> zf_u8 (Seq.slice s 0 (US.v size)))
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let aligned_alloc arena_id alignment size =
  if size = 0sz then intro_null_null_or_varray #U8.t else (
  if US.lte size (US.uint32_to_sizet page_size) && US.lte alignment (US.uint32_to_sizet page_size)
  then (
    let ptr = slab_aligned_alloc arena_id (US.sizet_to_uint32 alignment) (US.sizet_to_uint32 size) in
    if (A.is_null ptr) then (
      return ptr
    ) else (
      elim_live_null_or_varray ptr;
      let _ = memset_u8 ptr 0z size in
      intro_live_null_or_varray ptr;
      return ptr
    )
  ) else (
    // mmap returns page-aligned memory. We do not support alignment larger
    // than a page size.
    if alignment `US.rem` 16sz = 0sz && alignment `US.lte` (US.uint32_to_sizet page_size) then
      large_malloc size
    else
      intro_null_null_or_varray #U8.t
  ))
#pop-options

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
    elim_null_null_or_varray ptr;
    [@inline_let] let b = true in
    change_equal_slprop
      emp (if b then emp else A.varray ptr);
    return b
  ) else (
    elim_live_null_or_varray ptr;
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
    //TODO: add precond+postcond
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

module G = FStar.Ghost

let return_status = x:nat{x < 3}

// in case of failure, this vprop describes
// memory that is still allocated but not returned
// TODO: doc this better, realloc conforms to C DR 400
// realloc(NULL,0) only gives NULL on alloc failure
// (errno is ENOMEM)
// realloc(ptr,0) only gives NULL on alloc failure, ptr unchanged
// (errno is ENOMEM)
// TODO: errno

let realloc_vp (status: return_status)
  (ptr: array U8.t)
  (new_ptr: array U8.t)
  : vprop
  = match status with
  // success
  | 0 -> emp
  // new allocation fails, cannot memcpy,
  // returning previous allocation
  | 1 -> null_or_varray ptr
  // new_allocation succeeds, freeing old allocation fails
  // returning null
  | 2 -> null_or_varray ptr `star` null_or_varray new_ptr

#restart-solver

#push-options "--fuel 1 --ifuel 1"
#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects"
let realloc (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (ptr: array U8.t) (new_size: US.t)
  : Steel (array U8.t & G.erased (return_status & array U8.t))
  (
    null_or_varray ptr `star`
    (A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size))
  )
  (fun r ->
    null_or_varray (fst r) `star`
    (realloc_vp (fst (G.reveal (snd r))) ptr (snd (G.reveal (snd r))) `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size))
  )
  //TODO: add precond+postcond (expected_size)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let s0 : t_of (null_or_varray ptr)
      = h0 (null_or_varray ptr) in
    let s1 : t_of (null_or_varray (fst r))
      = h1 (null_or_varray (fst r)) in
    // success
    not (A.is_null (fst r)) ==> (
      A.length (fst r) >= US.v new_size /\
      (not (A.is_null ptr) ==>
        Seq.slice s1 0 (min (A.length ptr) (US.v new_size))
        ==
        Seq.slice s0 0 (min (A.length ptr) (US.v new_size))
      )
    )
    // On failure, returns a null pointer.
    // The original pointer ptr remains valid and may need to be deallocated with free or realloc.
    //TODO: add corresponding postcond
  )
  =
  if A.is_null ptr then (
    // In case that ptr is a null pointer, the function behaves
    // like malloc, assigning a new block of size bytes and
    // returning a pointer to its beginning.
    elim_null_null_or_varray ptr;
    let new_ptr = malloc arena_id new_size in
    change_equal_slprop
      emp
      (realloc_vp 0 (A.null #U8.t) (A.null #U8.t));
    return (new_ptr, G.hide (0, A.null #U8.t))
  ) else (
    elim_live_null_or_varray ptr;
    let new_ptr = malloc arena_id new_size in
    if (A.is_null new_ptr) then (
      // If the function fails to allocate the requested block
      // of memory, a null pointer is returned, and the memory
      // block pointed to by argument ptr is not deallocated
      // (it is still valid, and with its contents unchanged).
      elim_null_null_or_varray new_ptr;
      intro_live_null_or_varray ptr;
      change_equal_slprop
        (null_or_varray ptr)
        (realloc_vp 1 ptr (A.null #U8.t));
      let r = intro_null_null_or_varray #U8.t in
      return (r, G.hide (1, A.null #U8.t))
    ) else (
      // The content of the memory block is preserved up to the
      // lesser of the new and old sizes, even if the block is
      // moved to a new location. If the new size is larger, the
      // value of the newly allocated portion is indeterminate.
      elim_live_null_or_varray new_ptr;
      let old_size = getsize ptr in
      // TODO: to be removed, refine large_getsize + add slab_getsize precondition
      assume (US.v old_size == A.length ptr);
      assert (A.length new_ptr >= US.v new_size);
      let min_of_sizes =
        if US.lte new_size old_size
        then new_size
        else old_size in
      let _ = memcpy_u8 new_ptr ptr min_of_sizes in
      intro_live_null_or_varray new_ptr;
      intro_live_null_or_varray ptr;
      let b = free ptr in
      if b then (
        change_equal_slprop
          (if b then emp else A.varray ptr) emp;
        change_equal_slprop
          emp
          (realloc_vp 0 ptr (A.null #U8.t));
        return (new_ptr, G.hide (0, A.null #U8.t))
      ) else (
        //TODO: add a die(), internal error
        change_equal_slprop
          (if b then emp else A.varray ptr)
          (A.varray ptr);
        intro_live_null_or_varray ptr;
        change_equal_slprop
          (null_or_varray ptr `star` null_or_varray new_ptr)
          (realloc_vp 2 ptr new_ptr);
        let r = intro_null_null_or_varray #U8.t in
        return (r, G.hide (2, new_ptr))
      )
    )
  )

//TODO: there should be defensive checks and no precondition
let calloc
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (size1 size2: US.t)
  : Steel (array U8.t)
  (
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (fun r ->
    null_or_varray r `star`
    (A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size))
  )
  (requires fun _ -> US.fits (US.v size1 * US.v size2))
  (ensures fun _ r h1 ->
    let size = US.v size1 * US.v size2 in
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (A.is_null r) ==> (
      A.length r >= size /\
      zf_u8 (Seq.slice s 0 size)
    )
  )
  =
  let size = US.mul size1 size2 in
  let ptr = malloc arena_id size in
  if A.is_null ptr
  then (
    return ptr
  ) else (
    if enable_zeroing then (
      return ptr
    ) else (
      elim_live_null_or_varray ptr;
      let _ = memset_u8 ptr 0z size in
      intro_live_null_or_varray ptr;
      return ptr
    )
  )
