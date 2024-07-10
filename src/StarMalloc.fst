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
open Constants
open Config
open Utils2
open ExternUtils
open NullOrVarray

// small allocations: slab allocator
//open Main
open Main.Meta
open Main2
// large allocations: AVL+mmap allocator
open LargeAlloc

#push-options "--fuel 0 --ifuel 0"

#push-options "--fuel 1 --ifuel 1"
val malloc (arena_id:US.t{US.v arena_id < US.v nb_arenas}) (size: US.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ ->
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (A.is_null r) ==> (
      A.length r >= US.v size /\
      array_u8_alignment r 16ul /\
      (enable_zeroing_malloc ==> zf_u8 (Seq.slice s 0 (US.v size)))
      //Seq.length s >= 2 /\
      //(enable_slab_canaries_malloc ==>
      //  Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
      //  Seq.index s (A.length r - 1) == slab_canaries_magic2
      //)
    )
  )
#pop-options

module G = FStar.Ghost

//TODO: [@ CConst]
let threshold : US.t =
  if enable_slab_canaries_malloc
  then US.sub (US.uint32_to_sizet page_size) 2sz
  else US.uint32_to_sizet page_size

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let malloc arena_id size =
  if (US.lte size threshold) then (
    let ptr = slab_malloc arena_id (US.sizet_to_uint32 size) in
    if (A.is_null ptr || not enable_zeroing_malloc) then (
      return ptr
    ) else (
      elim_live_null_or_varray ptr;
      let b = check_zeroing_u8 ptr size in
      if b then (
        intro_live_null_or_varray ptr;
        return ptr
      ) else (
        FatalError.die_from_malloc_zeroing_check_failure ptr;
        intro_null_null_or_varray #U8.t
      )
    )
  ) else (
    // TODO: use efficient align here
    assert (US.v size > U32.v page_size - 2);
    let size' = if US.lte size (US.uint32_to_sizet page_size)
      then US.add (US.uint32_to_sizet page_size) 1sz
      else size in
    let r = large_malloc size' in
    let s : G.erased (t_of (null_or_varray r))
      = gget (null_or_varray r) in
    if not (A.is_null r)
    then (
      zf_u8_split s (US.v size);
      array_u8_alignment_lemma
        r
        r
        page_size
        16ul
    ) else ();
    return r
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val aligned_alloc (arena_id:US.t{US.v arena_id < US.v nb_arenas}) (alignment:US.t) (size: US.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ ->
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (A.is_null r) ==> (
      0 < US.v alignment /\
      US.v alignment <= U32.v page_size /\
      A.length r >= US.v size /\
      array_u8_alignment r 16ul /\
      array_u8_alignment r (US.sizet_to_uint32 alignment) /\
      (enable_zeroing_malloc ==> zf_u8 (Seq.slice s 0 (US.v size)))
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let aligned_alloc arena_id alignment size
  =
  let page_as_sz = US.uint32_to_sizet page_size in
  let check = US.gt alignment 0sz && US.rem (US.uint32_to_sizet page_size) alignment = 0sz in
  if check then (
    let alignment_as_u32 = US.sizet_to_uint32 alignment in
    if (US.lte size threshold) then (
      let ptr = slab_aligned_alloc arena_id alignment_as_u32 (US.sizet_to_uint32 size) in
      if (A.is_null ptr || not enable_zeroing_malloc) then (
        return ptr
      ) else (
        elim_live_null_or_varray ptr;
        let b = check_zeroing_u8 ptr size in
        if b then (
          intro_live_null_or_varray ptr;
          return ptr
        ) else (
          // TODO: distinct case from malloc?
          FatalError.die_from_malloc_zeroing_check_failure ptr;
          intro_null_null_or_varray #U8.t
        )
      )
    ) else (
      let size' = if US.lte size (US.uint32_to_sizet page_size)
        then US.add (US.uint32_to_sizet page_size) 1sz
        else size in
      let ptr = large_malloc size' in
      assert_norm (pow2 12 == U32.v page_size);
      MiscArith.alignment_lemma (U32.v page_size) 12 (US.v alignment) (U32.v page_size);
      array_u8_alignment_lemma2 ptr page_size (US.sizet_to_uint32 alignment);
      let s : G.erased (t_of (null_or_varray ptr))
        = gget (null_or_varray ptr) in
      if not (A.is_null ptr)
      then (
        zf_u8_split s (US.v size);
        array_u8_alignment_lemma
          ptr
          ptr
          page_size
          16ul
      ) else ();
      return ptr
    )
  ) else (
    // TODO: add some warning, failure
    let r = intro_null_null_or_varray #U8.t in
    return r
  )
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
  (requires fun _ -> within_size_classes_pred ptr )
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

noextract
let spec_getsize
  (length: nat{enable_slab_canaries_malloc ==> length >= 2})
  : Tot nat
  =
  if (length <= U32.v page_size)
  then (
    // slab allocation, possibly a canary
    if enable_slab_canaries_malloc
    then length - 2
    else length
  ) else (
    // large allocation, no canary
    length
  )

module L = FStar.List.Tot

inline_for_extraction noextract
let full_getsize (ptr: array U8.t)
  : Steel (US.t & G.erased bool)
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
  (requires fun _ -> within_size_classes_pred ptr)
  (ensures fun h0 result h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    (US.v (fst result) > 0 ==>
      (enable_slab_canaries_malloc ==> A.length ptr >= 2) /\
      US.v (fst result) == spec_getsize (A.length ptr) /\
      (G.reveal (snd result) <==> US.v (fst result) <= U32.v page_size) /\
      (G.reveal (snd result) ==> (
        let idx = sc_selection (US.sizet_to_uint32 (fst result)) in
        (enable_sc_fast_selection ==>
          A.length ptr == U32.v (L.index sc_list (US.v idx))) /\
        (enable_slab_canaries_malloc ==>
          A.length ptr == US.v (fst result) + 2
        ) /\
        (not enable_slab_canaries_malloc ==>
          A.length ptr == US.v (fst result)
        )
      ))
    )
  )
  =
  let b = SAA.within_bounds_intro
    (A.split_l sc_all.slab_region 0sz)
    ptr
    (A.split_r sc_all.slab_region slab_region_size) in
  if b then (
    let r = slab_getsize ptr in
    r, G.hide b
  ) else (
    let r = large_getsize ptr in
    r, G.hide b
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
  (requires fun _ -> within_size_classes_pred ptr)
  (ensures fun h0 result h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    (US.v result > 0 ==>
      (enable_slab_canaries_malloc ==> A.length ptr >= 2) /\
      US.v result == spec_getsize (A.length ptr) /\
      (US.v result <= U32.v page_size ==> (
        let idx = sc_selection (US.sizet_to_uint32 result) in
        (enable_sc_fast_selection ==>
          A.length ptr == U32.v (L.index sc_list (US.v idx))) /\
        (enable_slab_canaries_malloc ==>
          A.length ptr == US.v result + 2
        ) /\
        (not enable_slab_canaries_malloc ==>
          A.length ptr == US.v result
        )
      ))
    )
  )
  =
  let r, _ = full_getsize ptr in
  r

module G = FStar.Ghost

noextract
let return_status = x:nat{x < 8}

let realloc_small_optim_lemma
  (old_size: US.t)
  (new_size: US.t)
  : Lemma
  (requires enable_sc_fast_selection /\
    US.v old_size <= U32.v page_size /\
    US.v new_size <= US.v threshold /\
    (let old_idx = sc_selection (US.sizet_to_uint32 old_size) in
    let old_sc = L.index sc_list (US.v old_idx) in
    let new_idx = if enable_slab_canaries_malloc
      then sc_selection (US.sizet_to_uint32 (US.add new_size 2sz))
      else sc_selection (US.sizet_to_uint32 new_size) in
    (enable_slab_canaries_malloc ==>
      US.v old_size == U32.v old_sc - 2) /\
    (not enable_slab_canaries_malloc ==>
      US.v old_size == U32.v old_sc) /\
    old_idx = new_idx)
  )
  (ensures
    US.v new_size <= US.v old_size
  )
  =
  ()


// in case of failure, this vprop describes
// memory that is still allocated but not returned
// TODO: realloc(NULL, 0) could be POSIX or C23, deallocation is deprecated
// TODO: errno

let realloc_vp (status: return_status)
  (ptr: array U8.t)
  (new_ptr: array U8.t)
  : vprop
  = match status with
  // realloc(NULL, new_size): allocation, new_ptr should be returned
  | 0 -> emp
  // realloc(ptr, 0): deallocation success, NULL should be returned
  | 1 -> emp
  // realloc(ptr, 0): deallocation failure, fatal_error (invalid free)
  | 2 -> emp
  // realloc(invalid pointer, ...): failure, fatal_error (invalid realloc)
  | 3 -> emp
  // realloc(valid pointer, ...): optim case (success), ptr should be returned
  | 4 -> emp
  // realloc(valid pointer, ...): allocation failure, NULL should be returned
  | 5 -> null_or_varray ptr
  // realloc(valid pointer, ...): success, new_ptr should be returned
  | 6 -> emp
  // realloc(valid pointer, ...): deallocation failure, fatal_error (invalid free)
  | 7 -> null_or_varray new_ptr

#restart-solver

#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
val realloc_standard_case (arena_id:US.t{US.v arena_id < US.v nb_arenas})
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
  (requires fun _ ->
    within_size_classes_pred ptr /\
    US.fits (US.v new_size + U32.v page_size) /\
    not (A.is_null ptr) /\
    US.v new_size > 0
  )
  (ensures fun h0 r h1 ->
    let s0 : t_of (null_or_varray ptr)
      = h0 (null_or_varray ptr) in
    let s1 : t_of (null_or_varray (fst r))
      = h1 (null_or_varray (fst r)) in
    // success
    not (A.is_null (fst r)) ==> (
      A.length (fst r) >= US.v new_size /\
      //array_u8_alignment (fst r) 16ul /\
      (not (A.is_null ptr) ==> (
        (enable_slab_canaries_malloc ==> A.length ptr >= 2) /\
        (let size = spec_getsize (A.length ptr) in
          Seq.slice s1 0 (min size (US.v new_size))
          ==
          Seq.slice s0 0 (min size (US.v new_size))
        )
      ))
    ) /\
    True
  )
#pop-options

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"
let realloc_standard_case arena_id ptr new_size
  =
  elim_live_null_or_varray ptr;
  let old_size = getsize ptr in
  let old_allocation_is_small : bool = US.lte old_size (u32_to_sz page_size) in
  let new_allocation_is_small : bool = US.lte new_size threshold in
  let same_case : bool = old_allocation_is_small = new_allocation_is_small in
  let small_case_optim_condition = enable_sc_fast_selection && old_allocation_is_small && same_case && (
    let old_sc = sc_selection (US.sizet_to_uint32 old_size) in
    let new_sc = if enable_slab_canaries_malloc
      then sc_selection (US.sizet_to_uint32 (US.add new_size 2sz))
      else sc_selection (US.sizet_to_uint32 new_size) in
    old_sc = new_sc) in
  let large_case_optim_condition = (not old_allocation_is_small) && same_case && (
    US.lte new_size old_size
  ) in
  // not a valid pointer from the allocator point of view, fail
  if (old_size = 0sz) then (
    // 3) invalid pointer, fatal_error
    FatalError.die_from_realloc_invalid_previous_alloc ptr;
    let r = intro_null_null_or_varray #U8.t in
    change_equal_slprop
      emp
      (realloc_vp 3 ptr (A.null #U8.t));
    return (r, G.hide (3, A.null #U8.t))
  ) else (
    // most common case
    if small_case_optim_condition then realloc_small_optim_lemma old_size new_size else ();
    assert (small_case_optim_condition ==> A.length ptr >= US.v new_size);
    assert (large_case_optim_condition ==> A.length ptr >= US.v new_size);

    if (small_case_optim_condition || large_case_optim_condition) then (
      // 4) optimization
      (**) intro_live_null_or_varray ptr;
      (**) change_equal_slprop
        emp
        (realloc_vp 4 (A.null #U8.t) (A.null #U8.t));
      return (ptr, G.hide (4, A.null #U8.t))
    ) else (
      // reallocation classical malloc/memcpy/free sequence of operations
      let new_ptr = malloc arena_id new_size in
      if (A.is_null new_ptr) then (
        // If the function fails to allocate the requested block
        // of memory, a null pointer is returned, and the memory
        // block pointed to by argument ptr is not deallocated
        // (it is still valid, and with its contents unchanged).
        // 5) allocation failure
        (**) elim_null_null_or_varray new_ptr;
        (**) intro_live_null_or_varray ptr;
        change_equal_slprop
          (null_or_varray ptr)
          (realloc_vp 5 ptr (A.null #U8.t));
        let r = intro_null_null_or_varray #U8.t in
        return (r, G.hide (5, A.null #U8.t))
      ) else (
        // The content of the memory block is preserved up to the
        // lesser of the new and old sizes, even if the block is
        // moved to a new location. If the new size is larger, the
        // value of the newly allocated portion is indeterminate.
        (**) elim_live_null_or_varray new_ptr;
        assert (A.length new_ptr >= US.v new_size);
        let min_of_sizes =
          if US.lte new_size old_size
          then new_size
          else old_size in
        let _ = memcpy_u8 new_ptr ptr min_of_sizes in
        (**) intro_live_null_or_varray new_ptr;
        (**) intro_live_null_or_varray ptr;
        let b = free ptr in
        if b then (
          // 6) full reallocation success
          change_equal_slprop
            (if b then emp else A.varray ptr) emp;
          change_equal_slprop
            emp
            (realloc_vp 0 ptr (A.null #U8.t));
          return (new_ptr, G.hide (6, A.null #U8.t))
        ) else (
          // 7) deallocation failure, fatal_error
          change_equal_slprop
            (if b then emp else A.varray ptr)
            (A.varray ptr);
          FatalError.die_from_realloc_free_failure ptr;
          let r = intro_null_null_or_varray #U8.t in
          return (r, G.hide (7, new_ptr))
        )
      )
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val realloc (arena_id:US.t{US.v arena_id < US.v nb_arenas})
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
  (requires fun _ ->
    within_size_classes_pred ptr /\
    US.fits (US.v new_size + U32.v page_size)
  )
  (ensures fun h0 r h1 ->
    let s0 : t_of (null_or_varray ptr)
      = h0 (null_or_varray ptr) in
    let s1 : t_of (null_or_varray (fst r))
      = h1 (null_or_varray (fst r)) in
    // success
    not (A.is_null (fst r)) ==> (
      A.length (fst r) >= US.v new_size /\
      //array_u8_alignment (fst r) 16ul /\
      (not (A.is_null ptr) ==> (
        (enable_slab_canaries_malloc ==> A.length ptr >= 2) /\
        (let size = spec_getsize (A.length ptr) in
          Seq.slice s1 0 (min size (US.v new_size))
          ==
          Seq.slice s0 0 (min size (US.v new_size))
        )
      ))
    ) /\
    // optimization case
    //(G.reveal (fst (snd r)) = 3 ==> fst r == ptr)
    True
  )

let realloc arena_id ptr new_size
  =
  if A.is_null ptr then (
    // 1) realloc(null, new_size)
    // In case that ptr is a null pointer, the function behaves
    // like malloc, assigning a new block of size bytes and
    // returning a pointer to its beginning.
    (**) elim_null_null_or_varray ptr;
    let new_ptr = malloc arena_id new_size in
    (**) change_equal_slprop
      emp
      (realloc_vp 0 (A.null #U8.t) (A.null #U8.t));
    return (new_ptr, G.hide (0, A.null #U8.t))
  ) else (if (new_size = 0sz) then (
    // 2) realloc(ptr, 0sz)
    // freeing
    // TODO: POSIX or C23: realloc(ptr, 0) does not free memory, add corresponding config switch
    let b = free ptr in
    if b then (
      (**) change_equal_slprop
        (if b then emp else A.varray ptr) emp;
      (**) change_equal_slprop
        emp
        (realloc_vp 1 ptr (A.null #U8.t));
      let r = intro_null_null_or_varray #U8.t in
      return (r, G.hide (1, A.null #U8.t))
    ) else (
      (**) change_equal_slprop
        (if b then emp else A.varray ptr)
        (A.varray ptr);
      FatalError.die_from_realloc_free_failure ptr;
      let r = intro_null_null_or_varray #U8.t in
      (**) change_equal_slprop
        emp
        (realloc_vp 2 (A.null #U8.t) (A.null #U8.t));
      return (r, G.hide (2, A.null #U8.t))
    )
  ) else (
    realloc_standard_case arena_id ptr new_size
  ))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
//TODO: there should be defensive checks and no precondition
val calloc
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
  (requires fun _ ->
    FStar.Math.Lemmas.nat_times_nat_is_nat (US.v size1) (US.v size2);
    let size : nat = US.v size1 * US.v size2 in
    US.fits (size + U32.v page_size)
  )
  (ensures fun _ r h1 ->
    FStar.Math.Lemmas.nat_times_nat_is_nat (US.v size1) (US.v size2);
    let size : nat = US.v size1 * US.v size2 in
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    null_or_varray_t r;
    not (A.is_null r) ==> (
      A.length r >= size /\
      zf_u8 (Seq.slice s 0 size) /\
      array_u8_alignment r 16ul
    )
  )

let calloc arena_id size1 size2
  =
  let size = builtin_mul_overflow size1 size2 in
  let ptr = malloc arena_id size in
  if A.is_null ptr
  then (
    return ptr
  ) else (
    if enable_zeroing_malloc then (
      return ptr
    ) else (
      elim_live_null_or_varray ptr;
      let _ = apply_zeroing_u8 ptr size in
      intro_live_null_or_varray ptr;
      return ptr
    )
  )
#pop-options
