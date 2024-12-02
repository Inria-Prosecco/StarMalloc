module Main2

inline_for_extraction noextract
val slab_malloc_generic
  (arena_id: US.t{US.v arena_id < US.v nb_arenas})
  (bytes: U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16ul /\
      Seq.length s >= 2 /\
      (enable_slab_canaries_malloc ==>
        Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length r - 1) == slab_canaries_magic2
      )
    )
  )

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_malloc_generic arena_id bytes =
  if enable_slab_canaries_malloc
  then slab_malloc_generic_canary arena_id bytes
  else slab_malloc_generic_nocanary arena_id bytes
#pop-options

inline_for_extraction noextract
val slab_malloc_fast
  (arena_id: US.t{US.v arena_id < US.v nb_arenas})
  (bytes: U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ ->
    (enable_slab_canaries_malloc ==> U32.v bytes <= U32.v page_size - 2) /\
    (not enable_slab_canaries_malloc ==> U32.v bytes <= U32.v page_size)
  )
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16ul /\
      Seq.length s >= 2 /\
      (enable_slab_canaries_malloc ==>
        Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length r - 1) == slab_canaries_magic2
      )
    )
  )

#restart-solver

open FStar.Mul
open MiscArith

let adhoc_mod_lemma
  (i k multiple: nat)
  : Lemma
  (requires
    multiple > 0 /\
    i < multiple
  )
  (ensures
    (i + k * multiple) % multiple == i
  )
  =
  lemma_mod_mul2 k multiple multiple;
  lemma_mod_plus2 i (k * multiple) multiple

#restart-solver

module FML = FStar.Math.Lemmas

let slab_malloc_fast_lemma_aux_mod
  (i j k n: nat)
  : Lemma
  (requires
    i < k /\
    j < n
  )
  (ensures
    i * n + j < k * n
  )
  =
  FML.lemma_mult_le_right n i (k-1);
  assert (i * n <= (k-1) * n)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let slab_malloc_fast_lemma
  (arena_id: US.t{US.v arena_id < US.v nb_arenas})
  (size: U32.t)
  (i: US.t)
  : Lemma
  (requires
    US.v i < US.v nb_size_classes /\
    U32.v size <= U32.v (get_u32 (L.index sc_list (US.v i)))
  )
  (ensures
    US.fits (US.v arena_id * US.v nb_size_classes) /\
    US.fits (US.v arena_id * US.v nb_size_classes + US.v i) /\
    US.v arena_id * US.v nb_size_classes + US.v i < TLA.length sizes /\
    (let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
    U32.v size <= U32.v (get_u32 ((Seq.index (G.reveal sc_all.g_size_classes) (US.v idx)).data.size))
  ))
  =
  total_nb_sc_lemma ();
  assert (US.fits (US.v nb_arenas * US.v nb_size_classes));
  slab_malloc_fast_lemma_aux_mod (US.v arena_id) (US.v i) (US.v nb_arenas) (US.v nb_size_classes);
  assert (US.v arena_id * US.v nb_size_classes + US.v i < US.v nb_arenas * US.v nb_size_classes);
  US.fits_lte (US.v arena_id * US.v nb_size_classes + US.v i) (US.v nb_arenas * US.v nb_size_classes);
  let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
  let size1 = L.index sc_list (US.v i) in
  let size2 = TLA.get sizes idx in
  let size3 = (Seq.index (G.reveal sc_all.g_size_classes) (US.v idx)).data.size in
  sizes_t_pred_elim sizes;
  assert (size2 == L.index arena_sc_list (US.v idx));
  assert (size2 == L.index sc_list (US.v idx % US.v nb_size_classes));
  adhoc_mod_lemma (US.v i) (US.v arena_id) (US.v nb_size_classes);
  assert (US.v idx % US.v nb_size_classes == US.v i);
  assert (size2 == size1);
  assume (size3 == size2)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_malloc_fast arena_id bytes
  =
  if enable_slab_canaries_malloc then (
    [@inline_let] let bytes = U32.add bytes 2ul in
    let i = sc_selection bytes in
    slab_malloc_fast_lemma arena_id bytes i;
    [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
    let size = TLA.get sizes idx in
    let ptr = slab_malloc_one idx bytes in
    assume (A.length ptr == U32.v (get_u32 size));
    set_canary ptr size;
    return ptr
  ) else (
    let i = sc_selection bytes in
    slab_malloc_fast_lemma arena_id bytes i;
    [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
    let ptr = slab_malloc_one idx bytes in
    return ptr
  )
#pop-options

let slab_malloc arena_id bytes
  =
  if enable_sc_fast_selection
  then slab_malloc_fast arena_id bytes
  else slab_malloc_generic arena_id bytes

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_aligned_alloc arena_id alignment bytes =
  if enable_slab_canaries_malloc
  then slab_aligned_alloc_generic_canary arena_id alignment bytes
  else slab_aligned_alloc_generic_nocanary arena_id alignment bytes
#pop-options

#restart-solver

open Mman
open SizeClass
open WithLock

#push-options "--fuel 0 --fuel 0 --z3rlimit 50"
inline_for_extraction noextract
let slab_free' (i:US.t{US.v i < US.v nb_size_classes * US.v nb_arenas}) (ptr: array U8.t) (diff: US.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun h0 ->
    Seq.length sc_all.g_size_classes == US.v nb_size_classes * US.v nb_arenas /\
    (let sc = Seq.index (G.reveal sc_all.g_size_classes) (US.v i) in
    let diff' = offset (ptr_of ptr) - offset (ptr_of sc.data.slab_region) in
    same_base_array ptr sc.data.slab_region /\
    0 <= diff' /\
    (sc.data.is_extended ==>
      diff' % US.v sc_ex_slab_size == 0
    ) /\
    (not sc.data.is_extended ==>
      (diff' % U32.v page_size) % U32.v (get_u32 sc.data.size) == 0
    ) /\
    diff' < US.v sc_slab_region_size /\
    A.length ptr == U32.v (get_u32 sc.data.size) /\
    US.v diff = diff'
  ))
  (ensures fun h0 _ h1 -> True)
  =
  let b = with_lock_roarray
    size_class_struct
    (array U8.t)
    bool
    size_class
    sc_all.size_classes
    (G.reveal sc_all.g_size_classes)
    sc_all.ro_perm
    (fun v0 -> size_class_vprop v0)
    (fun s -> s.data)
    (fun s -> s.lock)
    (fun v1 -> A.varray v1)
    (fun v1 r -> if r then emp else A.varray v1)
    i
    ptr
    (fun _ _ _ _ -> True)
    (fun sc_data -> deallocate_size_class sc_data ptr diff)
  in
  return b
#pop-options

/// Precondition of free, capturing that a client must return an array corresponding to the
/// entire memory provided by the allocator:
/// If a pointer is within a size class and aligned with
/// the slots, then its length corresponds to the slot size
let within_size_class_i (ptr:A.array U8.t) (sc: size_class_struct) : prop =
  (
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region)) in
    // If ptr is within the size class sc
    same_base_array sc.slab_region ptr /\
    0 <= diff /\
    diff < US.v sc_slab_region_size /\
    // and it is aligned on the slots
    (sc.is_extended ==>
      diff % US.v sc_ex_slab_size == 0
    ) /\
    (not sc.is_extended ==>
      (diff % U32.v page_size) % U32.v (get_u32 sc.size) == 0
    )
  ) ==>
    // then its length is the length of a slot
    A.length ptr == U32.v (get_u32 sc.size)

#restart-solver

#push-options "--fuel 0 --ifuel 1 --z3rlimit 150 --quake 10/10"
/// Elimination lemma for `within_size_class_i`, triggering F* to prove the precondition
/// of the implication
let elim_within_size_class_i
  (ptr:A.array U8.t)
  (i:nat{i < Seq.length sc_all.g_size_classes})
  (size:U32.t)
  : Lemma
  (requires (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.data.slab_region)) in
    within_size_class_i ptr sc.data /\
    size == get_u32 sc.data.size /\
    same_base_array sc.data.slab_region ptr /\
    0 <= diff /\
    diff < US.v sc_slab_region_size /\
    (sc.data.is_extended ==>
      diff % US.v sc_ex_slab_size == 0
    ) /\
    (not sc.data.is_extended ==>
      (diff % U32.v page_size) % U32.v (get_u32 sc.data.size) == 0
    )
  ))
  (ensures (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    A.length ptr == U32.v size
  ))
  =
  ()
#pop-options

let within_size_classes_pred (ptr:A.array U8.t) : prop =
  forall (i:nat{i < Seq.length sc_all.g_size_classes}).
    within_size_class_i ptr (Seq.index (G.reveal sc_all.g_size_classes) i).data

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let mod_lt (a b: US.t)
  : Lemma
  (requires US.v b > 0)
  (ensures
    US.v (US.rem a b) = (US.v a) % (US.v b) /\
    US.v (US.rem a b) < US.v b)
  = ()
#pop-options

open Prelude
open Main

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --query_stats"
inline_for_extraction noextract
val slab_getsize_aux_sc
  (ptr: array U8.t)
  (index: US.t)
  (diff_sz: US.t)
  (size: U32.t)
  : Steel US.t
  (A.varray ptr)
  (fun _ -> A.varray ptr)
  (requires fun h0 ->
    US.v index < Seq.length sc_all.g_size_classes /\
    (let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc.data.slab_region) in
    let size_as_union = TLA.get sizes index in
    Sc? size_as_union /\
    size == get_sc size_as_union /\
    size == get_u32 size_as_union /\
    size == get_u32 sc.data.size /\
    US.v diff_sz == diff /\
    same_base_array ptr sc.data.slab_region /\
    0 <= diff /\
    diff < US.v sc_slab_region_size /\
    within_size_class_i ptr sc.data
  ))
  (ensures fun h0 result h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    US.v result <= U32.v page_size /\
    (let idx = sc_selection (US.sizet_to_uint32 result) in
    (result <> 0sz ==> (
      A.length ptr == U32.v size /\
      (enable_slab_canaries_malloc ==>
        A.length ptr == US.v result + 2
      ) /\
      (not enable_slab_canaries_malloc ==>
        A.length ptr == US.v result
      ) /\
      (enable_sc_fast_selection ==>
        A.length ptr == U32.v (get_u32 (L.index sc_list (US.v idx)))
      )
    ))
  ))

let slab_getsize_aux_sc ptr index diff_sz size
  =
  (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
  // reveal synced_sizes
  assume (not sc.data.is_extended);
  let rem_page = US.rem diff_sz (u32_to_sz page_size) in
  assert (US.v rem_page == (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc.data.slab_region)) % (U32.v page_size));
  if US.rem rem_page (u32_to_sz size) = 0sz then (
    (**) elim_within_size_class_i ptr (US.v index) size;
    (**) assert (A.length ptr == U32.v size);
    let index' = G.hide (US.v index % US.v nb_size_classes) in
    sizes_t_pred_elim sizes;
    assert (size = get_u32 (L.index sc_list index'));
    if enable_sc_fast_selection then (
      sc_selection_is_exact1 index';
      sc_selection_is_exact2 index'
    ) else ();
    if enable_slab_canaries_malloc then
      return (US.uint32_to_sizet (size `U32.sub` 2ul))
    else
      return (US.uint32_to_sizet size)
  ) else (
    return 0sz
  )

inline_for_extraction noextract
val slab_getsize_aux_sc_ex
  (ptr: array U8.t)
  (index: US.t)
  (diff_sz: US.t)
  (size: U32.t)
  : Steel US.t
  (A.varray ptr)
  (fun _ -> A.varray ptr)
  (requires fun h0 ->
    US.v index < Seq.length sc_all.g_size_classes /\
    (let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc.data.slab_region) in
    let size_as_union = TLA.get sizes index in
    Sc_ex? size_as_union /\
    size == get_sc_ex size_as_union /\
    size == get_u32 size_as_union /\
    size == get_u32 sc.data.size /\
    US.v diff_sz == diff /\
    same_base_array ptr sc.data.slab_region /\
    0 <= diff /\
    diff < US.v sc_slab_region_size /\
    within_size_class_i ptr sc.data
  ))
  (ensures fun h0 result h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    US.v result <= max_sc_ex /\
    (let idx = sc_selection (US.sizet_to_uint32 result) in
    (result <> 0sz ==> (
      A.length ptr == U32.v size /\
      (enable_slab_canaries_malloc ==>
        A.length ptr == US.v result + 2
      ) /\
      (not enable_slab_canaries_malloc ==>
        A.length ptr == US.v result
      ) /\
      (enable_sc_fast_selection ==>
        A.length ptr == U32.v (get_u32 (L.index sc_list (US.v idx)))
      )
    ))
  ))

let slab_getsize_aux_sc_ex ptr index diff_sz size
  =
  (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
  // reveal synced_sizes
  assume (sc.data.is_extended);
  if US.rem diff_sz sc_ex_slab_size = 0sz then (
    (**) elim_within_size_class_i ptr (US.v index) size;
    (**) assert (A.length ptr == U32.v size);
    let index' = G.hide (US.v index % US.v nb_size_classes) in
    sizes_t_pred_elim sizes;
    assert (size = get_u32 (L.index sc_list index'));
    if enable_sc_fast_selection then (
      sc_selection_is_exact1 index';
      sc_selection_is_exact2 index'
    ) else ();
    if enable_slab_canaries_malloc then
      return (US.uint32_to_sizet (size `U32.sub` 2ul))
    else
      return (US.uint32_to_sizet size)
  ) else (
    return 0sz
  )

let slab_getsize ptr
  =
  SAA.within_bounds_elim
    (A.split_l sc_all.slab_region 0sz)
    (A.split_r sc_all.slab_region slab_region_size)
    ptr;
  UP.fits_lt
    (A.offset (A.ptr_of ptr)
    -
    A.offset (A.ptr_of (A.split_l sc_all.slab_region 0sz)))
    (US.v slab_region_size);
  let diff = A.ptrdiff
    ptr
    (A.split_l sc_all.slab_region 0sz) in
  let diff_sz = UP.ptrdifft_to_sizet diff in
  let index = US.div diff_sz sc_slab_region_size in
  lemma_div_lt (US.v sc_slab_region_size) (US.v nb_size_classes) (US.v nb_arenas) (US.v diff_sz);
  total_nb_sc_lemma ();
  assert (US.v index < total_nb_sc);
  mod_lt index nb_size_classes;
  let size_as_union = TLA.get sizes index in
  let size = get_u32 size_as_union in

  (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  // reveal size_class_pred
  assume (A.offset (A.ptr_of (G.reveal sc).data.slab_region) == A.offset (A.ptr_of sc_all.slab_region) + US.v index * US.v sc_slab_region_size);

  let rem_sc = US.rem diff_sz sc_slab_region_size in
  assert (US.v rem_sc == A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc).data.slab_region));

  assume (size == get_u32 sc.data.size);
  assume (same_base_array ptr sc.data.slab_region);
  if Sc? size_as_union then
    slab_getsize_aux_sc ptr index rem_sc size
  else
    slab_getsize_aux_sc_ex ptr index rem_sc size

#restart-solver

#restart-solver

inline_for_extraction noextract
val slab_free_aux_sc
  (ptr: array U8.t)
  (index: US.t)
  (diff_sz: US.t)
  (size: U32.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun h0 ->
    Seq.length sc_all.g_size_classes == US.v nb_size_classes * US.v nb_arenas /\
    US.v index < Seq.length sc_all.g_size_classes /\
    (let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc.data.slab_region) in
    let size_as_union = TLA.get sizes index in
    Sc? size_as_union /\
    size == get_sc size_as_union /\
    size == get_u32 size_as_union /\
    size == get_u32 sc.data.size /\
    US.v diff_sz == diff /\
    same_base_array ptr sc.data.slab_region /\
    0 <= diff /\
    diff < US.v sc_slab_region_size /\
    within_size_class_i ptr sc.data
  ))
  (ensures fun h0 r _ ->
    let s = A.asel ptr h0 in
    enable_slab_canaries_free ==>
      (r ==>
        A.length ptr >= 2 /\
        Seq.index s (A.length ptr - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length ptr - 1) == slab_canaries_magic2
      )
  )

let slab_free_aux_sc ptr index diff_sz size
  =
  (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
  // reveal synced_sizes
  assume (not sc.data.is_extended);
  let rem_page = US.rem diff_sz (u32_to_sz page_size) in
  assert (US.v rem_page == (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc.data.slab_region)) % (U32.v page_size));
  if US.rem rem_page (u32_to_sz size) = 0sz then (
    (**) elim_within_size_class_i ptr (US.v index) size;
    (**) assert (A.length ptr == U32.v size);
    if enable_slab_canaries_free then (
      enable_slab_canaries_lemma ();
      let magic1 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) in
      let magic2 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) in
      if magic1 = slab_canaries_magic1 && magic2 = slab_canaries_magic2 then
        slab_free' index ptr diff_sz
      else
        // Canary was overwritten
        return false
    ) else (
      slab_free' index ptr diff_sz
    )
  ) else (
    return false
  )

inline_for_extraction noextract
val slab_free_aux_sc_ex
  (ptr: array U8.t)
  (index: US.t)
  (diff_sz: US.t)
  (size: U32.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun h0 ->
    Seq.length sc_all.g_size_classes == US.v nb_size_classes * US.v nb_arenas /\
    US.v index < Seq.length sc_all.g_size_classes /\
    (let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc.data.slab_region) in
    let size_as_union = TLA.get sizes index in
    Sc_ex? size_as_union /\
    size == get_sc_ex size_as_union /\
    size == get_u32 size_as_union /\
    size == get_u32 sc.data.size /\
    US.v diff_sz == diff /\
    same_base_array ptr sc.data.slab_region /\
    0 <= diff /\
    diff < US.v sc_slab_region_size /\
    within_size_class_i ptr sc.data
  ))
  (ensures fun h0 r _ ->
    let s = A.asel ptr h0 in
    enable_slab_canaries_free ==>
      (r ==>
        A.length ptr >= 2 /\
        Seq.index s (A.length ptr - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length ptr - 1) == slab_canaries_magic2
      )
  )

let slab_free_aux_sc_ex ptr index diff_sz size
  =
  (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
  // reveal synced_sizes
  assume (sc.data.is_extended);
  if US.rem diff_sz sc_ex_slab_size = 0sz then (
    if enable_slab_canaries_free then (
      enable_slab_canaries_lemma ();
      let magic1 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) in
      let magic2 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) in
      if magic1 = slab_canaries_magic1 && magic2 = slab_canaries_magic2 then
        slab_free' index ptr diff_sz
      else
        // Canary was overwritten
        return false
    ) else (
      slab_free' index ptr diff_sz
    )
  ) else (
    return false
  )

let slab_free ptr
  =
  SAA.within_bounds_elim
    (A.split_l sc_all.slab_region 0sz)
    (A.split_r sc_all.slab_region slab_region_size)
    ptr;
  UP.fits_lt
    (A.offset (A.ptr_of ptr)
    -
    A.offset (A.ptr_of (A.split_l sc_all.slab_region 0sz)))
    (US.v slab_region_size);
  let diff = A.ptrdiff
    ptr
    (A.split_l sc_all.slab_region 0sz) in
  let diff_sz = UP.ptrdifft_to_sizet diff in
  let index = US.div diff_sz sc_slab_region_size in
  lemma_div_lt (US.v sc_slab_region_size) (US.v nb_size_classes) (US.v nb_arenas) (US.v diff_sz);
  total_nb_sc_lemma ();
  assert (US.v index < total_nb_sc);
  mod_lt index nb_size_classes;
  let size_as_union = TLA.get sizes index in
  let size = get_u32 size_as_union in

  (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  // reveal size_class_pred
  assume (A.offset (A.ptr_of (G.reveal sc).data.slab_region) == A.offset (A.ptr_of sc_all.slab_region) + US.v index * US.v sc_slab_region_size);

  let rem_sc = US.rem diff_sz sc_slab_region_size in
  assert (US.v rem_sc == A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc).data.slab_region));

  assume (size == get_u32 sc.data.size);
  assume (same_base_array ptr sc.data.slab_region);
  assume (U32.v size > 0);

  if Sc? size_as_union then
    slab_free_aux_sc ptr index rem_sc size
  else
    slab_free_aux_sc_ex ptr index rem_sc size

