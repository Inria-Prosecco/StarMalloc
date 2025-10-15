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
    (enable_slab_canaries_malloc ==> U32.v bytes <= U32.v max_slab_size - 2) /\
    (not enable_slab_canaries_malloc ==> U32.v bytes <= U32.v max_slab_size)
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

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let slab_malloc_fast_lemma
  (arena_id: US.t{US.v arena_id < US.v nb_arenas})
  (size: U32.t)
  (i: US.t)
  : Lemma
  (requires
    US.v i < US.v nb_size_classes /\
    U32.v size <= U32.v (L.index sc_list (US.v i)).sc
  )
  (ensures
    US.fits (US.v arena_id * US.v nb_size_classes) /\
    US.fits (US.v arena_id * US.v nb_size_classes + US.v i) /\
    US.v arena_id * US.v nb_size_classes + US.v i < TLA.length sizes /\
    (let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
    U32.v size <= U32.v (Seq.index (G.reveal sc_all.g_size_classes) (US.v idx)).data.size.sc
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
  assert (size3 == size2)
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
    set_canary ptr size.sc;
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
    diff' < US.v sc_slab_region_size /\
    (diff' % U32.v sc.data.size.slab_size) % U32.v sc.data.size.sc == 0 /\
    A.length ptr == U32.v sc.data.size.sc /\
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
    // If ptr is within the size class sc
    same_base_array sc.slab_region ptr /\
    A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region)) >= 0 /\
    A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region)) < US.v sc_slab_region_size /\
    // and it is aligned on the slots
    ((A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region))) % U32.v sc.size.slab_size) % U32.v sc.size.sc = 0
  )
  // then its length is the length of a slot
  ==> A.length ptr == U32.v sc.size.sc

/// Elimination lemma for `within_size_class_i`, triggering F* to prove the precondition
/// of the implication
val elim_within_size_class_i (ptr:A.array U8.t) (i:nat{i < Seq.length sc_all.g_size_classes}) (size:sc_full)
  : Lemma
  (requires (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    size == sc.data.size /\
    within_size_class_i ptr sc.data /\
    same_base_array sc.data.slab_region ptr /\
    A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region)) >= 0 /\
    A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region)) < US.v sc_slab_region_size /\
    ((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc_all.slab_region))) % U32.v size.slab_size) % U32.v size.sc = 0))
  (ensures (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    ((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region))) % U32.v size.slab_size) % U32.v size.sc = 0 /\
    A.length ptr == U32.v size.sc
  ))

let aux_lemma
  (n x1 y1 x2 y2: nat)
  : Lemma
  (requires
    x1 > 0 /\ y1 > 0 /\
    x1 == x2 /\ y1 == y2
  )
  (ensures
    (n % x1) % y1 == (n % x2) % y2
  )
  =
  ()

#push-options "--fuel 0 --ifuel 1 --z3rlimit 150"// --query_stats --split_queries always"
let elim_within_size_class_i ptr i size
  =
  let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
  assert (size.sc == sc.data.size.sc);
  assert (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.data.slab_region)) >= 0);
  assert (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.data.slab_region)) < US.v sc_slab_region_size);
  assert (((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc_all.slab_region))) % U32.v size.slab_size) % U32.v size.sc = 0);
  aux_lemma (A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc_all.slab_region)))
    (U32.v size.slab_size)
    (U32.v size.sc)
    (U32.v sc.data.size.slab_size)
    (U32.v sc.data.size.sc);
  assert (((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc_all.slab_region))) % U32.v sc.data.size.slab_size) % U32.v sc.data.size.sc = 0);
  let off_ptr = A.offset (A.ptr_of ptr) in
  let off1 = A.offset (A.ptr_of (G.reveal sc_all.slab_region)) in
  let off2 = A.offset (A.ptr_of (G.reveal sc.data.slab_region)) in
  assert (off2 - off1 = i * US.v sc_slab_region_size);
  assert (off_ptr - off1 = off_ptr - off2 + i * US.v sc_slab_region_size);
  assert (i * US.v sc_slab_region_size == i * US.v sc.data.size.md_max * U32.v sc.data.size.slab_size);
  Math.Lemmas.lemma_mod_plus
    (off_ptr - off2)
    (i * US.v sc.data.size.md_max)
    (U32.v sc.data.size.slab_size);
  assert (
    (off_ptr - off1) % U32.v sc.data.size.slab_size
    ==
    (off_ptr - off2) % U32.v sc.data.size.slab_size
  )
#pop-options

let within_size_classes_pred (ptr:A.array U8.t) : prop =
  forall (i:nat{i < Seq.length sc_all.g_size_classes}).
    within_size_class_i ptr (Seq.index (G.reveal sc_all.g_size_classes) i).data

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let mod_lt (a b: US.t)
  : Lemma
  (requires US.v b > 0)
  (ensures
    US.v (US.rem a b) = (US.v a) % (US.v b) /\
    US.v (US.rem a b) < US.v b)
  = ()
#pop-options

open Main

#restart-solver

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let slab_getsize ptr =
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
  assert (US.v index < US.v nb_size_classes * US.v nb_arenas);
  assert (TLA.length sizes == US.v nb_size_classes * US.v nb_arenas);
  assert (US.v index < TLA.length sizes);
  let size = TLA.get sizes index in
  sizes_t_pred_elim sizes;
  let index' = G.hide (US.v index % US.v nb_size_classes) in
  assert (size = L.index sc_list index');
  assert (U32.v size.sc <= U32.v max_slab_size) by (let open FStar.Tactics in set_fuel 1; set_ifuel 1);
  if enable_sc_fast_selection then (
    sc_selection_is_exact1 index';
    sc_selection_is_exact2 index';
    let index'' = G.hide (sc_selection size.sc) in
    assert (L.index sc_list (G.reveal index') == L.index sc_list (US.v (G.reveal index'')));
    assert (size = L.index sc_list (US.v (G.reveal index'')))
  ) else ();
  let rem_slab = US.rem diff_sz sc_slab_region_size in
  let rem_slot = US.rem diff_sz (US.uint32_to_sizet size.slab_size) in
  // TODO: some refactor needed wrt SlotsFree
  if US.rem rem_slot (US.uint32_to_sizet size.sc) = 0sz then (
    (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
    assert (A.offset (A.ptr_of (G.reveal sc).data.slab_region) == A.offset (A.ptr_of sc_all.slab_region) + (US.v index) * (US.v sc_slab_region_size));
    assert (US.v rem_slab == A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc).data.slab_region));
    mod_lt diff_sz sc_slab_region_size;
    assert (US.v rem_slab < US.v sc_slab_region_size);
    mod_lt diff_sz (u32_to_sz size.slab_size);
    assert (US.v rem_slot == (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc_all.slab_region)) % (U32.v size.slab_size));
    mod_lt rem_slot (US.uint32_to_sizet size.sc);
    (**) elim_within_size_class_i ptr (US.v index) size;
    (**) assert (A.length ptr == U32.v size.sc);
    if enable_slab_canaries_malloc then
      return (US.uint32_to_sizet (size.sc `U32.sub` 2ul))
    else
      return (US.uint32_to_sizet size.sc)
  ) else (
    // invalid pointer
    return 0sz
  )
#pop-options

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let slab_free ptr =
  SAA.within_bounds_elim
    (A.split_l sc_all.slab_region 0sz)
    (A.split_r sc_all.slab_region slab_region_size)
    ptr;
  UP.fits_lt
    (A.offset (A.ptr_of ptr)
    -
    A.offset (A.ptr_of (A.split_l sc_all.slab_region 0sz)))
    (US.v full_slab_region_size);
  let diff = A.ptrdiff
    ptr
    (A.split_l sc_all.slab_region 0sz) in
  let diff_sz = UP.ptrdifft_to_sizet diff in
  let index = US.div diff_sz sc_slab_region_size in
  lemma_div_lt (US.v sc_slab_region_size) (US.v nb_size_classes) (US.v nb_arenas) (US.v diff_sz);
  total_nb_sc_lemma ();
  assert (US.v index < US.v nb_size_classes * US.v nb_arenas);
  assert (TLA.length sizes == US.v nb_size_classes * US.v nb_arenas);
  assert (US.v index < TLA.length sizes);
  let size = TLA.get sizes index in
  let rem_slab = US.rem diff_sz sc_slab_region_size in
  let rem_slot = US.rem diff_sz (US.uint32_to_sizet size.slab_size) in
  // TODO: some refactor needed wrt SlotsFree
  if US.rem rem_slot (US.uint32_to_sizet size.sc) = 0sz then (
    (**) let sc = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
    assert (A.offset (A.ptr_of (G.reveal sc).data.slab_region) == A.offset (A.ptr_of sc_all.slab_region) + (US.v index) * (US.v sc_slab_region_size));
    assert (US.v rem_slab == A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc).data.slab_region));
    mod_lt diff_sz sc_slab_region_size;
    assert (US.v rem_slab < US.v sc_slab_region_size);
    mod_lt diff_sz (u32_to_sz size.slab_size);
    assert (US.v rem_slot == (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc_all.slab_region)) % (U32.v size.slab_size));
    mod_lt rem_slot (US.uint32_to_sizet size.sc);
    (**) elim_within_size_class_i ptr (US.v index) size;
    (**) assert (A.length ptr == U32.v size.sc);
    if enable_slab_canaries_free then (
      enable_slab_canaries_lemma ();
      let magic1 = A.index ptr (US.uint32_to_sizet (size.sc `U32.sub` 2ul)) in
      let magic2 = A.index ptr (US.uint32_to_sizet (size.sc `U32.sub` 1ul)) in
      if magic1 = slab_canaries_magic1 && magic2 = slab_canaries_magic2 then
        slab_free' index ptr rem_slab
      else
        // Canary was overwritten
        return false
    ) else (
      slab_free' index ptr rem_slab
    )
  ) else (
    return false
  )
#pop-options
