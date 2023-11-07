module Main.Meta

friend Config

[@@ reduce_attr]
inline_for_extraction noextract
let sc_list: l:list sc{US.v nb_size_classes == List.length sc_list}
= normalize_term sc_list

module L2 = FStar.List.Tot

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let f (k:nat{k <= 8}) : sc = admit (); U32.uint_to_t (pow2 (k + 4))
#pop-options

let bound (x bound: nat) : bool
  =
  x <= pow2 bound

assume val ceil_log (x: U64.t)
  : Pure U32.t
  (requires
    U64.v x > 0)
  (ensures fun r ->
    bound (U64.v x) (U32.v r) /\
    (forall (r':U32.t{bound (U64.v x) (U32.v r')}).
      U32.v r <= U32.v r')
  )

#push-options "--fuel 0 --ifuel 0"
let ceil_log_lemma_le (x y: U64.t)
  : Lemma
  (requires
    0 < U64.v x /\
    0 < U64.v y /\
    U64.v x <= U64.v y
  )
  (ensures (
    let k1 = ceil_log x in
    let k2 = ceil_log y in
    U32.v k1 <= U32.v k2
  ))
  =
  let k1 = ceil_log x in
  let k2 = ceil_log y in
  if U32.v k1 > U32.v k2 then (
    Math.Lemmas.pow2_lt_compat (U32.v k1) (U32.v k2)
  ) else ()

let ceil_log_lemma_witness (x: U64.t) (k: U32.t)
  : Lemma
  (requires
    U32.v k > 0 /\
    pow2 (U32.v k - 1) < U64.v x /\
    U64.v x <= pow2 (U32.v k)
  )
  (ensures
    k == ceil_log x
  )
  =
  Classical.forall_intro_2 (
    Classical.move_requires_2 (
      FStar.Math.Lemmas.pow2_le_compat
    )
  )
#pop-options

module G = FStar.Ghost

let ceil_log_specialized (x: U32.t)
  : Pure U32.t
  (requires
    U32.v x >= 14 /\
    U32.v x <= U32.v page_size)
  (ensures fun r ->
    U32.v r >= 4 /\
    U32.v r <= 12 /\
    bound (U32.v x) (U32.v r)
  )
  =
  let page_size_as_u64 = G.hide (FStar.Int.Cast.uint32_to_uint64 page_size) in
  [@inline_let] let x_as_u64 = FStar.Int.Cast.uint32_to_uint64 x in
  ceil_log_lemma_witness 14UL 4ul;
  ceil_log_lemma_witness (G.reveal page_size_as_u64) 12ul;
  ceil_log_lemma_le 14UL x_as_u64;
  ceil_log_lemma_le x_as_u64 (G.reveal page_size_as_u64);
  ceil_log x_as_u64

let temp (_:unit)
  =
  let base = Seq.seq_of_list [0; 1; 2; 3; 4; 5; 6; 7; 8] in
  let t = Seq.map_seq f base in
  Seq.map_seq_len f base;
  let t' = Seq.seq_to_list t in
  admit ();
  Seq.lemma_eq_intro (Seq.seq_of_list sc_list) t
  //assert_norm (sc_list == t)

  //Seq.seq_to_list
  //List.Tot.map f [0; 1; 2; 3; 4; 5; 6; 7; 8])


let sc_selection (x: U32.t)
  : Pure (US.t)
  (requires
    U32.v x >= 14 /\
    U32.v x <= U32.v page_size)
  (ensures fun r ->
    US.v r < L2.length sc_list /\
    U32.v x <= U32.v (L2.index sc_list (US.v r))
  )
  =
  assert_norm (L2.length sc_list = 9);
  assert_norm (sc_list == List.Tot.map f [0; 1; 2; 3; 4; 5; 6; 7; 8]);
  assume (forall (x:nat{x < 9}). U32.v (L2.index sc_list x) == pow2 (x + 4));
  let idx = ceil_log_specialized x in
  let idx' = U32.sub idx 4ul in
  assume (US.fits_u32);
  US.uint32_to_sizet idx'

let sc_size (x: US.t)
  : Pure (U32.t)
  (requires US.v x < L2.length sc_list)
  (ensures fun r ->
    r = L2.index sc_list (US.v x)
  )
  =
  assert_norm (L2.length sc_list = 9);
  assert_norm (sc_list == List.Tot.map f [0; 1; 2; 3; 4; 5; 6; 7; 8]);
  assume (forall (x:nat{x < 9}). U32.v (L2.index sc_list x) == pow2 (x + 4));
  admit ();
  U32.shift_left 1ul (U32.add (US.sizet_to_uint32 x) 4ul)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let slab_malloc arena_id bytes =
  let bytes = if U32.lt bytes 14ul then 14ul else bytes in
  if enable_slab_canaries_malloc then (
    let bytes = U32.add bytes 2ul in
    let idx = sc_selection bytes in
    let idx' = US.add (US.mul arena_id nb_size_classes) idx in
    admit ();
    let ptr = slab_malloc_one idx' bytes in
    if is_null ptr then (
      return ptr
    ) else (
      let size = sc_size idx in
      elim_live_null_or_varray ptr;
      sladmit ();
      upd ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) slab_canaries_magic1;
      upd ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) slab_canaries_magic2;
      intro_live_null_or_varray ptr;
      return ptr
    )
  ) else (
    let idx = sc_selection bytes in
    let idx = US.add (US.mul arena_id nb_size_classes) idx in
    slab_malloc_one idx bytes
  )
#pop-options




//type selection' = (f:(x:U32.t{U32.v x <= U32.v page_size}) -> US.t)
//
//#push-options "--print_universes"
//
//type selection = f:selection'{
//  forall (x: U32.t{
//    16 <= U32.v x /\
//    U32.v x <= U32.v page_size
//  }). (
//    US.v (f x) < L.length sc_list /\
//    U32.v x <= U32.v (L.index sc_list (US.v (f x)))
//  )
//}



#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
  //if enable_slab_canaries_malloc then
  //  (slab_malloc_canary_i sc_list 0sz) arena_id bytes
  //else
  //  (slab_malloc_i sc_list 0sz) arena_id bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_aligned_alloc arena_id alignment bytes =
  if enable_slab_canaries_malloc then
    (slab_aligned_alloc_canary_i sc_list 0sz) arena_id alignment bytes
  else
    (slab_aligned_alloc_i sc_list 0sz) arena_id alignment bytes
#pop-options

#restart-solver

open FStar.Mul
#push-options "--z3rlimit 50"
inline_for_extraction noextract
let slab_free' (i:US.t{US.v i < US.v nb_size_classes * US.v nb_arenas}) (ptr: array U8.t) (diff: US.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun h0 ->
    let sc = Seq.index (G.reveal sc_all.g_size_classes) (US.v i) in
    let diff' = offset (ptr_of ptr) - offset (ptr_of sc.data.slab_region) in
    same_base_array ptr sc.data.slab_region /\
    0 <= diff' /\
    diff' < US.v slab_size /\
    (diff' % U32.v page_size) % U32.v sc.data.size == 0 /\
    A.length ptr == U32.v sc.data.size /\
    US.v diff = diff')
  (ensures fun h0 _ h1 -> True)
  =
  let sc = ROArray.index sc_all.ro_perm i in
  L.acquire sc.lock;
  let sc = ROArray.index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  let res = deallocate_size_class sc.data ptr diff in
  let sc = ROArray.index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  L.release sc.lock;
  return res

/// Precondition of free, capturing that a client must return an array corresponding to the
/// entire memory provided by the allocator:
/// If a pointer is within a size class and aligned with
/// the slots, then its length corresponds to the slot size
let within_size_class_i (ptr:A.array U8.t) (sc: size_class_struct) : prop = (
  // If ptr is within the size class sc
  same_base_array sc.slab_region ptr /\
  A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region)) >= 0 /\
  A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region)) < US.v slab_size /\
  // and it is aligned on the slots
  ((A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region))) % U32.v page_size) % U32.v sc.size = 0) ==>
    // then its length is the length of a slot
    A.length ptr == U32.v sc.size

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
/// Elimination lemma for `within_size_class_i`, triggering F* to prove the precondition
/// of the implication
let elim_within_size_class_i (ptr:A.array U8.t) (i:nat{i < Seq.length sc_all.g_size_classes}) (size:sc)
  : Lemma
  (requires (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    size == sc.data.size /\
    within_size_class_i ptr sc.data /\
    same_base_array sc.data.slab_region ptr /\
    A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region)) >= 0 /\
    A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region)) < US.v slab_size /\
    ((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc_all.slab_region))) % U32.v page_size) % U32.v size = 0))
  (ensures (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    ((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region))) % U32.v page_size) % U32.v size = 0 /\
    A.length ptr == U32.v size
  ))
  =
  let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
  let off_ptr = A.offset (A.ptr_of ptr) in
  let off1 = A.offset (A.ptr_of (G.reveal sc_all.slab_region)) in
  let off2 = A.offset (A.ptr_of (G.reveal sc.data.slab_region)) in
  assert (off2 - off1 = i * US.v slab_size);
  assert (off_ptr - off1 = off_ptr - off2 + i * US.v slab_size);
  assert (i * US.v slab_size == i * US.v metadata_max * U32.v page_size);
  Math.Lemmas.lemma_mod_plus
    (off_ptr - off2)
    (i * US.v metadata_max)
    (U32.v page_size);
  assert (
    (off_ptr - off1) % U32.v page_size
    ==
    (off_ptr - off2) % U32.v page_size
  )
#pop-options

let within_size_classes_pred (ptr:A.array U8.t) : prop =
  forall (i:nat{i < Seq.length sc_all.g_size_classes}).
    within_size_class_i ptr (Seq.index (G.reveal sc_all.g_size_classes) i).data

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

open MiscArith
let slab_getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (fun _ ->
   A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (requires fun _ ->
    within_size_classes_pred ptr /\
    SAA.within_bounds
      (A.split_l (G.reveal sc_all.slab_region) 0sz)
      ptr
      (A.split_r (G.reveal sc_all.slab_region) slab_region_size)
  )
  (ensures fun h0 r h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    (r <> 0sz ==>
      (enable_slab_canaries_malloc ==>
        A.length ptr == US.v r + 2
      ) /\
      (not enable_slab_canaries_malloc ==>
        A.length ptr == US.v r
      )
    )
  )
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
  assert (US.v slab_size > 0);
  let index = US.div diff_sz slab_size in
  lemma_div_le (US.v slab_size) (US.v nb_size_classes) (US.v nb_arenas) (US.v diff_sz);
  let size = ROArray.index sc_all.ro_sizes index in
  let rem_slab = US.rem diff_sz slab_size in
  let rem_slot = US.rem diff_sz (u32_to_sz page_size) in
  // TODO: some refactor needed wrt SlotsFree
  if US.rem rem_slot (US.uint32_to_sizet size) = 0sz then (
    (**) let sc = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    //lemma_nlarith_aux diff_sz size;
    (**) elim_within_size_class_i ptr (US.v index) size;
    (**) assert (A.length ptr == U32.v size);
    if enable_slab_canaries_malloc then
      return (US.uint32_to_sizet (size `U32.sub` 2ul))
    else
      return (US.uint32_to_sizet size)
  ) else (
    // invalid pointer
    return 0sz
  )

#restart-solver

let slab_free ptr =
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
  assert (ptr_of (A.split_l sc_all.slab_region 0sz) == ptr_of (sc_all.slab_region));
  assert (US.v slab_size > 0);
  let index = US.div diff_sz slab_size in
  lemma_div_le (US.v slab_size) (US.v nb_size_classes) (US.v nb_arenas) (US.v diff_sz);
  (**) let g_sc = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  (**) assert (size_class_pred sc_all.slab_region (G.reveal g_sc) (US.v index));
  let size = ROArray.index sc_all.ro_sizes index in
  let rem_slab = US.rem diff_sz slab_size in
  let rem_slot = US.rem diff_sz (u32_to_sz page_size) in
  // TODO: some refactor needed wrt SlotsFree
  if US.rem rem_slot (US.uint32_to_sizet size) <> 0sz then (
    return false
  ) else (
    (**) let sc = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
    (**) elim_within_size_class_i ptr (US.v index) size;
    (**) assert (A.length ptr == U32.v size);
    if enable_slab_canaries_free then (
      enable_slab_canaries_lemma ();
      let magic1 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) in
      let magic2 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) in
      if magic1 = slab_canaries_magic1 && magic2 = slab_canaries_magic2 then
        slab_free' index ptr rem_slab
      else
        // Canary was overwritten
        return false
    ) else (
      slab_free' index ptr rem_slab
    )
  )
