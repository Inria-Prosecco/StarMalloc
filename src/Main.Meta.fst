module Main.Meta

friend Config

[@@ reduce_attr]
inline_for_extraction noextract
let sc_list: l:list sc_union{US.v nb_size_classes == List.length sc_list}
= normalize_term sc_list

/// Number of arenas as a nat, for specification purposes. Not relying on US.v
/// allows better normalization for extraction
[@@ reduce_attr]
inline_for_extraction noextract
let nb_arenas_nat : n:nat{n == US.v nb_arenas /\ n < pow2 32}
= normalize_term (US.v nb_arenas)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
open FStar.Mul
let total_nb_sc : n:nat{
  n == US.v nb_size_classes * US.v nb_arenas /\
  n == US.v nb_size_classes * nb_arenas_nat
}
=
assert_norm ((US.v nb_size_classes * US.v nb_arenas) < pow2 32);
US.fits_u32_implies_fits (US.v nb_size_classes * US.v nb_arenas);
normalize_term (US.v nb_size_classes * US.v nb_arenas)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
/// Duplicating the list of size_classes sizes for each arena, which enables a simpler
/// initialization directly using the mechanism in place for one arena
[@@ reduce_attr]
inline_for_extraction noextract
let rec arena_sc_list'
  (i:nat{i <= US.v nb_arenas})
  (acc:list sc_union{List.length acc = i * US.v nb_size_classes})
  : Tot (l:list sc_union{List.length l == total_nb_sc})
  (decreases (US.v nb_arenas - i))
  =
  calc (==) {
    nb_arenas_nat * US.v nb_size_classes;
    == { FStar.Math.Lemmas.swap_mul nb_arenas_nat (US.v nb_size_classes) }
    US.v nb_size_classes * nb_arenas_nat;
  };
  assert (total_nb_sc == nb_arenas_nat * US.v nb_size_classes);
  if i = nb_arenas_nat then acc
  else (
    List.append_length acc sc_list;
    admit ();
    arena_sc_list' (i + 1) (acc `List.append` sc_list)
  )

/// Fuel needed to establish that the length of [] is 0
#push-options "--fuel 1"
[@@ reduce_attr]
let arena_sc_list = arena_sc_list' 0 []
#pop-options

//let init_sizes (_:unit)
//  : SteelTop (sizes_t) false
//  (fun _ -> emp)
//  (fun _ r _ ->
//    TLA.length r == total_nb_sc /\
//    (forall (k:U32.t{U32.v k < total_nb_sc}).
//      TLA.get r k == List.Tot.index arena_sc_list (U32.v k))
//  )
//  =
//  let v = TLA.create #sc arena_sc_list in
//  return v

#restart-solver

let sizes : sizes_t =
  normalize_term_spec arena_sc_list;
  TLA.create #sc_union (normalize_term arena_sc_list)

type tuple4 = {
  x: US.t;
  y: US.t;
  z: US.t;
  w: US.t;
}

let gen_arena_sizes
  (_:unit)
  : Pure tuple4
  (requires
    True
  )
  (ensures fun r ->
    hidden_pred sc_list_sc sc_list_ex
      nb_size_classes
      nb_size_classes_sc
      nb_size_classes_sc_ex
      r.y
      r.z
      r.w /\
    hidden_pred2
      nb_size_classes
      r.x
  )
  =
  admit ();
  //assume (
  //  US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_region_size * US.v nb_arenas)
  //);
  let arena_slab_region_size
    = US.mul sc_slab_region_size nb_size_classes in
  let arena_md_bm_region_size
    = US.mul (US.mul metadata_max 4sz) nb_size_classes_sc in
  let arena_md_bm_region_b_size
    = US.mul metadata_max_ex nb_size_classes_sc_ex in
  let arena_md_region_size
    = US.add
      (US.mul metadata_max nb_size_classes_sc)
      (US.mul metadata_max_ex nb_size_classes_sc_ex)
  in
  {
    x = arena_slab_region_size;
    y = arena_md_bm_region_size;
    z = arena_md_bm_region_b_size;
    w = arena_md_region_size
  }

friend Main

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
let init
  (_:unit)
  : SteelTop size_classes_all false
  (fun _ -> emp)
  (fun _ r _ -> True)
  =
  let arena_sizes = gen_arena_sizes () in
  assume (
    US.fits (US.v nb_size_classes * US.v nb_arenas) /\
    US.fits (US.v arena_sizes.x * US.v nb_arenas) /\
    US.fits (US.v arena_sizes.y * US.v nb_arenas) /\
    US.fits (US.v arena_sizes.z * US.v nb_arenas) /\
    US.fits (US.v arena_sizes.w * US.v nb_arenas)
  );
  let slab_region = mmap_u8_init (US.mul arena_sizes.x nb_arenas) in
  let md_bm_region = mmap_u64_init (US.mul arena_sizes.y nb_arenas) in
  let md_bm_region_b = mmap_bool_init (US.mul arena_sizes.z nb_arenas) in
  let md_region = mmap_cell_status_init (US.mul arena_sizes.w nb_arenas) in
  let size_classes = mmap_sc_init (US.mul nb_size_classes nb_arenas) in
  //Pervasives.norm
  //[
  //  //delta_attr [`%reduce_attr];
  //  delta_only [`%init_n_first_arenas];
  //  iota; zeta; primops
  //]
  //admit ();
  //init_one_arena
  //  0sz
  //  sc_list_sc
  //  sc_list_ex
  //  nb_size_classes_sc nb_size_classes_sc_ex
  //  nb_size_classes
  //  nb_arenas
  //  arena_sizes.x
  //  arena_sizes.y
  //  arena_sizes.z
  //  arena_sizes.w
  //  slab_region
  //  md_bm_region
  //  md_bm_region_b
  //  md_region
  //  size_classes
  //  sizes;
  //sladmit ();



  init_all_arenas
    sc_list_sc sc_list_ex
    nb_size_classes_sc nb_size_classes_sc_ex
    nb_size_classes
    arena_sizes.x
    arena_sizes.y
    arena_sizes.z
    arena_sizes.w
    nb_arenas
    slab_region
    md_bm_region
    md_bm_region_b
    md_region
    size_classes
    sizes;

  let g_size_classes = gget (varray size_classes) in
  let ro_perm = create_ro_array size_classes g_size_classes in

  [@inline_let]
  let s : size_classes_all = {
    size_classes;
    g_size_classes;
    //g_sizes;
    ro_perm;
    //ro_sizes;
    slab_region;
  } in
  return s

#reset-options "--fuel 1 --ifuel 1"

#push-options "--print_implicits"

#push-options "--warn_error '-272'"
let sc_all : size_classes_all = init ()
#pop-options

#restart-solver

#push-options "--fuel 0 --ifuel 0 --query_stats"
inline_for_extraction noextract
let slab_malloc_one (i:US.t{US.v i < total_nb_sc}) (bytes: U32.t)
  : Steel
  (array U8.t)
  emp (fun r -> null_or_varray r)
  (requires fun _ ->
    U32.v bytes <= U32.v (get_u32 (Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size)
  )
  (ensures fun _ r _ ->
    let size = get_u32 (Seq.index sc_all.g_size_classes (US.v i)).data.size in
    U32.v size > 0 /\
    not (is_null r) ==> (
      A.length r == U32.v size /\
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16sz /\
      ((U32.v page_size) % (U32.v size) == 0 ==> array_u8_alignment r (u32_to_sz size))
    )
  )
  =
  admit ();
  let sc = index sc_all.ro_perm i in
  L.acquire sc.lock;
  let sc = index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  let ptr = allocate_size_class sc.data in
  let sc = index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  L.release sc.lock;
  return ptr
#pop-options

let cons_implies_positive_length (#a: Type) (l: list a)
  : Lemma
  (requires Cons? l)
  (ensures List.length l > 0)
  = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --query_stats"
let aux_lemma
  (l:list sc_union{List.length l <= length sc_all.size_classes /\ Cons? l})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  : Lemma
  (
    (US.v arena_id) * (US.v nb_size_classes) + (US.v i) < total_nb_sc /\
    0 <= (US.v arena_id) * (US.v nb_size_classes) /\
    US.fits ((US.v arena_id) * (US.v nb_size_classes)) /\
    0 <= (US.v arena_id) * (US.v nb_size_classes) + (US.v i) /\
    US.fits ((US.v arena_id) * (US.v nb_size_classes) + (US.v i)) /\
    (let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
    let idx' = US.sizet_to_uint32 idx in
    US.v idx == U32.v idx' /\
    US.v idx < TLA.length sizes)
  )
  =
  cons_implies_positive_length l;
  assert (US.v i < US.v nb_size_classes);
  assert ((US.v arena_id) * (US.v nb_size_classes) + (US.v i) < (US.v arena_id + 1) * (US.v nb_size_classes));
  Math.Lemmas.lemma_mult_le_right (US.v nb_size_classes) (US.v arena_id + 1) (US.v nb_arenas);
  assert ((US.v arena_id) * (US.v nb_size_classes) + (US.v i) < (US.v nb_arenas) * (US.v nb_size_classes));
  Math.Lemmas.swap_mul (US.v nb_arenas) (US.v nb_size_classes);
  assert ((US.v arena_id) * (US.v nb_size_classes) + (US.v i) < total_nb_sc);
  US.fits_lte
    ((US.v arena_id) * (US.v nb_size_classes))
    ((US.v arena_id) * (US.v nb_size_classes) + (US.v i));
  US.fits_lte
    ((US.v arena_id) * (US.v nb_size_classes) + (US.v i))
    total_nb_sc;
  assert (total_nb_sc < pow2 32);
  assert (US.fits_u32);
  assert (US.fits (total_nb_sc));
  ()
#pop-options

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
/// A wrapper around slab_malloc' that performs dispatch in the size classes
/// for arena [arena_id] in a generic way.
/// The list argument is not actually used, it just serves
/// as a counter that reduces better than nats
[@@ reduce_attr]
noextract
let rec slab_malloc_i
  (l:list sc_union{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16sz /\
      Seq.length s >= 2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      aux_lemma l i arena_id;
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = get_u32 (TLA.get sizes idx) in
      admit ();
      if bytes `U32.lte` size then
        slab_malloc_one idx bytes
      else
        slab_malloc_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

#restart-solver

[@@ reduce_attr]
inline_for_extraction noextract
let set_canary
  (ptr: array U8.t)
  (size: sc)
  : Steel unit
  (null_or_varray ptr) (fun _ -> null_or_varray ptr)
  (requires fun _ ->
    not (is_null ptr) ==> A.length ptr = U32.v size)
  (ensures fun _ _ h1 ->
    let s : t_of (null_or_varray ptr)
      = h1 (null_or_varray ptr) in
    not (is_null ptr) ==> (
      Seq.length s >= 2 /\
      Seq.index s (A.length ptr - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length ptr - 1) == slab_canaries_magic2
    )
  )
  =
  assert (UInt.size (U32.v size - 2) U32.n);
  assert (UInt.size (U32.v size - 1) U32.n);
  if is_null ptr then return ()
  else (
    elim_live_null_or_varray ptr;
    upd ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) slab_canaries_magic1;
    upd ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) slab_canaries_magic2;
    intro_live_null_or_varray ptr
  )

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// A variant of slab_malloc_i adding slab canaries
[@@ reduce_attr]
noextract
let rec slab_malloc_canary_i
  (l:list sc_union{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16sz /\
      Seq.length s >= 2 /\
      Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length r - 1) == slab_canaries_magic2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      aux_lemma l i arena_id;
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = get_u32 (TLA.get sizes idx) in
      admit ();
      if bytes `U32.lte` (size `U32.sub` 2ul) then
        let ptr = slab_malloc_one idx bytes in
        set_canary ptr size;
        return ptr
      else
        slab_malloc_canary_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_malloc arena_id bytes =
  if enable_slab_canaries_malloc then (
    admit ();
    (slab_malloc_canary_i sc_list 0sz) arena_id bytes
  ) else (
    admit ();
    (slab_malloc_i sc_list 0sz) arena_id bytes
  )
#pop-options

#restart-solver

open MiscArith

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
/// `slab_aligned_alloc` works in a very similar way as `slab_malloc_i`
/// The key difference lies in the condition of the if-branch: we only
/// attempt to allocate in this size class if it satisfies the alignment
/// constraint, i.e., alignment % size == 0
[@@ reduce_attr]
noextract
let rec slab_aligned_alloc_i
  (l:list sc_union{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (alignment: (v:U32.t{U32.v v > 0 /\ (U32.v page_size) % (U32.v v) = 0}))
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16sz /\
      array_u8_alignment r (u32_to_sz alignment) /\
      Seq.length s >= 2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      aux_lemma l i arena_id;
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = get_u32 (TLA.get sizes idx) in
      admit ();
      let b = U32.eq (U32.rem page_size size) 0ul in
      if b && bytes `U32.lte` size && alignment `U32.lte` size then (
        let r = slab_malloc_one idx bytes in
        let size_ = G.hide (get_u32 (Seq.index sc_all.g_size_classes (US.v idx)).data.size) in
        assert (G.reveal size_ = size);
        assert ((U32.v page_size) % (U32.v (G.reveal size_ )) = 0);
        assert_norm (U32.v page_size = pow2 12);
        alignment_lemma (U32.v page_size) 12 (U32.v alignment) (U32.v size);
        assert (U32.v size % U32.v alignment = 0);
        array_u8_alignment_lemma2 r (u32_to_sz size) (u32_to_sz alignment);
        return r
      ) else (
        slab_aligned_alloc_i tl (i `US.add` 1sz) arena_id alignment bytes
      )
#pop-options

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
/// Version of `slab_aligned_alloc_i` with slab canaries
[@@ reduce_attr]
noextract
let rec slab_aligned_alloc_canary_i
  (l:list sc_union{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (alignment: (v:U32.t{U32.v v > 0 /\ (U32.v page_size) % (U32.v v) = 0}))
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16sz /\
      array_u8_alignment r (u32_to_sz alignment) /\
      Seq.length s >= 2 /\
      Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length r - 1) == slab_canaries_magic2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      aux_lemma l i arena_id;
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = get_u32 (TLA.get sizes idx) in
      admit ();
      let b = U32.eq (U32.rem page_size size) 0ul in
      if b && bytes `U32.lte` (size `U32.sub` 2ul) && alignment `U32.lte` size then (
        let ptr = slab_malloc_one idx bytes in
        let size_ = G.hide (get_u32 (Seq.index sc_all.g_size_classes (US.v idx)).data.size) in
        assert (G.reveal size_ = size);
        assert ((U32.v page_size) % (U32.v (G.reveal size_ )) = 0);
        assert_norm (U32.v page_size = pow2 12);
        alignment_lemma (U32.v page_size) 12 (U32.v alignment) (U32.v size);
        assert (U32.v size % U32.v alignment = 0);
        array_u8_alignment_lemma2 ptr (u32_to_sz size) (u32_to_sz alignment);
        set_canary ptr size;
        return ptr
      ) else (
        slab_aligned_alloc_canary_i tl (i `US.add` 1sz) arena_id alignment bytes
      )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_aligned_alloc arena_id alignment bytes =
  admit ();
  if enable_slab_canaries_malloc then
    (slab_aligned_alloc_canary_i sc_list 0sz) arena_id alignment bytes
  else
    (slab_aligned_alloc_i sc_list 0sz) arena_id alignment bytes
#pop-options

#restart-solver

#push-options "--fuel 0 --fuel 0 --z3rlimit 50"
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
    (diff' % U32.v page_size) % U32.v (get_u32 sc.data.size) == 0 /\
    A.length ptr == U32.v (get_u32 sc.data.size) /\
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
#pop-options

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
  ((A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc.slab_region))) % U32.v page_size) % U32.v (get_u32 sc.size) = 0) ==>
    // then its length is the length of a slot
    A.length ptr == U32.v (get_u32 sc.size)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
/// Elimination lemma for `within_size_class_i`, triggering F* to prove the precondition
/// of the implication
let elim_within_size_class_i (ptr:A.array U8.t) (i:nat{i < Seq.length sc_all.g_size_classes}) (size:sc_union)
  : Lemma
  (requires (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    size == sc.data.size /\
    within_size_class_i ptr sc.data /\
    same_base_array sc.data.slab_region ptr /\
    A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region)) >= 0 /\
    A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region)) < US.v slab_size /\
    ((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc_all.slab_region))) % U32.v page_size) % U32.v (get_u32 size) = 0))
  (ensures (
    let sc : size_class = G.reveal (Seq.index sc_all.g_size_classes i) in
    ((A.offset (A.ptr_of ptr) - A.offset (ptr_of (G.reveal sc.data.slab_region))) % U32.v page_size) % U32.v (get_u32 size) = 0 /\
    A.length ptr == U32.v (get_u32 size)
  ))
  =
  admit ();
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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let mod_lt (a b: US.t)
  : Lemma
  (requires US.v b > 0)
  (ensures
    US.v (US.rem a b) = (US.v a) % (US.v b) /\
    US.v (US.rem a b) < US.v b)
  = ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --query_stats"
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
  admit ();
  let index = US.div diff_sz sc_slab_region_size in
  lemma_div_lt (US.v sc_slab_region_size) (US.v nb_size_classes) (US.v nb_arenas) (US.v diff_sz);
  assert (US.v index < US.v nb_size_classes * US.v nb_arenas);
  let size = get_u32 (TLA.get sizes index) in
  let index1 = US.rem index nb_size_classes in
  if US.lt index1 nb_size_classes_sc then (
    let rem_slab = US.rem diff_sz sc_slab_region_size in
    let rem_slot = US.rem diff_sz (u32_to_sz page_size) in
    // TODO: some refactor needed wrt SlotsFree
    if US.rem rem_slot (US.uint32_to_sizet size) = 0sz then (
      (**) let sc : G.erased size_class = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
      assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
      assert (A.offset (A.ptr_of (G.reveal sc).data.slab_region) == A.offset (A.ptr_of sc_all.slab_region) + (US.v index) * (US.v sc_slab_region_size));
      assert (US.v rem_slab == A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc).data.slab_region));
      mod_lt diff_sz sc_slab_region_size;
      assert (US.v rem_slab < US.v sc_slab_region_size);
      mod_lt diff_sz (u32_to_sz page_size);
      assert (US.v rem_slot == (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc_all.slab_region)) % (U32.v page_size));
      mod_lt rem_slot (US.uint32_to_sizet size);
      //(**) elim_within_size_class_i ptr (US.v index) size;
      (**) assert (A.length ptr == U32.v size);
      if enable_slab_canaries_malloc then
        return (US.uint32_to_sizet (size `U32.sub` 2ul))
      else
        return (US.uint32_to_sizet size)
    ) else (
      // invalid pointer
      return 0sz
    )
  ) else (
    let rem_slot = US.rem diff_sz slab_size in
    if rem_slot = 0sz then (
      if enable_slab_canaries_malloc then
        return (US.uint32_to_sizet (size `U32.sub` 2ul))
      else
        return (US.uint32_to_sizet size)
    ) else (
      return 0sz
    )
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
  admit ();
  let index = US.div diff_sz sc_slab_region_size in
  lemma_div_lt (US.v sc_slab_region_size) (US.v nb_size_classes) (US.v nb_arenas) (US.v diff_sz);
  assert (US.v index < US.v nb_size_classes * US.v nb_arenas);
  let size = get_u32 (TLA.get sizes index) in
  let index1 = US.rem index nb_size_classes in
  if US.lt index1 nb_size_classes_sc then (
    let rem_slab = US.rem diff_sz sc_slab_region_size in
    let rem_slot = US.rem diff_sz (u32_to_sz page_size) in
    // TODO: some refactor needed wrt SlotsFree
    if US.rem rem_slot (US.uint32_to_sizet size) = 0sz then (
      (**) let sc = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
      assert (size_class_pred sc_all.slab_region (G.reveal sc) (US.v index));
      assert (A.offset (A.ptr_of (G.reveal sc).data.slab_region) == A.offset (A.ptr_of sc_all.slab_region) + (US.v index) * (US.v sc_slab_region_size));
      assert (US.v rem_slab == A.offset (A.ptr_of ptr) - A.offset (A.ptr_of (G.reveal sc).data.slab_region));
      mod_lt diff_sz sc_slab_region_size;
      assert (US.v rem_slab < US.v sc_slab_region_size);
      mod_lt diff_sz (u32_to_sz page_size);
      assert (US.v rem_slot == (A.offset (A.ptr_of ptr) - A.offset (A.ptr_of sc_all.slab_region)) % (U32.v page_size));
      mod_lt rem_slot (US.uint32_to_sizet size);
      //(**) elim_within_size_class_i ptr (US.v index) size;
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
    ) else (
      return false
    )
  ) else (
    let rem_slab = US.rem diff_sz sc_slab_region_size in
    let rem_slot = US.rem diff_sz slab_size in
    if rem_slot = 0sz then (
      slab_free' index ptr rem_slab
    ) else (
      return false
    )

  )
#pop-options
