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

open FStar.Mul

#push-options "--fuel 0 --ifuel 0"
let total_nb_sc : n:nat{
  n == US.v nb_size_classes * US.v nb_arenas /\
  n == US.v nb_size_classes * nb_arenas_nat
}
=
assert_norm ((US.v nb_size_classes * US.v nb_arenas) < pow2 32);
US.fits_u32_implies_fits (US.v nb_size_classes * US.v nb_arenas);
normalize_term (US.v nb_size_classes * US.v nb_arenas)
#pop-options

let total_nb_sc_lemma _ = ()

module ML = MiscList

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// Duplicating the list of size_classes sizes for each arena, which enables a simpler
/// initialization directly using the mechanism in place for one arena
[@@ reduce_attr]
inline_for_extraction noextract
let rec arena_sc_list'
  (i:nat{i <= US.v nb_arenas})
  (acc:list sc_union{
    List.length acc = i * US.v nb_size_classes /\
    (forall (k:nat{k < L.length acc}). L.index acc k == L.index sc_list (k % (US.v nb_size_classes)))
  })
  : Tot (l:list sc_union{
    L.length l == total_nb_sc /\
    (forall (k:nat{k < L.length l}). L.index l k == L.index sc_list (k % (US.v nb_size_classes)))
  })
  (decreases (US.v nb_arenas - i))
  =
  calc (==) {
    nb_arenas_nat * US.v nb_size_classes;
    == { FStar.Math.Lemmas.swap_mul nb_arenas_nat (US.v nb_size_classes) }
    US.v nb_size_classes * nb_arenas_nat;
  };
  assert (total_nb_sc == nb_arenas_nat * US.v nb_size_classes);
  if i = nb_arenas_nat then (
    acc
  ) else (
    List.append_length acc sc_list;
    let l = acc `List.append` sc_list in
    ML.lemma_append_repeat #sc_union i sc_list (US.v nb_size_classes) acc;
    assert (forall (k:nat{k < L.length acc}).
      L.index l k == L.index sc_list (k % (US.v nb_size_classes))
    );
    arena_sc_list' (i + 1) (acc `List.append` sc_list)
  )
#pop-options

/// Fuel needed to establish that the length of [] is 0
#push-options "--fuel 1"
[@@ reduce_attr]
let arena_sc_list : l:list sc_union{
  (forall (i:nat{i < L.length l}). L.index l i == L.index sc_list (i % US.v nb_size_classes))
}
= arena_sc_list' 0 []
#pop-options

#restart-solver

[@"opaque_to_smt"]
let sizes_t_pred (r: TLA.t sc_union)
  =
  TLA.length r == total_nb_sc /\
  (forall (k:US.t{US.v k < total_nb_sc}).
    TLA.get r k == L.index arena_sc_list (US.v k) /\
    TLA.get r k == L.index sc_list (US.v k % US.v nb_size_classes))

let sizes_t_pred_elim (r: sizes_t)
  =
  reveal_opaque (`%sizes_t_pred) sizes_t_pred

#push-options "--fuel 1 --ifuel 0 --z3rlimit 50"
let sizes : sizes_t =
  normalize_term_spec arena_sc_list;
  reveal_opaque (`%sizes_t_pred) sizes_t_pred;
  TLA.create #sc_union (normalize_term arena_sc_list)
#pop-options

type tuple4 = {
  x: US.t;
  y: US.t;
  z: US.t;
  w: US.t;
}

module FML = FStar.Math.Lemmas

let lemma_mult_nonzero_le
  (x y:nat)
  : Lemma
  (requires x > 0 /\ y > 0)
  (ensures
    x <= x * y)
  = ()

//#push-options "--z3cliopt smt.arith.nl=false"
#push-options "--fuel 0 --ifuel 0 --z3rlimit 50 --split_queries no"
let gen_arena_slab_region_size
  (_:unit)
  : Pure US.t
  (requires
    US.v sc_slab_region_size == US.v metadata_max * U32.v page_size /\
    US.fits (US.v sc_slab_region_size * US.v nb_size_classes * US.v nb_arenas)
  )
  (ensures fun r ->
    US.v r > 0 /\
    US.v r == US.v sc_slab_region_size * US.v nb_size_classes /\
    US.v r % U32.v page_size == 0 /\
    US.fits (US.v r * US.v nb_arenas)
  )
  =
  lemma_mult_nonzero_le
    (US.v nb_size_classes)
    (US.v nb_arenas);
  FML.lemma_mult_le_left
    (US.v sc_slab_region_size)
    (US.v nb_size_classes)
    (US.v nb_size_classes * US.v nb_arenas);
  US.fits_lte
    (US.v sc_slab_region_size * US.v nb_size_classes)
    (US.v sc_slab_region_size * US.v nb_size_classes * US.v nb_arenas);
  assert (US.fits (US.v sc_slab_region_size * US.v nb_size_classes));
  [@inline_let] let arena_slab_region_size
    = US.mul sc_slab_region_size nb_size_classes in
  MiscArith.lemma_mod_mul2 (US.v sc_slab_region_size) (U32.v page_size) (U32.v page_size);
  assert (US.v arena_slab_region_size % U32.v page_size == 0);
  arena_slab_region_size

let gen_arena_md_bm_region_size
  (_:unit)
  : Pure US.t
  (requires
    US.v sc_slab_region_size == US.v metadata_max * U32.v page_size /\
    US.fits (US.v sc_slab_region_size * US.v nb_size_classes)
  )
  (ensures fun r ->
    US.v r > 0 /\
    US.v r == US.v metadata_max * US.v 4sz * US.v nb_size_classes_sc /\
    US.fits (US.v r * US.v nb_arenas)
  )
  =
  FML.lemma_mult_le_left
    (US.v metadata_max)
    (US.v 4sz)
    (U32.v page_size);
  US.fits_lte
    (US.v metadata_max * US.v 4sz)
    (US.v metadata_max * U32.v page_size);
  let sc_md_bm_region_size = US.mul metadata_max 4sz in
  assert (US.v sc_md_bm_region_size <= US.v sc_slab_region_size);
  FML.lemma_mult_le_left
    (US.v sc_slab_region_size)
    (US.v nb_size_classes_sc)
    (US.v nb_size_classes);
  FML.lemma_mult_le_right
    (US.v nb_size_classes_sc)
    (US.v sc_md_bm_region_size)
    (US.v sc_slab_region_size);
  US.fits_lte
    (US.v sc_md_bm_region_size * US.v nb_size_classes_sc)
    (US.v sc_slab_region_size * US.v nb_size_classes);
  [@inline_let] let arena_md_bm_region_size
    = US.mul sc_md_bm_region_size nb_size_classes_sc in
  arena_md_bm_region_size

let gen_arena_md_region_size
  (_:unit)
  : Pure US.t
  (requires
    US.v sc_slab_region_size == US.v metadata_max * U32.v page_size /\
    US.fits (US.v sc_slab_region_size * US.v nb_size_classes) /\
    US.v metadata_max_ex <= US.v metadata_max
  )
  (ensures fun r ->
    US.v r > 0 /\
    US.v r == US.v metadata_max * US.v nb_size_classes_sc + US.v metadata_max_ex * US.v nb_size_classes_sc_ex /\
    US.fits (US.v metadata_max_ex * US.v nb_size_classes_sc_ex) /\
    US.fits (US.v r * US.v nb_arenas)
  )
  =
  FML.lemma_mult_le_left
    (US.v metadata_max)
    1
    (U32.v page_size);
  US.fits_lte
    (US.v metadata_max)
    (US.v metadata_max * U32.v page_size);
  FML.lemma_mult_le_right
    (US.v nb_size_classes)
    (US.v metadata_max)
    (US.v sc_slab_region_size);
  US.fits_lte
    (US.v metadata_max * US.v nb_size_classes)
    (US.v sc_slab_region_size * US.v nb_size_classes);
  FML.distributivity_add_right (US.v metadata_max) (US.v nb_size_classes_sc) (US.v nb_size_classes_sc_ex);
  US.fits_lte
    (US.v metadata_max * US.v nb_size_classes_sc)
    (US.v metadata_max * US.v nb_size_classes);
  [@inline_let] let x1 = US.mul metadata_max nb_size_classes_sc in
  FML.lemma_mult_le_right
    (US.v nb_size_classes_sc_ex)
    (US.v metadata_max_ex)
    (US.v metadata_max);
  US.fits_lte
    (US.v metadata_max_ex * US.v nb_size_classes_sc_ex)
    (US.v metadata_max * US.v nb_size_classes_sc_ex);
  [@inline_let] let x2 = US.mul metadata_max_ex nb_size_classes_sc_ex in
  US.add x1 x2

let gen_arena_md_bm_region_b_size
  (_:unit)
  : Pure US.t
  (requires
    US.v metadata_max_ex > 0 /\
    US.fits (US.v metadata_max_ex * US.v nb_size_classes_sc_ex)
  )
  (ensures fun r ->
    US.v r > 0 /\
    US.v r == US.v metadata_max_ex * US.v nb_size_classes_sc_ex /\
    US.fits (US.v r * US.v nb_arenas)
  )
  =
  US.mul metadata_max_ex nb_size_classes_sc_ex

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --split_queries no"
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
      r.x /\
    US.v r.x > 0 /\
    US.v r.y > 0 /\
    US.v r.z > 0 /\
    US.v r.w > 0 /\
    U32.v page_size > 0 /\
    US.v r.x % U32.v page_size == 0 /\
    US.fits (US.v r.x * US.v nb_arenas) /\
    US.fits (US.v r.y * US.v nb_arenas) /\
    US.fits (US.v r.z * US.v nb_arenas) /\
    US.fits (US.v r.w * US.v nb_arenas) /\
    True
  )
  =
  let x = gen_arena_slab_region_size () in
  let y = gen_arena_md_bm_region_size () in
  let w = gen_arena_md_region_size () in
  let z = gen_arena_md_bm_region_b_size () in
  hidden_pred_reveal sc_list_sc sc_list_ex
    nb_size_classes
    nb_size_classes_sc
    nb_size_classes_sc_ex
    y
    z
    w;
  hidden_pred2_reveal nb_size_classes x;
  { x; y; z; w; }

let init_aux_lemma
  (_:unit)
  : Lemma
  (
    US.fits (US.v nb_size_classes * US.v nb_arenas) /\
    US.v nb_size_classes * US.v nb_arenas > 0
  )
  =
  FML.lemma_mult_le_right
    (US.v nb_size_classes * US.v nb_arenas)
    1
    (US.v metadata_max * U32.v page_size);
  US.fits_lte
    (US.v nb_size_classes * US.v nb_arenas)
    (US.v metadata_max * U32.v page_size * US.v nb_size_classes * US.v nb_arenas)

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
let init
  (_:unit)
  : SteelTop size_classes_all false
  (fun _ -> emp)
  (fun _ r _ -> True)
  =
  let arena_sizes = gen_arena_sizes () in
  init_aux_lemma ();
  let slab_region = mmap_u8_init (US.mul arena_sizes.x nb_arenas) in
  assert (A.length slab_region == US.v full_slab_region_size);
  let md_bm_region = mmap_u64_init (US.mul arena_sizes.y nb_arenas) in
  let md_bm_region_b = mmap_bool_init (US.mul arena_sizes.z nb_arenas) in
  let md_region = mmap_cell_status_init (US.mul arena_sizes.w nb_arenas) in
  let size_classes = mmap_sc_init (US.mul nb_size_classes nb_arenas) in
  init_all_arenas
    sc_list_sc sc_list_ex
    nb_size_classes_sc nb_size_classes_sc_ex
    nb_size_classes
    arena_sizes.x
    arena_sizes.w
    arena_sizes.y
    arena_sizes.z
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

#push-options "--warn_error '-272'"
let sc_all : size_classes_all = init ()
#pop-options

open WithLock

val allocate_size_class
  (idx: G.erased (US.t){US.v (G.reveal idx) < A.length sc_all.size_classes})
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r -> null_or_varray r `star` size_class_vprop scs)
  (requires fun h0 ->
    scs == (Seq.index (G.reveal sc_all.g_size_classes) (US.v (G.reveal idx))).data
  )
  (ensures fun h0 r h1 ->
    let scs' = (Seq.index (G.reveal sc_all.g_size_classes) (US.v (G.reveal idx))).data in
    let size = get_u32 scs'.size in
    scs' == scs /\
    not (is_null r) ==> (
      A.length r == U32.v size /\
      array_u8_alignment r 16ul /\
      ((U32.v size > 0 /\ (U32.v page_size) % (U32.v size) == 0) ==> array_u8_alignment r size)
    )
  )

let allocate_size_class _ scs =
  Main.allocate_size_class scs

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let slab_malloc_one (i:US.t{US.v i < total_nb_sc}) (bytes: U32.t)
  =
  let ptr = with_lock_roarray
    size_class_struct
    unit
    (array U8.t)
    size_class
    sc_all.size_classes
    (G.reveal sc_all.g_size_classes)
    sc_all.ro_perm
    (fun v0 -> size_class_vprop v0)
    (fun s -> s.data)
    (fun s -> s.lock)
    (fun v1 -> emp)
    (fun v1 r -> null_or_varray r)
    i
    ()
    (fun _ _ r x1 ->
      let size = get_u32 ((Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size) in
      U32.v size > 0 /\
      not (is_null r) ==> (
        A.length r == U32.v size /\
        A.length r >= U32.v bytes /\
        array_u8_alignment r 16ul /\
        ((U32.v page_size) % (U32.v size) == 0 ==> array_u8_alignment r size)
      )
    )
    (fun sc_data -> allocate_size_class (G.hide i) sc_data)
  in
  return ptr
#pop-options

#push-options "--fuel 1 --ifuel 1"
let cons_implies_positive_length (#a: Type) (l: list a)
  : Lemma
  (requires Cons? l)
  (ensures List.length l > 0)
  = ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
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
      array_u8_alignment r 16ul /\
      Seq.length s >= 2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      aux_lemma l i arena_id;
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = get_u32 (TLA.get sizes idx) in
      synced_sizes_reveal 0sz sc_all.g_size_classes sizes total_nb_sc;
      if bytes `U32.lte` size then
        slab_malloc_one idx bytes
      else
        slab_malloc_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

#restart-solver

#push-options "--fuel 1 --ifuel 1"
let set_canary ptr size
  =
  let size = get_u32 size in
  assert (UInt.size (U32.v size - 2) U32.n);
  assert (UInt.size (U32.v size - 1) U32.n);
  if is_null ptr
  then return ()
  else (
    elim_live_null_or_varray ptr;
    upd ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) slab_canaries_magic1;
    upd ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) slab_canaries_magic2;
    intro_live_null_or_varray ptr
  )
#pop-options

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
      array_u8_alignment r 16ul /\
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
      let size = TLA.get sizes idx in
      let size' = get_u32 size in
      synced_sizes_reveal 0sz sc_all.g_size_classes sizes total_nb_sc;
      if bytes `U32.lte` (size' `U32.sub` 2ul) then
        let ptr = slab_malloc_one idx bytes in
        set_canary ptr size;
        return ptr
      else
        slab_malloc_canary_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

open MiscArith

#restart-solver

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
      array_u8_alignment r 16ul /\
      array_u8_alignment r alignment /\
      Seq.length s >= 2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      aux_lemma l i arena_id;
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = TLA.get sizes idx in
      let size' = get_u32 size in
      synced_sizes_reveal 0sz sc_all.g_size_classes sizes total_nb_sc;
      let b = U32.eq (U32.rem 131072ul size') 0ul in
      if b && bytes `U32.lte` size' && alignment `U32.lte` size' then (
        let r = slab_malloc_one idx bytes in
        let size_ = G.hide (get_u32 (Seq.index sc_all.g_size_classes (US.v idx)).data.size) in
        assert (G.reveal size_ = size');
        assume ((U32.v page_size) % (U32.v (G.reveal size_ )) = 0);
        assert_norm (U32.v page_size = pow2 12);
        alignment_lemma (U32.v page_size) 12 (U32.v alignment) (U32.v size');
        assert (U32.v size' % U32.v alignment = 0);
        array_u8_alignment_lemma2 r size' alignment;
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
      array_u8_alignment r 16ul /\
      array_u8_alignment r alignment /\
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
      let size = TLA.get sizes idx in
      let size' = get_u32 size in
      synced_sizes_reveal 0sz sc_all.g_size_classes sizes total_nb_sc;
      let b = U32.eq (U32.rem 131072ul size') 0ul in
      if b && bytes `U32.lte` (size' `U32.sub` 2ul) && alignment `U32.lte` size' then (
        let ptr = slab_malloc_one idx bytes in
        let size_ = G.hide (get_u32 (Seq.index sc_all.g_size_classes (US.v idx)).data.size) in
        assert (G.reveal size_ = size');
        assume ((U32.v page_size) % (U32.v (G.reveal size_ )) = 0);
        assert_norm (U32.v page_size = pow2 12);
        alignment_lemma (U32.v page_size) 12 (U32.v alignment) (U32.v size');
        assert (U32.v size' % U32.v alignment = 0);
        array_u8_alignment_lemma2 ptr size' alignment;
        set_canary ptr size;
        return ptr
      ) else (
        slab_aligned_alloc_canary_i tl (i `US.add` 1sz) arena_id alignment bytes
      )
#pop-options

/// Generic implementations: sizeclass selection = nested ifs

#restart-solver

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let slab_malloc_generic_nocanary arena_id bytes
  =
  (slab_malloc_i sc_list 0sz) arena_id bytes

let slab_malloc_generic_canary arena_id bytes
  =
  (slab_malloc_canary_i sc_list 0sz) arena_id bytes

let slab_aligned_alloc_generic_nocanary arena_id alignment bytes
  =
  (slab_aligned_alloc_i sc_list 0sz) arena_id alignment bytes

let slab_aligned_alloc_generic_canary arena_id alignment bytes
  =
  (slab_aligned_alloc_canary_i sc_list 0sz) arena_id alignment bytes
#pop-options
