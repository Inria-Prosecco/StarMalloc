module Main.Meta

friend Config

/// An attribute, that will indicate that the annotated functions should be unfolded at compile-time
irreducible let reduce_attr : unit = ()

[@@ reduce_attr]
inline_for_extraction noextract
let sc_list: l:list sc{US.v nb_size_classes == List.length sc_list}
= normalize_term sc_list

//let temp_thm (sc: sc)
//  : Lemma
//  (requires True)
//  (ensures U32.v sc > 0)
//  = ()
//let t = sc * bool
//[@@ reduce_attr]
//inline_for_extraction noextract
//let sc_list_aligned: l:(list t){List.length l == List.length sc_list}
//= admit ();
//  normalize_term (List.map
//  (fun s -> temp_thm s; (s, (U32.v page_size) % (U32.v s) = 0))
//  sc_list
//)
//let nb_size_classes_aligned: v:US.t{US.v v ==  List.length sc_list_aligned}
//  =
//  assume (List.length sc_list_aligned < U32.n);
//  [@inline_let] let l = normalize_term (List.length sc_list_aligned) in
//  normalize_term_spec (List.length sc_list_aligned);
//  assert (l == List.length sc_list_aligned);
//  [@inline_let] let l_as_u32 = normalize_term (U32.uint_to_t l) in
//  normalize_term_spec (U32.uint_to_t l);
//  assert (U32.v l_as_u32 == List.length sc_list_aligned);
//  US.fits_u64_implies_fits_32 ();
//  US.of_u32 l_as_u32

/// Number of arenas as a nat, for specification purposes. Not relying on US.v
/// allows better normalization for extraction
[@@ reduce_attr]
inline_for_extraction noextract
let nb_arenas_nat : n:nat{n == US.v nb_arenas}
= normalize_term (US.v nb_arenas)

open FStar.Mul
let total_nb_sc : n:nat{
  n == US.v nb_size_classes * US.v nb_arenas /\
  n == US.v nb_size_classes * nb_arenas_nat
}
=
normalize_term (US.v nb_size_classes * US.v nb_arenas)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// Duplicating the list of size_classes sizes for each arena, which enables a simpler
/// initialization directly using the mechanism in place for one arena
[@@ reduce_attr]
inline_for_extraction noextract
let rec arena_sc_list'
  (i:nat{i <= US.v nb_arenas})
  (acc:list sc{List.length acc = i * US.v nb_size_classes})
  : Tot (l:list sc{List.length l == total_nb_sc})
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
    arena_sc_list' (i + 1) (acc `List.append` sc_list)
  )


/// Fuel needed to establish that the length of [] is 0
#push-options "--fuel 1"
[@@ reduce_attr]
inline_for_extraction noextract
let arena_sc_list : (l:list sc{List.length l == total_nb_sc /\ Cons? l}) = arena_sc_list' 0 []
#pop-options

let sizes_t = r:TLA.t sc{
  TLA.length r == total_nb_sc /\
  (forall (k:U32.t{U32.v k < total_nb_sc}).
    TLA.get r k == List.Tot.index arena_sc_list (U32.v k))
}

let init_sizes (_:unit)
  : SteelTop (sizes_t) false
  (fun _ -> emp)
  (fun _ r _ ->
    TLA.length r == total_nb_sc /\
    (forall (k:U32.t{U32.v k < total_nb_sc}).
      TLA.get r k == List.Tot.index arena_sc_list (U32.v k))
  )
  =
  let v = TLA.create #sc arena_sc_list in
  return v

let sizes : sizes_t = init_sizes ()

#push-options "--fuel 0 --ifuel 0"

/// Performs the initialization of one size class of length [size_c], and stores it in the
/// size_classes array at index [k]
val init_size_class
  (size_c: sc)
  (n: US.t{
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (k: US.t{US.v k < US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k'
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n /\
    A.length md_region >= US.v metadata_max * US.v k /\
    A.length md_region >= US.v metadata_max * US.v k'
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k')) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) page_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    //synced_sizes (US.v k) (asel sizes h0) (asel size_classes h0) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) page_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) h1) /\
    //synced_sizes (US.v k') (asel sizes h1) (asel size_classes h1) /\
    (forall (i:nat{i <= US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

let init_size_class size n k k' slab_region md_bm_region md_region size_classes =
  (**) let g0 = gget (varray size_classes) in
  //(**) let g_sizes0 = gget (varray sizes) in
  f_lemma n k;
  //upd sizes k size;
  let sc = init_wrapper2 size n k k' slab_region md_bm_region md_region in
  upd size_classes k sc;

  (**) let g1 = gget (varray size_classes) in
  //(**) let g_sizes1 = gget (varray sizes) in
  //(**) assert (Ghost.reveal g_sizes1 == Seq.upd (Ghost.reveal g_sizes0) (US.v k) size);
  (**) assert (Ghost.reveal g1 == Seq.upd (Ghost.reveal g0) (US.v k) sc)


#restart-solver

/// Wrapper around `init_size_class`. It takes as argument a list [l] of sizes
/// for size classes to be created, creates them, and stores them in order in
/// the [size_classes] array. Note, this function should not be extracted as is,
/// it will be reduced at compile-time to yield an idiomatic sequence of calls
/// to `init_size_class`
[@@ reduce_attr]
noextract
val init_size_classes_aux (l:list sc)
  (n: US.t{
    US.fits (US.v n) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (k: US.t{US.v k < US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k'
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n /\
    A.length md_region >= US.v metadata_max * US.v k /\
    A.length md_region >= US.v metadata_max * US.v k'
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max n)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    US.v k + List.length l == US.v n /\
    Cons? l /\

    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) page_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    //synced_sizes (US.v k) (asel sizes h0) (asel size_classes h0) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) page_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    //synced_sizes (US.v n) (asel sizes h1) (asel size_classes h1) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

#restart-solver

open MiscArith

#restart-solver

// We need to bump the fuel to reason about the length of the lists
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1 --query_stats"
let rec init_size_classes_aux l n k k' slab_region md_bm_region md_region size_classes
  = match l with
  | [hd] ->
      assert (US.v k' == US.v n);
      init_size_class hd n k k' slab_region md_bm_region md_region size_classes;
      // Need to rewrite the k' into n to satisfy the postcondition
      change_equal_slprop (A.varray (split_r md_bm_region _)) (A.varray (split_r md_bm_region _));
      change_equal_slprop (A.varray (split_r md_region _)) (A.varray (split_r md_region _));
      change_equal_slprop (A.varray (split_r slab_region _)) (A.varray (split_r slab_region _))
  | hd::tl ->
      init_size_class hd n k k' slab_region md_bm_region md_region size_classes;
      // This proof obligation in the recursive call seems especially problematic.
      // The call to the lemma alleviates the issue, we might need something similar for
      // the md_region and md_bm_region in the future
      assert (US.v (k' `US.add` 1sz) <= US.v n);
      lemma_mul_le (US.v metadata_max) (US.v (u32_to_sz page_size)) (US.v (k' `US.add` 1sz)) (US.v n);
      lemma_mul_le (US.v metadata_max) (US.v 4sz) (US.v (k' `US.add` 1sz)) (US.v n);
      Math.Lemmas.lemma_mult_le_left (US.v metadata_max) (US.v (k' `US.add` 1sz)) (US.v n);

      init_size_classes_aux tl n k' (k' `US.add` 1sz) slab_region md_bm_region md_region size_classes
#pop-options

#restart-solver

#push-options "--fuel 0 --ifuel 0"
/// Entrypoint, allocating all size classes according to the list of sizes [l]
inline_for_extraction noextract
val init_size_classes (l:list sc)
  (n: US.t{
    US.fits (US.v n) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * 0 /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * 1
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * 0 /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * 1
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n /\
    A.length md_region >= US.v metadata_max * 0 /\
    A.length md_region >= US.v metadata_max * 1
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max 0sz)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max n)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) page_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) h0) /\
    //synced_sizes 0 (asel sizes h0) (asel size_classes h0) /\
    (forall (i:nat{i < 0}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) page_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    //synced_sizes (US.v n) (asel sizes h1) (asel size_classes h1) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

/// The normalization steps for reduction at compile-time
unfold
let normal_steps = [
      delta_attr [`%reduce_attr];
      delta_only [`%List.append];
      iota; zeta; primops]

unfold
let normal (#a:Type) (x:a) =
  Pervasives.norm normal_steps x

let init_size_classes l n slab_region md_bm_region md_region size_classes =
  (normal (init_size_classes_aux l n 0sz 1sz)) slab_region md_bm_region md_region size_classes



#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
let init
  (_:unit)
  : SteelTop size_classes_all false
  (fun _ -> emp)
  (fun _ r _ -> True)
  =
  metadata_max_up_fits ();
  US.fits_lte
    (US.v nb_size_classes * US.v nb_arenas)
    ((US.v metadata_max * U32.v page_size) * US.v nb_size_classes * US.v nb_arenas);
  [@inline_let]
  let n = nb_size_classes `US.mul` nb_arenas in
  assert (
    US.v n > 0 /\ US.v n >= US.v 1sz /\
    US.v n == total_nb_sc /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size)) /\
    US.fits (US.v metadata_max * US.v 4sz) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n) /\
    True
  );
  let slab_region = mmap_u8_init (US.mul (US.mul metadata_max (u32_to_sz page_size)) n) in
  let md_bm_region = mmap_u64_init (US.mul (US.mul metadata_max 4sz) n) in
  let md_region = mmap_cell_status_init (US.mul metadata_max n) in

  Math.Lemmas.mul_zero_right_is_zero (US.v (US.mul metadata_max (u32_to_sz page_size)));
  Math.Lemmas.mul_zero_right_is_zero (US.v (US.mul metadata_max 4sz));
  Math.Lemmas.mul_zero_right_is_zero (US.v metadata_max);
  A.ptr_shift_zero (A.ptr_of slab_region);
  A.ptr_shift_zero (A.ptr_of md_bm_region);
  A.ptr_shift_zero (A.ptr_of md_region);

  change_equal_slprop
    (A.varray slab_region)
    (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)));
  change_equal_slprop
    (A.varray md_bm_region)
    (A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)));
  change_equal_slprop
    (A.varray md_region)
    (A.varray (A.split_r md_region (US.mul metadata_max 0sz)));

  assert (A.length (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n);
  assert (A.length (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) == US.v metadata_max * 4 * US.v n);
  assert (A.length (A.split_r md_region (US.mul metadata_max 0sz)) == US.v metadata_max * US.v n);

  let size_classes = mmap_sc_init n in
  //let sizes = mmap_sizes_init n in

  init_size_classes arena_sc_list n slab_region md_bm_region md_region size_classes;

  let g_size_classes = gget (varray size_classes) in
  //let g_sizes = gget (varray sizes) in

  let ro_perm = create_ro_array size_classes g_size_classes in
  //let ro_sizes = create_ro_array sizes g_sizes in

  drop (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size))
    n)));
  drop (A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz)
    n)));
  drop (A.varray (A.split_r md_region (US.mul metadata_max
   n)));

  [@inline_let]
  let s : size_classes_all = {
    size_classes;
    sizes;
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

open NullOrVarray

inline_for_extraction noextract
let return_null ()
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> is_null r)
  =
  intro_null_null_or_varray #U8.t

/// Wrapper around allocate_size_class, that does not return a pair, and instead
/// always returns a valid permission on the new pointer if it is not null
inline_for_extraction noextract
val allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r -> null_or_varray r `star` size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    not (is_null r) ==> (
      A.length r == U32.v scs.size /\
      array_u8_alignment r 16ul /\
      ((U32.v scs.size > 0 /\ (U32.v page_size) % (U32.v scs.size) == 0) ==> array_u8_alignment r scs.size)
    )
  )

let allocate_size_class scs =
  let r = SizeClass.allocate_size_class scs in
  intro_vrewrite
    (if A.is_null r then emp else A.varray r)
    (null_or_varray_f r);
  return r

#restart-solver

#push-options "--fuel 0 --ifuel 0 --query_stats"
inline_for_extraction noextract
let slab_malloc_one (i:US.t{US.v i < total_nb_sc}) (bytes: U32.t)
  : Steel
  (array U8.t)
  emp (fun r -> null_or_varray r)
  (requires fun _ ->
    U32.v bytes <= U32.v (Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size
  )
  (ensures fun _ r _ ->
    let size = (Seq.index sc_all.g_size_classes (US.v i)).data.size in
    not (is_null r) ==> (
      A.length r == U32.v (Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size /\
      A.length r >= U32.v bytes /\
      array_u8_alignment r 16ul /\
      ((U32.v page_size) % (U32.v size) == 0 ==> array_u8_alignment r size)
    )
  )
  =
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

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// A wrapper around slab_malloc' that performs dispatch in the size classes
/// for arena [arena_id] in a generic way.
/// The list argument is not actually used, it just serves
/// as a counter that reduces better than nats
[@@ reduce_attr]
noextract
let rec slab_malloc_i
  (l:list sc{List.length l <= length sc_all.size_classes})
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
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = TLA.get sc_all.sizes idx in
      if bytes `U32.lte` size then
        slab_malloc_one idx bytes
      else
        slab_malloc_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// A variant of slab_malloc_i adding slab canaries
[@@ reduce_attr]
noextract
let rec slab_malloc_canary_i
  (l:list sc{List.length l <= length sc_all.size_classes})
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
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = index sc_all.ro_sizes idx in
      if bytes `U32.lte` (size `U32.sub` 2ul) then
        let ptr = slab_malloc_one idx bytes in
        if is_null ptr then return ptr
        else (
          elim_live_null_or_varray ptr;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) slab_canaries_magic1;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) slab_canaries_magic2;
          intro_live_null_or_varray ptr;
          return ptr
        )
      else
        slab_malloc_canary_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_malloc arena_id bytes =
  if enable_slab_canaries_malloc then
    (slab_malloc_canary_i sc_list 0sz) arena_id bytes
  else
    (slab_malloc_i sc_list 0sz) arena_id bytes
#pop-options

open MiscArith

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// `slab_aligned_alloc` works in a very similar way as `slab_malloc_i`
/// The key difference lies in the condition of the if-branch: we only
/// attempt to allocate in this size class if it satisfies the alignment
/// constraint, i.e., alignment % size == 0
[@@ reduce_attr]
noextract
let rec slab_aligned_alloc_i
  (l:list sc{List.length l <= length sc_all.size_classes})
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
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = index sc_all.ro_sizes idx in
      let b = U32.eq (U32.rem page_size size) 0ul in
      if b && bytes `U32.lte` size && alignment `U32.lte` size then (
        let r = slab_malloc_one idx bytes in
        let size_ = G.hide (Seq.index sc_all.g_size_classes (US.v idx)).data.size in
        assert (G.reveal size_ = size);
        assert ((U32.v page_size) % (U32.v (G.reveal size_ )) = 0);
        assert_norm (U32.v page_size = pow2 12);
        alignment_lemma (U32.v page_size) 12 (U32.v alignment) (U32.v size);
        assert (U32.v size % U32.v alignment = 0);
        array_u8_alignment_lemma2 r size alignment;
        return r
      ) else (
        slab_aligned_alloc_i tl (i `US.add` 1sz) arena_id alignment bytes
      )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// Version of `slab_aligned_alloc_i` with slab canaries
[@@ reduce_attr]
noextract
let rec slab_aligned_alloc_canary_i
  (l:list sc{List.length l <= length sc_all.size_classes})
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
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = index sc_all.ro_sizes idx in
      let b = U32.eq (U32.rem page_size size) 0ul in
      if b && bytes `U32.lte` (size `U32.sub` 2ul) && alignment `U32.lte` size then
        let ptr = slab_malloc_one idx bytes in
        let size_ = G.hide (Seq.index sc_all.g_size_classes (US.v idx)).data.size in
        assert (G.reveal size_ = size);
        assert ((U32.v page_size) % (U32.v (G.reveal size_ )) = 0);
        assert_norm (U32.v page_size = pow2 12);
        alignment_lemma (U32.v page_size) 12 (U32.v alignment) (U32.v size);
        assert (U32.v size % U32.v alignment = 0);
        array_u8_alignment_lemma2 ptr size alignment;
        if is_null ptr then return ptr
        else (
          elim_live_null_or_varray ptr;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) slab_canaries_magic1;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) slab_canaries_magic2;
          intro_live_null_or_varray ptr;
          return ptr
        )
      else
        slab_aligned_alloc_canary_i tl (i `US.add` 1sz) arena_id alignment bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_aligned_alloc arena_id alignment bytes =
  if enable_slab_canaries_malloc then
    (slab_aligned_alloc_canary_i sc_list 0sz) arena_id alignment bytes
  else
    (slab_aligned_alloc_i sc_list 0sz) arena_id alignment bytes
#pop-options

#restart-solver

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
