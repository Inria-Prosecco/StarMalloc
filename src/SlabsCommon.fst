module SlabsCommon

let t (size_class: sc) : Type0 =
  dtuple2
    (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
   (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
  & Seq.lseq U8.t (U32.v page_size - US.v (rounding size_class))

#push-options "--fuel 0 --ifuel 0"
let empty_md_is_properly_zeroed
  (size_class: sc)
  : Lemma
  (slab_vprop_aux2 size_class (Seq.create 4 0UL))
  =
  let zero_to_vec_lemma2 (i:nat{i < 64})
    : Lemma
    (FU.nth (FU.zero 64) i = false)
    =
    FU.zero_to_vec_lemma #64 i in
  let s0 = Seq.create 4 0UL in
  let bm = Bitmap4.array_to_bv2 #4 s0 in
  let bound2 = bound2_gen (nb_slots size_class) (G.hide size_class) in
  assert (U64.v (Seq.index s0 0) == FU.zero 64);
  array_to_bv_slice #4 s0 0;
  Classical.forall_intro (zero_to_vec_lemma2);
  Seq.lemma_eq_intro (Seq.slice bm 0 64) (Seq.create 64 false);
  zf_b_slice (Seq.slice bm 0 64) 0 (64 - U32.v bound2)
#pop-options

let empty_t size_class =
  empty_md_is_properly_zeroed size_class;
  ((| Seq.create 4 0UL, Seq.create (U32.v (nb_slots size_class)) (Ghost.hide None) |), Seq.create (U32.v page_size - US.v (rounding size_class)) U8.zero)

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 50"
let p_empty_unpack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  ((p_empty sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    b1 == b2 /\
    is_empty sc v1 /\
    h0 ((p_empty sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )
  =
  change_slprop_rel
    ((p_empty sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_empty sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|),_) -> is_empty sc s == true)

let p_partial_unpack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  ((p_partial sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    b1 == b2 /\
    is_partial sc v1 /\
    h0 ((p_partial sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )
  =
  change_slprop_rel
    ((p_partial sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_partial sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|),_) -> is_partial sc s == true)

let p_full_unpack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  ((p_full sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    b1 == b2 /\
    is_full sc v1 /\
    h0 ((p_full sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )
  =
  change_slprop_rel
    ((p_full sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_full sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|),_) -> is_full sc s == true)

let p_empty_pack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_empty sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    is_empty sc v0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_empty sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|),_) -> is_empty sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_empty sc s == true))
    ((p_empty sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_partial_pack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_partial sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    is_partial sc v0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_partial sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|),_) -> is_partial sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_partial sc s == true))
    ((p_partial sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_full_pack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_full sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    is_full sc v0 /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_full sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|),_) -> is_full sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_full sc s == true))
    ((p_full sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_guard_pack (#opened:_) size_class b =
  intro_vrewrite (guard_slab (snd b) `star` A.varray (fst b)) (fun _ -> empty_t size_class)

let p_quarantine_pack (#opened:_) size_class b =
  intro_vrewrite (quarantine_slab (snd b) `star` A.varray (fst b)) (fun _ -> empty_t size_class)
#pop-options

inline_for_extraction noextract
let slab_array
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : Pure (array U8.t)
  (requires
    A.length slab_region = US.v metadata_max * U32.v page_size /\
    US.v md_count < US.v metadata_max)
  (ensures fun r ->
    A.length r = U32.v page_size /\
    same_base_array r slab_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of slab_region) + US.v md_count * U32.v page_size
  )
  =
  let ptr = A.ptr_of slab_region in
  let page_size_t = u32_to_sz page_size in
  let shift_size_t = US.mul md_count page_size_t in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide (U32.v page_size)|)

let pack_slab_array (#opened:_)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) (u32_to_sz page_size)))
    (fun _ -> A.varray (slab_array slab_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) (u32_to_sz page_size)) h0 ==
      A.asel (slab_array slab_region md_count) h1)
  = change_equal_slprop
    (A.varray (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz page_size))) (u32_to_sz page_size)))
    (A.varray (slab_array slab_region md_count))

inline_for_extraction noextract
let md_bm_array
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : Pure (array U64.t)
  (requires
    A.length md_bm_region = US.v metadata_max * 4 /\
    US.v md_count < US.v metadata_max)
  (ensures fun r ->
    A.length r = 4 /\
    same_base_array r md_bm_region
  )
  =
  let ptr = A.ptr_of md_bm_region in
  let shift_size_t = US.mul md_count 4sz in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide 4|)

let pack_md_bm_array (#opened:_)
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz))
    (fun _ -> A.varray (md_bm_array md_bm_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz) h0 ==
      A.asel (md_bm_array md_bm_region md_count) h1)
  = change_equal_slprop
    (A.varray (A.split_l (A.split_r md_bm_region (US.mul md_count 4sz)) 4sz))
    (A.varray (md_bm_array md_bm_region md_count))

inline_for_extraction noextract
let md_array
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : Pure (array AL.cell)
  (requires
    A.length md_region = US.v metadata_max /\
    US.v md_count < US.v metadata_max)
  (ensures fun r ->
    A.length r = 1 /\
    same_base_array r md_region /\
    True
  )
  =
  let ptr = A.ptr_of md_region in
  let ptr_shifted = A.ptr_shift ptr md_count in
  (|ptr_shifted, G.hide 1|)

let pack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_region md_count) 1sz))
    (fun _ -> A.varray (md_array md_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region md_count) 1sz) h0 ==
      A.asel (md_array md_region md_count) h1)
  = change_equal_slprop
      (A.varray (A.split_l (A.split_r md_region md_count) 1sz))
      (A.varray (md_array md_region md_count))

let unpack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: US.t{US.v md_count < US.v metadata_max})
  : SteelGhost unit opened
    (A.varray (md_array md_region md_count))
    (fun _ -> A.varray (A.split_l (A.split_r md_region md_count) 1sz))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region md_count) 1sz) h1 ==
      A.asel (md_array md_region md_count) h0)
  = change_equal_slprop
      (A.varray (md_array md_region md_count))
      (A.varray (A.split_l (A.split_r md_region md_count) 1sz))

let f_lemma
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: Seq.lseq AL.status (US.v md_count_v))
  (i: US.t{US.v i < US.v md_count_v})
  : Lemma
  (t_of (f size_class slab_region md_bm_region md_count_v md_region_lv i)
  == t size_class)
  =
  slab_vprop_lemma size_class
    (slab_array slab_region i)
    (md_bm_array md_bm_region i)

#restart-solver

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let pack_3
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5: US.t)
  : SteelGhost unit opened
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    vptr r5 `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    sel r5 h0 == idx5 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob1)
  =
  intro_vrefine
    (ind_varraylist_aux2
      (A.split_l md_region md_count_v)
      ((((idx1, idx2), idx3), idx4), idx5))
    (ind_varraylist_aux_refinement
      (A.split_l md_region md_count_v)
      ((((idx1, idx2), idx3), idx4), idx5));
  intro_vdep
    (vptr r1 `star` vptr r2 `star` vptr r3 `star` vptr r4 `star` vptr r5)
    (ind_varraylist_aux
      (A.split_l md_region md_count_v)
      ((((idx1, idx2), idx3), idx4), idx5))
    (ind_varraylist_aux
      (A.split_l md_region md_count_v));

  change_equal_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_us_refined (US.v md_count_v)))
    (left_vprop2 size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv));

  intro_vdep
    (left_vprop1 md_region r1 r2 r3 r4 r5 md_count_v)
    (left_vprop2 size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
    (left_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 md_count_v);

  intro_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 md_count_v)
#pop-options

let lemma_slab_aux_starseq
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx:nat{idx < US.v md_count_v})
  (v:AL.status)
  : Lemma
  (let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
   let f2 = f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
   let s = SeqUtils.init_us_refined (US.v md_count_v) in
   forall (k:nat{k <> idx /\ k < Seq.length s}).
     f1 (Seq.index s k) == f2 (Seq.index s k))
  =
  let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
  let f2 = f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
  let md_region_lv' = Seq.upd (G.reveal md_region_lv) idx v in
  let s = SeqUtils.init_us_refined (US.v md_count_v) in
  let aux (k:nat{k <> idx /\ k < Seq.length s})
    : Lemma (f1 (Seq.index s k) == f2 (Seq.index s k))
    = let i = Seq.index s k in
      SeqUtils.init_us_refined_index (US.v md_count_v) k;
      assert (Seq.index md_region_lv (US.v i) == Seq.index md_region_lv' (US.v i))
  in Classical.forall_intro aux

#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
let pack_slab_starseq
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  //(r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx: US.t{US.v idx < US.v md_count_v})
  (v: AL.status)
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx) `star`
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx))
    = h0 (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx)) in
    let md : Seq.lseq U64.t 4 = dfst (fst md_blob) in
    v <> 4ul /\ v <> 3ul /\
    (v == 2ul ==> is_full size_class md) /\
    (v == 1ul ==> is_partial size_class md) /\
    (v == 0ul ==> is_empty size_class md) /\
    idx <> AL.null_ptr
  )
  (ensures fun h0 _ h1 -> True)
  =
  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx);
  if (U32.eq v 2ul) then (
    p_full_pack size_class
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx)
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx);
    change_equal_slprop
      (p_full size_class (md_bm_array md_bm_region idx, slab_array slab_region idx))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)))
  ) else if (U32.eq v 1ul) then (
    p_partial_pack size_class
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx)
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx);
    change_equal_slprop
      (p_partial size_class (md_bm_array md_bm_region idx, slab_array slab_region idx))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)))
  ) else (
    p_empty_pack size_class
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx)
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx);
    change_equal_slprop
      (p_empty size_class (md_bm_array md_bm_region idx, slab_array slab_region idx))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)))
  );
  lemma_slab_aux_starseq size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv (US.v idx) v;
  starseq_upd_pack
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx)
#pop-options

#push-options "--z3rlimit 40"
let upd_and_pack_slab_starseq_quarantine size_class
  slab_region
  md_bm_region
  md_region
  md_count
  md_count_v
  md_region_lv
  idx
  =
  let md_as_seq = elim_slab_vprop size_class
    (md_bm_array md_bm_region idx) (slab_array slab_region idx) in
  Helpers.intro_empty_slab_varray size_class md_as_seq (slab_array slab_region idx);
  mmap_trap_quarantine
          (slab_array slab_region idx)
          (u32_to_sz page_size);

  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx);
  p_quarantine_pack size_class (md_bm_array md_bm_region idx, slab_array slab_region idx);
  change_equal_slprop
    (p_quarantine size_class (md_bm_array md_bm_region idx, slab_array slab_region idx))
    (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) 4ul)
      (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)));
  lemma_slab_aux_starseq size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv (US.v idx) 4ul;
  starseq_upd_pack
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) 4ul))
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) 4ul))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx)
#pop-options

#push-options "--z3rlimit 20 --compat_pre_typed_indexed_effects"
let pack_right_and_refactor_vrefine_dep
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count: ref US.t)
  (r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max})
  : SteelGhost unit opened
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    `star`
    right_vprop slab_region md_bm_region md_region md_count_v
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
  )
  (requires fun h0 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    md_count_v == dfst blob0)
  (ensures fun h0 _ h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    ) in
    dfst blob0 == dfst blob1
  )
  =
  let md_count_v' = elim_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5) in
  assert (G.reveal md_count_v' == md_count_v);
  change_equal_slprop
    (right_vprop slab_region md_bm_region md_region md_count_v)
    (right_vprop slab_region md_bm_region md_region (G.reveal md_count_v'));

  intro_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5)
    (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 r5 (G.reveal md_count_v') `star`
    right_vprop slab_region md_bm_region md_region (G.reveal md_count_v'))
#pop-options
