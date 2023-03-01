module SlabsCommon

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
    (fun ((|s,_|), _) -> is_empty sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|), _) -> is_empty sc s == true)

let p_partial_unpack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
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
    (fun ((|s,_|), _) -> is_partial sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|), _) -> is_partial sc s == true)

let p_full_unpack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
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
    (fun ((|s,_|), _) -> is_full sc s == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|), _) -> is_full sc s == true)

let p_guard_unpack (#opened:_)
  (sc: sc)
  (b1 b2: blob)
  : SteelGhost unit opened
  ((p_guard sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
    b1 == b2 /\
    is_guard sc (snd b1) /\
    h0 ((p_guard sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )
  =
  sladmit ();
  change_slprop_rel
    ((p_guard sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_guard sc (snd b1)))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|), _) -> is_guard sc (snd b1))

let p_empty_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
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
    (fun ((|s,_|), _) -> is_empty sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_empty sc s == true))
    ((p_empty sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_partial_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
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
    (fun ((|s,_|), _) -> is_partial sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_partial sc s == true))
    ((p_partial sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_full_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
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
    (fun ((|s,_|), _) -> is_full sc s == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_full sc s == true))
    ((p_full sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_guard_pack (#opened:_)
  (sc: sc)
  (b1: blob)
  (b2: blob)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_guard sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
    is_guard sc (snd b1) /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_guard sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|), _) -> is_guard sc (snd b1));
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_guard sc (snd b1)))
    ((p_guard sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())
#pop-options


inline_for_extraction noextract
let slab_array
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array U8.t)
  (requires
    A.length slab_region = U32.v metadata_max * U32.v page_size /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = U32.v page_size /\
    same_base_array r slab_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of slab_region) + U32.v md_count * U32.v page_size
  )
  =
  let ptr = A.ptr_of slab_region in
  let shift = U32.mul md_count page_size in
  let shift_size_t = u32_to_sz shift in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide (U32.v page_size)|)

let pack_slab_array (#opened:_)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (fun _ -> A.varray (slab_array slab_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)) h0 ==
      A.asel (slab_array slab_region md_count) h1)
  = change_equal_slprop
    (A.varray (A.split_l (A.split_r slab_region (u32_to_sz (U32.mul md_count page_size))) (u32_to_sz page_size)))
    (A.varray (slab_array slab_region md_count))

inline_for_extraction noextract
let md_bm_array
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array U64.t)
  (requires
    A.length md_bm_region = U32.v metadata_max * 4 /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = 4 /\
    same_base_array r md_bm_region
  )
  =
  let ptr = A.ptr_of md_bm_region in
  let shift = U32.mul md_count 4ul in
  let shift_size_t = u32_to_sz shift in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide 4|)

let pack_md_bm_array (#opened:_)
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (fun _ -> A.varray (md_bm_array md_bm_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)) h0 ==
      A.asel (md_bm_array md_bm_region md_count) h1)
  = change_equal_slprop
    (A.varray (A.split_l (A.split_r md_bm_region (u32_to_sz (U32.mul md_count 4ul))) (u32_to_sz 4ul)))
    (A.varray (md_bm_array md_bm_region md_count))

inline_for_extraction noextract
let md_array
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : Pure (array AL.cell)
  (requires
    A.length md_region = U32.v metadata_max /\
    U32.v md_count < U32.v metadata_max)
  (ensures fun r ->
    A.length r = 1 /\
    same_base_array r md_region /\
    True
  )
  =
  let ptr = A.ptr_of md_region in
  let shift_size_t = u32_to_sz md_count in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide 1|)

let pack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul)))
    (fun _ -> A.varray (md_array md_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul)) h0 ==
      A.asel (md_array md_region md_count) h1)
  = change_equal_slprop
      (A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) (u32_to_sz 1ul)))
      (A.varray (md_array md_region md_count))

let unpack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: U32.t{U32.v md_count < U32.v metadata_max})
  : SteelGhost unit opened
    (A.varray (md_array md_region md_count))
    (fun _ -> A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) 1sz))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region (u32_to_sz md_count)) 1sz) h1 ==
      A.asel (md_array md_region md_count) h0)
  = change_equal_slprop
      (A.varray (md_array md_region md_count))
      (A.varray (A.split_l (A.split_r md_region (u32_to_sz md_count)) 1sz))

let t (size_class: sc) : Type0 =
  dtuple2
    (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
    (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class)))) (U32.v (nb_slots size_class)))
  & Seq.lseq U8.t 0

let f_lemma
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: Seq.lseq AL.status (U32.v md_count_v))
  (i: U32.t{U32.v i < U32.v md_count_v})
  : Lemma
  (t_of (f size_class slab_region md_bm_region md_count_v md_region_lv i)
  == t size_class)
  = slab_vprop_lemma size_class
    (slab_array slab_region i)
    (md_bm_array md_bm_region i)

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let pack_3
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx1 idx2 idx3 idx4: US.t)
  : SteelGhost unit opened
  (
    vptr md_count `star`
    vptr r1 `star`
    vptr r2 `star`
    vptr r3 `star`
    vptr r4 `star`
    (AL.varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4
      (A.split_l md_region (u32_to_sz md_count_v))
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) h0 in
    U32.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    sel r1 h0 == idx1 /\
    sel r2 h0 == idx2 /\
    sel r3 h0 == idx3 /\
    sel r4 h0 == idx4 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0 (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    ) in
    md_count_v == dfst blob1)
  =
  intro_vrefine
    (ind_varraylist_aux2 pred1 pred2 pred3 pred4
      (A.split_l md_region (u32_to_sz md_count_v)) (((idx1, idx2), idx3), idx4))
    (ind_varraylist_aux_refinement pred1 pred2 pred3 pred4
      (A.split_l md_region (u32_to_sz md_count_v)) (((idx1, idx2), idx3), idx4));
  intro_vdep
    (vptr r1 `star` vptr r2 `star` vptr r3 `star` vptr r4)
    (ind_varraylist_aux pred1 pred2 pred3 pred4 (A.split_l md_region (u32_to_sz md_count_v)) (((idx1, idx2), idx3), idx4))
    (ind_varraylist_aux pred1 pred2 pred3 pred4 (A.split_l md_region (u32_to_sz md_count_v)));

  change_equal_slprop
    (starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_u32_refined (U32.v md_count_v)))
    (left_vprop2 size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv));

  intro_vdep
    (left_vprop1 md_region r1 r2 r3 r4 md_count_v)
    (left_vprop2 size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
    (left_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3 r4 md_count_v);

  intro_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4)
    (left_vprop size_class slab_region md_bm_region md_region r1 r2 r3 r4 md_count_v)
#pop-options

let lemma_slab_aux_starseq
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx:nat{idx < U32.v md_count_v})
  (v:AL.status)
  : Lemma
  (let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
   let f2 = f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
   let s = SeqUtils.init_u32_refined (U32.v md_count_v) in
   forall (k:nat{k <> idx /\ k < Seq.length s}).
     f1 (Seq.index s k) == f2 (Seq.index s k))
  =
  let f1 = f size_class slab_region md_bm_region md_count_v md_region_lv in
  let f2 = f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
  let md_region_lv' = Seq.upd (G.reveal md_region_lv) idx v in
  let s = SeqUtils.init_u32_refined (U32.v md_count_v) in
  let aux (k:nat{k <> idx /\ k < Seq.length s})
    : Lemma (f1 (Seq.index s k) == f2 (Seq.index s k))
    = let i = Seq.index s k in
      SeqUtils.init_u32_refined_index (U32.v md_count_v) k;
      assert (Seq.index md_region_lv (U32.v i) == Seq.index md_region_lv' (U32.v i))
  in Classical.forall_intro aux

//checkpoint

#push-options "--z3rlimit 75 --compat_pre_typed_indexed_effects"
let pack_slab_starseq
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3 r4: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (U32.v md_count_v)))
  (idx: US.t{US.v idx < U32.v md_count_v})
  (v: AL.status)
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx)) `star`
    (starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_u32_refined (U32.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_u32_refined (U32.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:U32.t{U32.v pos < U32.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (SeqUtils.init_u32_refined (U32.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx)))
    = h0 (slab_vprop size_class
      (slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx))) in
    let md : Seq.lseq U64.t 4 = dfst (fst md_blob) in
    (v == 3ul ==> True) /\
    (v == 2ul ==> is_full size_class md) /\
    (v == 1ul ==> is_partial size_class md) /\
    (v == 0ul ==> is_empty size_class md) /\
    idx <> AL.null_ptr
  )
  (ensures fun h0 _ h1 -> True)
  =
  SeqUtils.init_u32_refined_index (U32.v md_count_v) (US.v idx);
  if U32.eq v 2ul then (
    p_full_pack size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx));
    change_equal_slprop
      (p_full size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx), slab_array slab_region (US.sizet_to_uint32 idx)))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx)))
  ) else if U32.eq v 1ul then (
    p_partial_pack size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx));
    change_equal_slprop
      (p_partial size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx), slab_array slab_region (US.sizet_to_uint32 idx)))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx)))
  ) else (
     p_empty_pack size_class
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx))
      (md_bm_array md_bm_region (US.sizet_to_uint32 idx),
      slab_array slab_region (US.sizet_to_uint32 idx));
    change_equal_slprop
      (p_empty size_class (md_bm_array md_bm_region (US.sizet_to_uint32 idx), slab_array slab_region (US.sizet_to_uint32 idx)))
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_u32_refined (U32.v md_count_v)) (US.v idx)))
  );
  lemma_slab_aux_starseq size_class
    slab_region md_bm_region md_region
    md_count_v md_region_lv (US.v idx) v;
  starseq_upd_pack
    #_
    #(pos:U32.t{U32.v pos < U32.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v md_region_lv)
    (f size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (SeqUtils.init_u32_refined (U32.v md_count_v))
    (US.v idx)
#pop-options

#push-options "--z3rlimit 20 --compat_pre_typed_indexed_effects"
let pack_right_and_refactor_vrefine_dep
  (#opened:_)
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  (r1 r2 r3: ref US.t)
  (md_count_v: U32.t{U32.v md_count_v <= U32.v metadata_max})
  : SteelGhost unit opened
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3)
    `star`
    (right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v `star`
    A.varrayp (A.split_l slab_region 0sz) halfp)
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
  )
  (requires fun h0 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3)
    ) in
    md_count_v == dfst blob0)
  (ensures fun h0 _ h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
    ) in
    dfst blob0 == dfst blob1
  )
  =
  let md_count_v' = elim_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3) in
  assert (G.reveal md_count_v' == md_count_v);
  change_equal_slprop
    (right_vprop (A.split_r slab_region 0sz) md_bm_region md_region md_count_v)
    (right_vprop (A.split_r slab_region 0sz) md_bm_region md_region (G.reveal md_count_v'));
  intro_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r1 r2 r3)
    (left_vprop size_class (A.split_r slab_region 0sz) md_bm_region md_region r1 r2 r3 (G.reveal md_count_v') `star`
    right_vprop (A.split_r slab_region 0sz) md_bm_region md_region (G.reveal md_count_v') `star`
    A.varrayp (A.split_l slab_region 0sz) halfp)
#pop-options
