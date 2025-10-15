module SlabsCommon

#push-options "--fuel 0 --ifuel 0"
let lemma_partition_and_pred_implies_mem2
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  = ALG.lemma_mem_ptrs_in hd1 s idx;
    ALG.lemma_mem_ptrs_in hd2 s idx;
    ALG.lemma_mem_ptrs_in hd3 s idx;
    ALG.lemma_mem_ptrs_in hd4 s idx;
    ALG.lemma_mem_ptrs_in hd5 s idx;
    ALG.is_dlist2_implies_spec pred5 hd5 tl5 s;
    let open FStar.FiniteSet.Ambient in
    (* Need this assert to trigger the right SMTPats in FiniteSet.Ambiant *)
    assert (FStar.FiniteSet.Base.mem idx (ALG.ptrs_all hd1 hd2 hd3 hd4 hd5 s));
    Classical.move_requires (ALG.lemma_mem_implies_pred pred1 hd1 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred2 hd2 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred3 hd3 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred4 hd4 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred5 hd5 s) idx

let lemma_partition_and_pred_implies_mem3
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  = ALG.lemma_mem_ptrs_in hd1 s idx;
    ALG.lemma_mem_ptrs_in hd2 s idx;
    ALG.lemma_mem_ptrs_in hd3 s idx;
    ALG.lemma_mem_ptrs_in hd4 s idx;
    ALG.lemma_mem_ptrs_in hd5 s idx;
    ALG.is_dlist2_implies_spec pred5 hd5 tl5 s;
    let open FStar.FiniteSet.Ambient in
    (* Need this assert to trigger the right SMTPats in FiniteSet.Ambiant *)
    assert (FStar.FiniteSet.Base.mem idx (ALG.ptrs_all hd1 hd2 hd3 hd4 hd5 s));
    Classical.move_requires (ALG.lemma_mem_implies_pred pred1 hd1 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred2 hd2 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred3 hd3 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred4 hd4 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred5 hd5 s) idx

let lemma_partition_and_pred_implies_mem5
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  = ALG.lemma_mem_ptrs_in hd1 s idx;
    ALG.lemma_mem_ptrs_in hd2 s idx;
    ALG.lemma_mem_ptrs_in hd3 s idx;
    ALG.lemma_mem_ptrs_in hd4 s idx;
    ALG.lemma_mem_ptrs_in hd5 s idx;
    //ALG.is_dlist2_implies_spec pred5 hd5 tl5 s;
    let open FStar.FiniteSet.Ambient in
    (* Need this assert to trigger the right SMTPats in FiniteSet.Ambiant *)
    assert (FStar.FiniteSet.Base.mem idx (ALG.ptrs_all hd1 hd2 hd3 hd4 hd5 s));
    Classical.move_requires (ALG.lemma_mem_implies_pred pred1 hd1 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred2 hd2 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred3 hd3 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred4 hd4 s) idx;
    Classical.move_requires (ALG.lemma_mem_implies_pred pred5 hd5 s) idx
#pop-options

let t size_class : Type0 =
  dtuple2
    (x:Seq.lseq U64.t 4{slab_vprop_aux2 size_class x})
   (fun _ -> Seq.lseq (G.erased (option (Seq.lseq U8.t (U32.v size_class.sc)))) (U32.v (nb_slots size_class)))
  & Seq.lseq U8.t (U32.v size_class.slab_size - US.v (rounding size_class))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let empty_md_is_properly_zeroed size_class
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
  ((| Seq.create 4 0UL, Seq.create (U32.v (nb_slots size_class)) (Ghost.hide None) |), Seq.create (U32.v size_class.slab_size - US.v (rounding size_class)) U8.zero)



#push-options "--z3rlimit 50 --compat_pre_typed_indexed_effects"
let p_empty_unpack sc b1 b2
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

let p_partial_unpack sc b1 b2
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

let p_full_unpack sc b1 b2
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

let p_empty_pack sc b1 b2
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

let p_partial_pack sc b1 b2
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

let p_full_pack sc b1 b2
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

let p_guard_pack size_class b
  =
  intro_vrewrite (guard_slab size_class (snd b) `star` A.varray (fst b)) (fun _ -> empty_t size_class)

let p_quarantine_pack sc b
  =
  VR2.intro_vrefine
    (quarantine_slab sc (snd b) `star` A.varray (fst b))
    (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL);
  intro_vrewrite
    (quarantine_slab sc (snd b) `star` A.varray (fst b)
    `VR2.vrefine`
    (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL))
    (fun _ -> empty_t sc)

let p_quarantine_unpack sc b
  =
  elim_vrewrite
    (quarantine_slab sc (snd b) `star` A.varray (fst b)
    `VR2.vrefine`
    (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL))
    (fun _ -> empty_t sc);
  VR2.elim_vrefine
    (quarantine_slab sc (snd b) `star` A.varray (fst b))
    (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL)
#pop-options

#restart-solver

let slab_array
  sc
  slab_region
  md_count
  =
  let ptr = A.ptr_of slab_region in
  let page_size_t = u32_to_sz sc.slab_size in
  let shift_size_t = US.mul md_count page_size_t in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide (U32.v sc.slab_size)|)

let pack_slab_array
  sc
  slab_region
  md_count
  = change_equal_slprop
    (A.varray (A.split_l (A.split_r slab_region (US.mul md_count (u32_to_sz sc.slab_size))) (u32_to_sz sc.slab_size)))
    (A.varray (slab_array sc slab_region md_count))

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
  sc
  slab_region
  md_bm_region
  md_coutn_v
  md_region_lv
  i
  =
  slab_vprop_lemma sc
    (slab_array sc slab_region i)
    (md_bm_array md_bm_region i)

#restart-solver

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let ind_varraylist_aux2_lemma_aux
  (#a: Type)
  (s: Seq.seq a)
  (l: list a)
  (i:nat{i < Seq.length s})
  : Lemma
  (requires
    s == Seq.seq_of_list l
  )
  (ensures
    List.Tot.index l i == Seq.index s i
  )
  =
  Seq.lemma_list_seq_bij l;
  Seq.lemma_index_is_nth s i

let ind_varraylist_aux2_lemma
  (r_varraylist: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Lemma
  (requires
    idx1 == Seq.index idxs 0 /\
    idx2 == Seq.index idxs 1 /\
    idx3 == Seq.index idxs 2 /\
    idx4 == Seq.index idxs 3 /\
    idx5 == Seq.index idxs 4 /\
    idx6 == Seq.index idxs 5 /\
    idx7 == Seq.index idxs 6
  )
  (ensures (
    let l : list US.t
      = [ idx1; idx2; idx3; idx4; idx5; idx6; idx7 ] in
    let s : Seq.seq US.t = Seq.seq_of_list l in
    List.Tot.length l == 7 /\
    Seq.length s == 7 /\
    s `Seq.equal` idxs /\
    ind_varraylist_aux2 r_varraylist idxs
    ==
    AL.varraylist pred1 pred2 pred3 pred4 pred5 r_varraylist
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idx5) (US.v idx6) (US.v idx7)
  ))
  =
  let l : list US.t
    = [ idx1; idx2; idx3; idx4; idx5; idx6; idx7 ] in
  let s : Seq.seq US.t = Seq.seq_of_list l in
  let l_length = List.Tot.length l in
  assert (l_length == 7);
  assert (Seq.length s == 7);
  Classical.forall_intro (Classical.move_requires (
    ind_varraylist_aux2_lemma_aux s l
  ));
  Seq.lemma_eq_intro idxs s

let pack_3
  sc
  slab_region
  md_bm_region
  md_region
  md_count
  r_idxs
  md_count_v
  md_region_lv
  idx1 idx2 idx3 idx4 idx5 idx6 idx7
  =
  let h0 = get () in
  let idxs : G.erased (Seq.lseq US.t 7)
    = A.asel r_idxs h0 in
  ind_varraylist_aux2_lemma
    (A.split_l md_region md_count_v) (G.reveal idxs)
    idx1
    idx2
    idx3
    idx4
    idx5
    idx6
    idx7;
  change_equal_slprop
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7))
    (ind_varraylist_aux2
      (A.split_l md_region md_count_v)
      idxs);
  intro_vrefine
    (ind_varraylist_aux2
      (A.split_l md_region md_count_v)
      idxs)
    (ind_varraylist_aux_refinement
      (A.split_l md_region md_count_v)
      idxs);
  intro_vdep
    (A.varray r_idxs)
    (ind_varraylist_aux
      (A.split_l md_region md_count_v)
      idxs)
    (ind_varraylist_aux
      (A.split_l md_region md_count_v));

  change_equal_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t sc)
      (f sc slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma sc slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_us_refined (US.v md_count_v)))
    (left_vprop2_aux sc slab_region md_bm_region md_count_v (G.reveal md_region_lv));

  intro_vdep
    (left_vprop1 md_region r_idxs md_count_v)
    (left_vprop2_aux sc slab_region md_bm_region md_count_v (G.reveal md_region_lv))
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs md_count_v);

  intro_vrefinedep
    (vptr md_count)
    (vrefinedep_prop sc)
    (left_vprop sc slab_region md_bm_region md_region r_idxs)
    (left_vprop sc slab_region md_bm_region md_region r_idxs md_count_v)
#pop-options

#restart-solver

let lemma_slab_aux_starseq
  (sc: sc_full)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (md_count_v: US.t{US.v md_count_v <= US.v sc.md_max})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx:nat{idx < US.v md_count_v})
  (v:AL.status)
  : Lemma
  (let f1 = f sc slab_region md_bm_region md_count_v md_region_lv in
   let f2 = f sc slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
   let s = SeqUtils.init_us_refined (US.v md_count_v) in
   forall (k:nat{k <> idx /\ k < Seq.length s}).
     f1 (Seq.index s k) == f2 (Seq.index s k))
  =
  let f1 = f sc slab_region md_bm_region md_count_v md_region_lv in
  let f2 = f sc slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) idx v) in
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
  sc
  slab_region
  md_bm_region
  md_region
  md_count
  md_count_v
  md_region_lv
  idx
  v
  =
  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx);
  if (U32.eq v 2ul) then (
    p_full_pack sc
      (md_bm_array md_bm_region idx,
      slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx,
      slab_array sc slab_region idx);
    change_equal_slprop
      (p_full sc (md_bm_array md_bm_region idx, slab_array sc slab_region idx))
      (f sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)))
  ) else if (U32.eq v 1ul) then (
    p_partial_pack sc
      (md_bm_array md_bm_region idx,
      slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx,
      slab_array sc slab_region idx);
    change_equal_slprop
      (p_partial sc (md_bm_array md_bm_region idx, slab_array sc slab_region idx))
      (f sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)))
  ) else (
    p_empty_pack sc
      (md_bm_array md_bm_region idx,
      slab_array sc slab_region idx)
      (md_bm_array md_bm_region idx,
      slab_array sc slab_region idx);
    change_equal_slprop
      (p_empty sc (md_bm_array md_bm_region idx, slab_array sc slab_region idx))
      (f sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v)
        (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)))
  );
  lemma_slab_aux_starseq sc
    slab_region md_bm_region md_region
    md_count_v md_region_lv (US.v idx) v;
  starseq_upd_pack
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t sc)
    (f sc slab_region md_bm_region md_count_v md_region_lv)
    (f sc slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (f_lemma sc slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma sc slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) v))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx)
#pop-options

let is_empty_and_slab_vprop_aux2_implies_zeroed
  (sc: sc_full)
  (md: Seq.lseq U64.t 4)
  : Lemma
  (requires
    is_empty sc md /\
    slab_vprop_aux2 sc md
  )
  (ensures
    md `Seq.equal` Seq.create 4 0UL
  )
  =
  ()

#push-options "--z3rlimit 40"
let upd_and_pack_slab_starseq_quarantine
  sc
  slab_region
  md_bm_region
  md_region
  md_count
  md_count_v
  md_region_lv
  idx
  =
  let md_as_seq = elim_slab_vprop sc
    (md_bm_array md_bm_region idx) (slab_array sc slab_region idx) in
  Helpers.intro_empty_slab_varray sc md_as_seq (slab_array sc slab_region idx);
  mmap_trap_quarantine sc
    (slab_array sc slab_region idx)
    (u32_to_sz sc.slab_size);

  SeqUtils.init_us_refined_index (US.v md_count_v) (US.v idx);
  is_empty_and_slab_vprop_aux2_implies_zeroed sc md_as_seq;
  p_quarantine_pack sc (md_bm_array md_bm_region idx, slab_array sc slab_region idx);
  change_equal_slprop
    (p_quarantine sc (md_bm_array md_bm_region idx, slab_array sc slab_region idx))
    (f sc slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) 4ul)
      (Seq.index (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx)));
  lemma_slab_aux_starseq sc
    slab_region md_bm_region md_region
    md_count_v md_region_lv (US.v idx) 4ul;
  starseq_upd_pack
    #_
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t sc)
    (f sc slab_region md_bm_region md_count_v md_region_lv)
    (f sc slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) 4ul))
    (f_lemma sc slab_region md_bm_region md_count_v md_region_lv)
    (f_lemma sc slab_region md_bm_region md_count_v (Seq.upd (G.reveal md_region_lv) (US.v idx) 4ul))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (SeqUtils.init_us_refined (US.v md_count_v))
    (US.v idx)
#pop-options

#push-options "--z3rlimit 20 --compat_pre_typed_indexed_effects"
let pack_right_and_refactor_vrefine_dep
  sc
  slab_region
  md_bm_region
  md_region
  md_count
  r_idxs
  md_count_v
  =
  let md_count_v' = elim_vrefinedep
    (vptr md_count)
    (vrefinedep_prop sc)
    (left_vprop sc slab_region md_bm_region md_region r_idxs) in
  assert (G.reveal md_count_v' == md_count_v);
  change_equal_slprop
    (right_vprop sc slab_region md_bm_region md_region md_count_v)
    (right_vprop sc slab_region md_bm_region md_region (G.reveal md_count_v'));

  intro_vrefinedep
    (vptr md_count)
    (vrefinedep_prop sc)
    (size_class_vprop_aux sc slab_region md_bm_region md_region r_idxs)
    (left_vprop sc slab_region md_bm_region md_region r_idxs (G.reveal md_count_v') `star`
    right_vprop sc slab_region md_bm_region md_region (G.reveal md_count_v'))
#pop-options
