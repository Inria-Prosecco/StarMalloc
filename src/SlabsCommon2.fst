module SlabsCommon2

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

let empty_t size_class =
  (|Seq.create 1 false, None|),
    Seq.create (US.v sc_ex_slab_size - U32.v size_class) U8.zero

#restart-solver

#push-options "--fuel 2 --ifuel 1 --query_stats --z3rlimit 100 --compat_pre_typed_indexed_effects"
let p_empty_unpack
  sc b1 b2
  =
  change_slprop_rel
    ((p_empty sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_empty (Seq.index s 0) == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|),_) -> is_empty (Seq.index s 0) == true)

let p_full_unpack
  sc b1 b2
  =
  change_slprop_rel
    ((p_full sc) b1)
    (slab_vprop sc (snd b2) (fst b2)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_full (Seq.index s 0) == true))
    (fun x y -> x == y)
    (fun _ -> ());
  VR2.elim_vrefine
    (slab_vprop sc (snd b2) (fst b2))
    (fun ((|s,_|),_) -> is_full (Seq.index s 0) == true)

let p_empty_pack
  sc b1 b2
 =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|),_) -> is_empty (Seq.index s 0) == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_empty (Seq.index s 0) == true))
    ((p_empty sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

let p_full_pack
  sc b1 b2
  =
  VR2.intro_vrefine
    (slab_vprop sc (snd b1) (fst b1))
    (fun ((|s,_|),_) -> is_full (Seq.index s 0) == true);
  change_slprop_rel
    (slab_vprop sc (snd b1) (fst b1)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_full (Seq.index s 0) == true))
    ((p_full sc) b2)
    (fun x y -> x == y)
    (fun _ -> ())

//let p_guard_pack (#opened:_) size_class b
//  =
//  intro_vrewrite (guard_slab (snd b) `star` A.varray (fst b)) (fun _ -> empty_t size_class)

let p_quarantine_pack (#opened:_) size_class b
  =
  sladmit ()
  //VR2.intro_vrefine
  //  (quarantine_slab (snd b) `star` A.varray (fst b))
  //  (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL);
  //intro_vrewrite
  //  (quarantine_slab (snd b) `star` A.varray (fst b)
  //  `VR2.vrefine`
  //  (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL))
  //  (fun _ -> empty_t size_class)

let p_quarantine_unpack (#opened:_) size_class b
  =
  sladmit ()
  //elim_vrewrite
  //  (quarantine_slab (snd b) `star` A.varray (fst b)
  //  `VR2.vrefine`
  //  (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL))
  //  (fun _ -> empty_t size_class);
  //VR2.elim_vrefine
  //  (quarantine_slab (snd b) `star` A.varray (fst b))
  //  (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL)
#pop-options

inline_for_extraction noextract
let md_bm_array
  md_bm_region
  md_count
  =
  let ptr = A.ptr_of md_bm_region in
  let shift_size_t = md_count in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide 1|)

inline_for_extraction noextract
let slab_array
  slab_region
  md_count
  =
  let ptr = A.ptr_of slab_region in
  let shift_size_t = US.mul md_count sc_ex_slab_size in
  let ptr_shifted = A.ptr_shift ptr shift_size_t in
  (|ptr_shifted, G.hide (US.v sc_ex_slab_size)|)

let pack_slab_array
  slab_region
  md_count
  = change_equal_slprop
    (A.varray (A.split_l (A.split_r slab_region (US.mul md_count sc_ex_slab_size)) sc_ex_slab_size))
    (A.varray (slab_array slab_region md_count))

let pack_md_bm_array
  md_bm_region
  md_count
 = change_equal_slprop
    (A.varray (A.split_l (A.split_r md_bm_region md_count) 1sz))
    (A.varray (md_bm_array md_bm_region md_count))

inline_for_extraction noextract
let md_array
  md_region
  md_count
 =
  let ptr = A.ptr_of md_region in
  let ptr_shifted = A.ptr_shift ptr md_count in
  (|ptr_shifted, G.hide 1|)

let pack_md_array
  md_region
  md_count
  = change_equal_slprop
      (A.varray (A.split_l (A.split_r md_region md_count) 1sz))
      (A.varray (md_array md_region md_count))

let unpack_md_array
  md_region
  md_count
  = change_equal_slprop
      (A.varray (md_array md_region md_count))
      (A.varray (A.split_l (A.split_r md_region md_count) 1sz))

let f_lemma
  size_class
  slab_region
  md_bm_region
  md_count_v
  md_region_lv
  i
  =
  slab_vprop_lemma size_class
    (slab_array slab_region i)
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
  assert_norm (l_length == 7);
  assert (Seq.length s == 7);
  Classical.forall_intro (Classical.move_requires (
    ind_varraylist_aux2_lemma_aux s l
  ));
  Seq.lemma_eq_intro idxs s
  
let pack_3
  size_class
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
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_us_refined (US.v md_count_v)))
    (left_vprop2_aux size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv));

  intro_vdep
    (left_vprop1 md_region r_idxs md_count_v)
    (left_vprop2_aux size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
    (left_vprop2 size_class slab_region md_bm_region md_region r_idxs md_count_v);

  intro_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (left_vprop size_class slab_region md_bm_region md_region r_idxs)
    (left_vprop size_class slab_region md_bm_region md_region r_idxs md_count_v)
#pop-options

#restart-solver

let lemma_slab_aux_starseq
  size_class
  slab_region
  md_bm_region
  md_region
  md_count_v
  md_region_lv
  idx
  v
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
  size_class
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
    p_full_pack size_class
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx)
      (md_bm_array md_bm_region idx,
      slab_array slab_region idx);
    change_equal_slprop
      (p_full size_class (md_bm_array md_bm_region idx, slab_array slab_region idx))
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
let upd_and_pack_slab_starseq_quarantine
  size_class
  slab_region
  md_bm_region
  md_region
  md_count
  md_count_v
  md_region_lv
  idx
  =
  let md_as_seq = elim_slab_vprop size_class
    (slab_array slab_region idx)
    (md_bm_array md_bm_region idx)
  in
  rewrite_slprop
    (slab_vprop_aux size_class
      (A.split_l (slab_array slab_region idx) (u32_to_sz size_class))
      (Seq.index md_as_seq 0))
    (A.varray
      (A.split_l (slab_array slab_region idx) (u32_to_sz size_class)))
    (fun _ -> admit ());
  mmap_trap_quarantine
    size_class
    (A.split_l
      (snd
        (md_bm_array md_bm_region idx,
        slab_array slab_region idx))
      (u32_to_sz size_class))
    (u32_to_sz size_class);
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
  size_class
  slab_region
  md_bm_region
  md_region
  md_count
  r_idxs
  md_count_v
  =
  let md_count_v' = elim_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (left_vprop size_class slab_region md_bm_region md_region r_idxs) in
  assert (G.reveal md_count_v' == md_count_v);
  change_equal_slprop
    (right_vprop slab_region md_bm_region md_region md_count_v)
    (right_vprop slab_region md_bm_region md_region (G.reveal md_count_v'));

  intro_vrefinedep
    (vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
    (left_vprop size_class slab_region md_bm_region md_region r_idxs (G.reveal md_count_v') `star`
    right_vprop slab_region md_bm_region md_region (G.reveal md_count_v'))
#pop-options
