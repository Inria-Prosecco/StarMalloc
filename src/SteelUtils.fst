module SteelUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory
module L = FStar.List.Tot
module G = FStar.Ghost

let rec starl_append (l1 l2: list vprop)
  : Lemma
  (starl (L.append l1 l2) `equiv` (starl l1 `star` starl l2))
  = match l1 with
  | [] ->
    cm_identity (starl l2);
    equiv_sym (emp `star` starl l2) (starl l2)
  | hd :: tl ->
    // Unfortunately, the transitivity rules for equiv are not automatic,
    // which prevents us from using a single calc
    calc (equiv) {
      starl (L.append l1 l2);
      (equiv) {
        starl_append tl l2;
        equiv_refl hd;
        star_congruence hd (starl (L.append tl l2)) hd (starl tl `star` starl l2)  }
      hd `star` (starl tl `star` starl l2);
    };

    calc (equiv) {
      hd `star` (starl tl `star` starl l2);
      (equiv) {
        star_associative hd (starl tl) (starl l2);
        equiv_sym (starl l1 `star` starl l2) (hd `star` (starl tl `star` starl l2))
      }
      starl l1 `star` starl l2;
    };

    equiv_trans
      (starl (L.append l1 l2))
      (hd `star` (starl tl `star` starl l2))
      (starl l1 `star` starl l2)

let starl_seq_append (s1 s2: Seq.seq vprop)
  : Lemma
  (starl_seq (Seq.append s1 s2) `equiv` (starl_seq s1 `star` starl_seq s2))
  =
  let l1 = Seq.seq_to_list s1 in
  let l2 = Seq.seq_to_list s2 in
  SeqUtils.lemma_seq_to_list_append s1 s2;
  starl_append l1 l2

let starl_seq_unpack (s: Seq.seq vprop) (n: nat)
  : Lemma
  (requires n < Seq.length s)
  (ensures
    starl_seq s
    `equiv`
    (Seq.index s n `star`
      (starl_seq (Seq.slice s 0 n) `star`
       starl_seq (Seq.slice s (n+1) (Seq.length s))))
  )
  =
  let s1, s2 = Seq.split s n in
  Seq.lemma_split s n;
  starl_seq_append s1 s2;
  assert (starl_seq s `equiv` (starl_seq s1 `star` starl_seq s2));
  let s21, s22 = Seq.split s2 1 in
  Seq.lemma_split s2 1;
  starl_seq_append s21 s22;
  assert (starl_seq s2 `equiv` (starl_seq s21 `star` starl_seq s22));
  equiv_refl (starl_seq s1);
  star_congruence
    (starl_seq s1) (starl_seq s2)
    (starl_seq s1) (starl_seq s21 `star` starl_seq s22);

  Seq.lemma_index_slice s n (Seq.length s) 0;
  assert (Seq.index s2 0 == Seq.index s n);
  Seq.lemma_index_slice s2 0 1 0;
  assert (Seq.index s21 0 == Seq.index s n);
  equiv_refl (starl_seq s21);
  assert_norm (starl_seq s21 == Seq.index s n `star` emp);
  assert (starl_seq s21 `equiv` (Seq.index s n `star` emp));
  star_commutative (Seq.index s n) emp;
  assert ((Seq.index s n `star` emp) `equiv` (emp `star` Seq.index s n));
  cm_identity (Seq.index s n);
  equiv_trans
    (starl_seq s21)
    (Seq.index s n `star` emp)
    (emp `star` Seq.index s n);
  equiv_trans
    (starl_seq s21)
    (emp `star` Seq.index s n)
    (Seq.index s n);
  equiv_refl (starl_seq s22);
  star_congruence
    (starl_seq s21) (starl_seq s22)
    (Seq.index s n) (starl_seq s22);
  equiv_refl (starl_seq s1);
  star_congruence
    (starl_seq s1) (starl_seq s21 `star` starl_seq s22)
    (starl_seq s1) (Seq.index s n `star` starl_seq s22);
  equiv_trans
    (starl_seq s)
    (starl_seq s1 `star` starl_seq s2)
    (starl_seq s1 `star` (starl_seq s21 `star` starl_seq s22));
  equiv_trans
    (starl_seq s)
    (starl_seq s1 `star` (starl_seq s21 `star` starl_seq s22))
    (starl_seq s1 `star` (Seq.index s n `star` starl_seq s22));
  star_associative
    (starl_seq s1)
    (Seq.index s n)
    (starl_seq s22);
  equiv_sym
    ((starl_seq s1 `star` Seq.index s n) `star` starl_seq s22)
    (starl_seq s1 `star` (Seq.index s n `star` starl_seq s22));
  equiv_trans
    (starl_seq s)
    (starl_seq s1 `star` (Seq.index s n `star` starl_seq s22))
    ((starl_seq s1 `star` Seq.index s n) `star` starl_seq s22);
  star_commutative
    (starl_seq s1)
    (Seq.index s n);
  star_congruence
    (starl_seq s1 `star` Seq.index s n) (starl_seq s22)
    (Seq.index s n `star` starl_seq s1) (starl_seq s22);
  equiv_trans
    (starl_seq s)
    ((starl_seq s1 `star` Seq.index s n) `star` starl_seq s22)
    ((Seq.index s n `star` starl_seq s1) `star` starl_seq s22);
  star_associative
    (Seq.index s n)
    (starl_seq s1)
    (starl_seq s22);
  equiv_trans
    (starl_seq s)
    ((Seq.index s n `star` starl_seq s1) `star` starl_seq s22)
    (Seq.index s n `star` (starl_seq s1 `star` starl_seq s22));
  ()

let starl_seq_pack (s: Seq.seq vprop) (n: nat)
  : Lemma
  (requires n < Seq.length s)
  (ensures
    (Seq.index s n `star`
      (starl_seq (Seq.slice s 0 n) `star`
       starl_seq (Seq.slice s (n+1) (Seq.length s))))
    `equiv`
    starl_seq s
  )
  =
  starl_seq_unpack s n;
  equiv_sym
    (starl_seq s)
    (Seq.index s n `star`
      (starl_seq (Seq.slice s 0 n) `star`
       starl_seq (Seq.slice s (n+1) (Seq.length s))))

let starl_seq_imp (s: Seq.seq vprop) (k: nat)
  : Lemma
  (requires k < Seq.length s)
  (ensures
    starl_seq s
    `can_be_split`
    Seq.index s k
  )
  =
  starl_seq_unpack s k;
  intro_can_be_split_frame
    (Seq.index s k)
    (starl_seq s)
    (starl_seq (Seq.slice s 0 k) `star`
     starl_seq (Seq.slice s (k+1) (Seq.length s)))

let starl_seq_map_imp (#a #b: Type0)
  (#n: nat)
  (f: a -> vprop)
  (s: Seq.lseq a n)
  (k: nat)
  : Lemma
  (requires k < n)
  (ensures
    starl_seq (Seq.map_seq f s)
    `can_be_split`
    f (Seq.index s k)
  )
  =
  Seq.map_seq_len f s;
  let s' : Seq.lseq vprop n = Seq.map_seq f s in
  assert (Seq.length (Seq.map_seq f s) == Seq.length s);
  assert (k < Seq.length s);
  assert (k < Seq.length (Seq.map_seq f s));
  Classical.forall_intro (Seq.map_seq_index f s);
  assert (Seq.index s' k == f (Seq.index s k));
  starl_seq_imp s' k

let starl_seq_sel_aux (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  (h: hmem (starl_seq (Seq.map_seq f s)))
  (k: nat{k < Seq.length (Seq.map_seq f s)})
  : G.erased b
  =
  Seq.map_seq_len f s;
  let v = Seq.index s k in
  starl_seq_map_imp #a #b #(Seq.length s) f s k;
  assert (starl_seq (Seq.map_seq f s) `can_be_split` (f (Seq.index s k)));
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) h;
  let s : selector b (hp_of (f (Seq.index s k))) = sel_of (f v) in
  G.hide (s h)

let starl_seq_sel' (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  : selector' (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))
  =
  Seq.map_seq_len f s;
  fun (h:hmem (starl_seq (Seq.map_seq f s))) ->
    Seq.map_seq
      (fun k -> starl_seq_sel_aux f s h k)
      (SeqUtils.init_nat (Seq.length s))

let starl_seq_sel_depends_only_on_aux (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  (m1: SM.mem{SM.disjoint m0 m1})
  (k: nat{k < Seq.length (Seq.map_seq f s)})
  : Lemma
  (let v1 = starl_seq_sel_aux #a #b f s m0 k in
  let v2 = starl_seq_sel_aux #a #b f s (SM.join m0 m1) k in
  v1 == v2)
  =
  let m' = SM.join m0 m1 in
  let s0 = starl_seq_sel' #a #b f s m0 in
  let s1 = starl_seq_sel' #a #b f s m' in
  Seq.map_seq_len f s;
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f s m0)
    (SeqUtils.init_nat (Seq.length s));
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f s m')
    (SeqUtils.init_nat (Seq.length s));
  let v1 = starl_seq_sel_aux #a #b f s m0 k in
  let v2 = starl_seq_sel_aux #a #b f s m' k in
  starl_seq_map_imp #a #b #(Seq.length s) f s k;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m0;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m'

let starl_seq_sel_depends_only_on_core_aux (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  (k: nat{k < Seq.length (Seq.map_seq f s)})
  : Lemma
  (let v1 = starl_seq_sel_aux #a #b f s m0 k in
  let v2 = starl_seq_sel_aux #a #b f s (SM.core_mem m0) k in
  v1 == v2)
  =
  let s0 = starl_seq_sel' #a #b f s m0 in
  let s1 = starl_seq_sel' #a #b f s (SM.core_mem m0) in
  Seq.map_seq_len f s;
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f s m0)
    (SeqUtils.init_nat (Seq.length s));
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f s (SM.core_mem m0))
    (SeqUtils.init_nat (Seq.length s));
  let v1 = starl_seq_sel_aux #a #b f s m0 k in
  let v2 = starl_seq_sel_aux #a #b f s (SM.core_mem m0) k in
  starl_seq_map_imp #a #b #(Seq.length s) f s k;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m0;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) (SM.core_mem m0)

let starl_seq_sel_depends_only_on (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  (m1: SM.mem{SM.disjoint m0 m1})
  : Lemma
  (starl_seq_sel' #a #b f s m0 == starl_seq_sel' #a #b f s (SM.join m0 m1))
  =
  let m' = SM.join m0 m1 in
  let s1 = starl_seq_sel' #a #b f s m0 in
  let s2 = starl_seq_sel' #a #b f s m' in
  Seq.map_seq_len f s;
  Seq.map_seq_len
    (fun k -> starl_seq_sel_aux #a #b f s m0 k)
    (SeqUtils.init_nat (Seq.length s));
  Seq.map_seq_len
    (fun k -> starl_seq_sel_aux #a #b f s m' k)
    (SeqUtils.init_nat (Seq.length s));
  let s1' =
    Seq.map_seq
      (fun k -> starl_seq_sel_aux f s m0 k)
      (SeqUtils.init_nat (Seq.length s)) in
  let s2' =
    Seq.map_seq
      (fun k -> starl_seq_sel_aux f s m' k)
      (SeqUtils.init_nat (Seq.length s)) in
    //Seq.map_seq
    //  (starl_seq_sel_aux f s m0)
    //  (SeqUtils.init_nat (Seq.length s)) in
  assert (s1 == s1');
  assert_norm (s2 == s2');
  Classical.forall_intro (
    Seq.map_seq_index
      (fun k -> starl_seq_sel_aux #a #b f s m0 k)
      (SeqUtils.init_nat (Seq.length s))
  );
  Classical.forall_intro (
    Seq.map_seq_index
      (fun k -> starl_seq_sel_aux #a #b f s m' k)
      (SeqUtils.init_nat (Seq.length s))
  );
  Classical.forall_intro (
    starl_seq_sel_depends_only_on_aux #a #b f s m0 m1
  );
  Seq.lemma_eq_intro #(G.erased b) s1 s2

let starl_seq_sel_depends_only_on_core (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  : Lemma
  (starl_seq_sel' #a #b f s m0 == starl_seq_sel' #a #b f s (SM.core_mem m0))
  =
  let m' = SM.core_mem m0 in
  let s1 = starl_seq_sel' #a #b f s m0 in
  let s2 = starl_seq_sel' #a #b f s m' in
  Seq.map_seq_len f s;
  let s1' =
    Seq.map_seq
      (fun k -> starl_seq_sel_aux f s m0 k)
      (SeqUtils.init_nat (Seq.length s)) in
  let s2' =
    Seq.map_seq
      (fun k -> starl_seq_sel_aux f s m' k)
      (SeqUtils.init_nat (Seq.length s)) in
    //Seq.map_seq
    //  (starl_seq_sel_aux f s m0)
    //  (SeqUtils.init_nat (Seq.length s)) in
  assert (s1 == s1');
  assert_norm (s2 == s2');
  Seq.map_seq_len
    (fun k -> starl_seq_sel_aux #a #b f s m0 k)
    (SeqUtils.init_nat (Seq.length s));
  Seq.map_seq_len
    (fun k -> starl_seq_sel_aux #a #b f s m' k)
    (SeqUtils.init_nat (Seq.length s));
  Classical.forall_intro (
    Seq.map_seq_index
      (fun k -> starl_seq_sel_aux #a #b f s m0 k)
      (SeqUtils.init_nat (Seq.length s))
  );
  Classical.forall_intro (
    Seq.map_seq_index
      (fun k -> starl_seq_sel_aux #a #b f s m' k)
      (SeqUtils.init_nat (Seq.length s))
  );
  Classical.forall_intro (
    starl_seq_sel_depends_only_on_core_aux #a #b f s m0
  );
  Seq.lemma_eq_intro #(G.erased b) s1 s2

let starl_seq_sel (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  : selector (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))
  =
  Seq.map_seq_len f s;
  Classical.forall_intro_2 (starl_seq_sel_depends_only_on #a #b f s);
  Classical.forall_intro (starl_seq_sel_depends_only_on_core #a #b f s);
  starl_seq_sel' f s
