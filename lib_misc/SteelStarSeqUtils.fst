module SteelStarSeqUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory
module L = FStar.List.Tot
module G = FStar.Ghost
open SteelOptUtils

let starl (l: list vprop)
  : vprop
  =
  L.fold_right star l emp

let starl_seq (s: Seq.seq vprop)
  : vprop
  =
  starl (Seq.seq_to_list s)

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

let starl_seq_unpack (s: Seq.seq vprop) (n: nat{n < Seq.length s})
  : Lemma
  //(requires n < Seq.length s)
  //(ensures
  (
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
  (f: a -> vprop)
  (s: Seq.seq a)
  (k: nat)
  : Lemma
  (requires k < Seq.length s)
  (ensures
    starl_seq (Seq.map_seq f s)
    `can_be_split`
    f (Seq.index s k)
  )
  =
  Seq.map_seq_len f s;
  Classical.forall_intro (Seq.map_seq_index f s);
  starl_seq_imp (Seq.map_seq f s) k

//let vpb (b: Type0) = vp:vprop{t_of vp == b}

let starl_seq_sel_aux (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (h: hmem (starl_seq (Seq.map_seq f s)))
  (k: nat{k < Seq.length s})
  : G.erased b
  =
  Seq.map_seq_len f s;
  let v = Seq.index s k in
  starl_seq_map_imp #a #b f s k;
  assert (starl_seq (Seq.map_seq f s) `can_be_split` (f (Seq.index s k)));
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) h;
  f_lemma v;
  let s : selector b (hp_of (f (Seq.index s k))) = sel_of (f v) in
  G.hide (s h)

#set-options "--print_implicits --print_universes"

let starl_seq_sel' (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : selector' (Seq.lseq (G.erased b) (Seq.length s)) (hp_of (starl_seq (Seq.map_seq f s)))
  =
  Seq.map_seq_len f s;
  fun (h:hmem (starl_seq (Seq.map_seq f s))) ->
    let f' = starl_seq_sel_aux #a #b f f_lemma s h in
    let s' = SeqUtils.init_nat (Seq.length s) in
    Seq.map_seq_len f' s';
    SeqUtils.init_nat_len (Seq.length s);
    Seq.map_seq f' s'

let starl_seq_sel_depends_only_on_aux (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  (m1: SM.mem{SM.disjoint m0 m1})
  (k: nat{k < Seq.length s})
  : Lemma
  (
  Seq.map_seq_len f s;
  let v1 = starl_seq_sel_aux #a #b f f_lemma s m0 k in
  let v2 = starl_seq_sel_aux #a #b f f_lemma s (SM.join m0 m1) k in
  v1 == v2)
  =
  let m' = SM.join m0 m1 in
  let s0 = starl_seq_sel' #a #b f f_lemma s m0 in
  let s1 = starl_seq_sel' #a #b f f_lemma s m' in
  Seq.map_seq_len f s;
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f f_lemma s m0)
    (SeqUtils.init_nat (Seq.length s));
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f f_lemma s m')
    (SeqUtils.init_nat (Seq.length s));
  let v1 = starl_seq_sel_aux #a #b f f_lemma s m0 k in
  let v2 = starl_seq_sel_aux #a #b f f_lemma s m' k in
  starl_seq_map_imp #a #b f s k;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m0;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m'

let starl_seq_sel_depends_only_on_core_aux (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  (k: nat{k < Seq.length s})
  : Lemma
  (let v1 = starl_seq_sel_aux #a #b f f_lemma s m0 k in
  let v2 = starl_seq_sel_aux #a #b f f_lemma s (SM.core_mem m0) k in
  v1 == v2)
  =
  let s0 = starl_seq_sel' #a #b f f_lemma s m0 in
  let s1 = starl_seq_sel' #a #b f f_lemma s (SM.core_mem m0) in
  Seq.map_seq_len f s;
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f f_lemma s m0)
    (SeqUtils.init_nat (Seq.length s));
  Seq.map_seq_len
    (starl_seq_sel_aux #a #b f f_lemma s (SM.core_mem m0))
    (SeqUtils.init_nat (Seq.length s));
  let v1 = starl_seq_sel_aux #a #b f f_lemma s m0 k in
  let v2 = starl_seq_sel_aux #a #b f f_lemma s (SM.core_mem m0) k in
  starl_seq_map_imp #a #b f s k;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m0;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) (SM.core_mem m0)

let starl_seq_sel_depends_only_on (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  (m1: SM.mem{SM.disjoint m0 m1})
  : Lemma
    (starl_seq_sel' #a #b f f_lemma s m0
  == starl_seq_sel' #a #b f f_lemma s (SM.join m0 m1))
  =
  let m' = SM.join m0 m1 in
  let s1 = starl_seq_sel' #a #b f f_lemma s m0 in
  let s2 = starl_seq_sel' #a #b f f_lemma s m' in
  Seq.map_seq_len f s;
  let f1 = starl_seq_sel_aux #a #b f f_lemma s m0 in
  let f2 = starl_seq_sel_aux #a #b f f_lemma s m' in
  let s' = SeqUtils.init_nat (Seq.length s) in
  Seq.map_seq_len f1 s';
  Seq.map_seq_len f2 s';
  let s1' = Seq.map_seq f1 s' in
  let s2' = Seq.map_seq f2 s' in
  assert (s1 == s1');
  assert_norm (s2 == s2');
  Classical.forall_intro (Seq.map_seq_index f1 s');
  assert (forall x. Seq.index s1' x == f1 (Seq.index s' x));
  Classical.forall_intro (Seq.map_seq_index f2 s');
  assert (forall x. Seq.index s2' x == f2 (Seq.index s' x));
  SeqUtils.init_nat_len (Seq.length s);
  assert (Seq.length s == Seq.length s');
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s));
  assert (forall x. f1 (Seq.index s' x)
    == starl_seq_sel_aux #a #b f f_lemma s m0 x);
  assert (forall x. f2 (Seq.index s' x)
    == starl_seq_sel_aux #a #b f f_lemma s m' x);
  Classical.forall_intro (
    starl_seq_sel_depends_only_on_aux #a #b f f_lemma s m0 m1
  );
  Seq.lemma_eq_intro #(G.erased b) s1 s2

let starl_seq_sel_depends_only_on_core (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (m0: SM.hmem (hp_of (starl_seq (Seq.map_seq f s))))
  : Lemma
    (starl_seq_sel' #a #b f f_lemma s m0
  == starl_seq_sel' #a #b f f_lemma s (SM.core_mem m0))
  =
  let m' = SM.core_mem m0 in
  let s1 = starl_seq_sel' #a #b f f_lemma s m0 in
  let s2 = starl_seq_sel' #a #b f f_lemma s m' in
  Seq.map_seq_len f s;
  let f1 = starl_seq_sel_aux #a #b f f_lemma s m0 in
  let f2 = starl_seq_sel_aux #a #b f f_lemma s m' in
  let s' = SeqUtils.init_nat (Seq.length s) in
  Seq.map_seq_len f1 s';
  Seq.map_seq_len f2 s';
  let s1' = Seq.map_seq f1 s' in
  let s2' = Seq.map_seq f2 s' in
  assert (s1 == s1');
  assert_norm (s2 == s2');
  Classical.forall_intro (Seq.map_seq_index f1 s');
  assert (forall x. Seq.index s1' x == f1 (Seq.index s' x));
  Classical.forall_intro (Seq.map_seq_index f2 s');
  assert (forall x. Seq.index s2' x == f2 (Seq.index s' x));
  SeqUtils.init_nat_len (Seq.length s);
  assert (Seq.length s == Seq.length s');
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s));
  assert (forall x. f1 (Seq.index s' x)
    == starl_seq_sel_aux #a #b f f_lemma s m0 x);
  assert (forall x. f2 (Seq.index s' x)
    == starl_seq_sel_aux #a #b f f_lemma s m' x);
  Classical.forall_intro (
    starl_seq_sel_depends_only_on_core_aux #a #b f f_lemma s m0
  );
  Seq.lemma_eq_intro #(G.erased b) s1 s2

let starl_seq_sel (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : selector (Seq.lseq (G.erased b) (Seq.length s)) (hp_of (starl_seq (Seq.map_seq f s)))
  =
  Seq.map_seq_len f s;
  Classical.forall_intro_2 (starl_seq_sel_depends_only_on #a #b f f_lemma s);
  Classical.forall_intro (starl_seq_sel_depends_only_on_core #a #b f f_lemma s);
  starl_seq_sel' f f_lemma s

let starseq_equiv (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : Lemma
  (starseq #a #b f f_lemma s `equiv` starl_seq (Seq.map_seq f s))
  =
  let p1 = starseq #a #b f f_lemma s in
  let p2 = starl_seq (Seq.map_seq f s) in
  assert (hp_of p1 `SM.equiv` hp_of p2);
  reveal_equiv p1 p2

#set-options "--print_implicits --print_universes"

let starseq_append (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s1 s2: Seq.seq u#0 a)
  : Lemma
  (starseq #a #b f f_lemma (Seq.append s1 s2)
  `equiv`
  (starseq #a #b f f_lemma s1 `star` starseq #a #b f f_lemma s2))
  =
  let s = Seq.append s1 s2 in
  let u1 : Seq.seq vprop = Seq.map_seq f s1 in
  let u2 : Seq.seq vprop = Seq.map_seq f s2 in
  let u : Seq.seq vprop= Seq.map_seq f s in
  Seq.map_seq_append f s1 s2;
  assert (u == Seq.append u1 u2);
  starseq_equiv #a #b f f_lemma  s;
  starl_seq_append u1 u2;
  equiv_trans
    (starseq #a #b f f_lemma (Seq.append s1 s2))
    (starl_seq (Seq.append u1 u2))
    (starl_seq u1 `star` starl_seq u2);
  starseq_equiv #a #b f f_lemma s1;
  equiv_sym
    (starseq #a #b f f_lemma s1)
    (starl_seq u1);
  starseq_equiv #a #b f f_lemma s2;
  equiv_sym
    (starseq #a #b f f_lemma s2)
    (starl_seq u2);
  star_congruence
    (starl_seq u1) (starl_seq u2)
    (starseq #a #b f f_lemma s1) (starseq #a #b f f_lemma s2);
  equiv_trans
    (starseq #a #b f f_lemma  (Seq.append s1 s2))
    (starl_seq u1 `star` starl_seq u2)
    (starseq #a #b f f_lemma s1 `star` starseq #a #b f f_lemma s2)

let starseq_unpack (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : Lemma
  (
    starseq #a #b f f_lemma s
    `equiv`
    (f (Seq.index s n) `star`
      (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
       starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
  )
  =
  Seq.map_seq_len f s;
  let u = Seq.map_seq f s in
  let u1 = Seq.slice u 0 n in
  let u2 = Seq.slice u (n+1) (Seq.length s) in
  starseq_equiv #a #b f f_lemma s;
  starl_seq_unpack (Seq.map_seq f s) n;
  equiv_trans
    (starseq #a #b f f_lemma s)
    (starl_seq (Seq.map_seq f s))
    (Seq.index (Seq.map_seq f s) n `star`
      (starl_seq u1 `star` starl_seq u2));
  SeqUtils.map_seq_slice f s 0 n;
  SeqUtils.map_seq_slice f s (n+1) (Seq.length s);
  starseq_equiv #a #b f f_lemma (Seq.slice s 0 n);
  equiv_sym
    (starseq #a #b f f_lemma (Seq.slice s 0 n))
    (starl_seq u1);
  starseq_equiv #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s));
  equiv_sym
    (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))
    (starl_seq u2);
  star_congruence
    (starl_seq u1)
    (starl_seq u2)
    (starseq #a #b f f_lemma (Seq.slice s 0 n))
    (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)));
  let u0 : vprop = Seq.index u n in
  let t0 : vprop = f (Seq.index s n) in
  Classical.forall_intro (Seq.map_seq_index f s);
  assert (u0 == t0);
  equiv_refl u0;
  assert (u0 `equiv` t0);
  star_congruence
    u0
    (starl_seq u1 `star`
    starl_seq u2)
    t0
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)));
  equiv_trans
    (starseq #a #b f f_lemma s)
    (Seq.index (Seq.map_seq f s) n `star`
      (starl_seq u1 `star` starl_seq u2))
    (t0 `star`
      (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
      starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))

let starseq_pack (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : Lemma
  (
    (f (Seq.index s n) `star`
      (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
       starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
    `equiv`
    starseq #a #b f f_lemma s
  )
  =
  let p1 =
    (f (Seq.index s n) `star`
      (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
       starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
  in
  let p2 =
    starseq #a #b f f_lemma s
  in
  starseq_unpack #a #b f f_lemma s n;
  equiv_sym p2 p1

let starseq_sel_len (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures
    Seq.length (starl_seq_sel #a #b f f_lemma s m) = Seq.length s
  )
  =
  ()

let starseq_imp_index (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures (
    starseq_sel_len #a #b f f_lemma s m;
    SM.interp (hp_of (f (Seq.index s n))) m
  ))
  =
  starseq_equiv #a #b f f_lemma s;
  equiv_can_be_split
    (starseq #a #b f f_lemma s)
    (starl_seq (Seq.map_seq f s));
  starl_seq_map_imp #a #b f s n;
  can_be_split_trans
    (starseq #a #b f f_lemma s)
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s n));
  can_be_split_interp (starseq #a #b f f_lemma s) (f (Seq.index s n)) m

let starseq_sel_index (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures (
    starseq_sel_len #a #b f f_lemma s m;
    f_lemma (Seq.index s n);
    SM.interp (hp_of (f (Seq.index s n))) m /\
    G.reveal (Seq.index (sel_of (starseq #a #b f f_lemma s) m) n)
    ==
    sel_of (f (Seq.index s n)) m
  ))
  =
  Seq.map_seq_len f s;
  let f' = starl_seq_sel_aux #a #b f f_lemma s m in
  let s' = SeqUtils.init_nat (Seq.length s) in
  Seq.map_seq_len f' s';
  assert (sel_of (starseq #a #b f f_lemma s) m == Seq.map_seq f' s');
  starseq_sel_len #a #b f f_lemma s m;
  assert (Seq.length (Seq.map_seq f' s') = Seq.length s);
  starseq_imp_index #a #b f f_lemma s n m;
  Seq.map_seq_index f' s' n;
  SeqUtils.init_nat_index (Seq.length s) n;
  assert (Seq.index s' n == n);
  f_lemma (Seq.index s n);
  assert (Seq.index (sel_of (starseq #a #b f f_lemma s) m) n == f' n)

let starseq_imp_slice_1 (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures (
    starseq_sel_len #a #b f f_lemma s m;
    SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s 0 n))) m
  ))
  =
  assert (n <= Seq.length s);
  starseq_unpack #a #b f f_lemma s n;
  let p0 = starseq #a #b f f_lemma s in
  let p1 = f (Seq.index s n) in
  let p2 = starseq #a #b f f_lemma (Seq.slice s 0 n) in
  let p3 = starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) in
  assert (p0 `equiv` (p1 `star` (p2 `star` p3)));
  star_associative p1 p2 p3;
  equiv_sym
    ((p1 `star` p2) `star` p3)
    (p1 `star` (p2 `star` p3));
  equiv_trans
    p0
    (p1 `star` (p2 `star` p3))
    ((p1 `star` p2) `star` p3);
  star_commutative p1 p2;
  equiv_refl p3;
  star_congruence
    (p1 `star` p2) p3
    (p2 `star` p1) p3;
  equiv_trans
    p0
    ((p1 `star` p2) `star` p3)
    ((p2 `star` p1) `star` p3);
  star_associative p2 p1 p3;
  equiv_trans
    p0
    ((p2 `star` p1) `star` p3)
    (p2 `star` (p1 `star` p3));
  intro_can_be_split_frame
    p2
    p0
    (p1 `star` p3);
  can_be_split_interp p0 p2 m

let starseq_imp_slice_2 (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures (
    starseq_sel_len #a #b f f_lemma s m;
    SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))) m
  ))
  =
  assert (n <= Seq.length s);
  starseq_unpack #a #b f f_lemma s n;
  let p0 = starseq #a #b f f_lemma s in
  let p1 = f (Seq.index s n) in
  let p2 = starseq #a #b f f_lemma (Seq.slice s 0 n) in
  let p3 = starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) in
  assert (p0 `equiv` (p1 `star` (p2 `star` p3)));
  star_associative p1 p2 p3;
  equiv_sym
    ((p1 `star` p2) `star` p3)
    (p1 `star` (p2 `star` p3));
  equiv_trans
    p0
    (p1 `star` (p2 `star` p3))
    ((p1 `star` p2) `star` p3);
  star_commutative (p1 `star` p2) p3;
  equiv_trans
    p0
    ((p1 `star` p2) `star` p3)
    (p3 `star` (p1 `star` p2));
  intro_can_be_split_frame
    p3
    p0
    (p1 `star` p2);
  can_be_split_interp p0 p3 m

let starseq_sel_slice_1 (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures (
    starseq_sel_len #a #b f f_lemma s m;
    SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s 0 n))) m /\
    sel_of (starseq #a #b f f_lemma (Seq.slice s 0 n)) m
      == Seq.slice (sel_of (starseq #a #b f f_lemma s) m) 0 n
  ))
  =
  Seq.map_seq_len f s;
  let f' = starl_seq_sel_aux #a #b f f_lemma s m in
  let s' = SeqUtils.init_nat (Seq.length s) in
  Seq.map_seq_len f' s';

  let r0 = Seq.map_seq f' s' in
  assert (r0 == sel_of (starseq #a #b f f_lemma s) m);
  starseq_sel_len #a #b f f_lemma s m;
  assert (Seq.length r0 = Seq.length s);
  starseq_imp_slice_1 #a #b f f_lemma s n m;
  assert (SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s 0 n))) m);
  let r1 = Seq.slice r0 0 n in
  let r2 = sel_of (starseq #a #b f f_lemma (Seq.slice s 0 n)) m in
  // prove (r1 == r2)

  let f2' = fun k -> starl_seq_sel_aux #a #b f f_lemma (Seq.slice s 0 n) m k in
  let s2' = SeqUtils.init_nat (Seq.length (Seq.slice s 0 n)) in
  SeqUtils.init_nat_len (Seq.length (Seq.slice s 0 n));
  assert (Seq.length s2' = n);
  assert_norm (r2 == Seq.map_seq f2' s2');
  Seq.lemma_len_slice s' 0 n;
  assert (Seq.length (Seq.slice s' 0 n) = n);
  assert (Seq.length s2' = Seq.length (Seq.slice s' 0 n));
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length (Seq.slice s 0 n)));
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s));
  Classical.forall_intro (SeqUtils.lemma_index_slice s' 0 n);
  assert (forall x. Seq.index s2' x == Seq.index (Seq.slice s' 0 n) x);
  SeqUtils.map_seq_weakening
    f'
    f2'
    (Seq.slice s' 0 n)
    s2';
  assert (r2 == Seq.map_seq f' (Seq.slice s' 0 n));
  SeqUtils.map_seq_slice f' s' 0 n;
  assert (r1 == Seq.map_seq f' (Seq.slice s' 0 n));
  ()

let starseq_sel_slice_2 (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)

  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures (
    starseq_sel_len #a #b f f_lemma s m;
    SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))) m /\
    sel_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) m
      == Seq.slice (sel_of (starseq #a #b f f_lemma s) m) (n+1) (Seq.length s)
  ))
  =
  Seq.map_seq_len f s;
  let f' = starl_seq_sel_aux #a #b f f_lemma s m in
  let s' = SeqUtils.init_nat (Seq.length s) in
  Seq.map_seq_len f' s';

  let r0 = Seq.map_seq f' s' in
  assert (r0 == sel_of (starseq #a #b f f_lemma s) m);
  starseq_sel_len #a #b f f_lemma s m;
  assert (Seq.length r0 = Seq.length s);
  starseq_imp_slice_2 #a #b f f_lemma s n m;
  assert (SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))) m);
  let r1 = Seq.slice r0 (n+1) (Seq.length s) in
  let r2 = sel_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) m in
  // prove (r1 == r2)

  let f2' = starl_seq_sel_aux #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) m in
  let s2' = SeqUtils.init_nat (Seq.length (Seq.slice s (n+1) (Seq.length s))) in
  SeqUtils.init_nat_len (Seq.length (Seq.slice s (n+1) (Seq.length s)));
  assert (Seq.length s2' = Seq.length s - (n+1));
  assert_norm (r2 == Seq.map_seq f2' s2');
  Seq.lemma_len_slice s' (n+1) (Seq.length s);
  assert (Seq.length (Seq.slice s' (n+1) (Seq.length s)) = Seq.length s - (n+1));
  assert (Seq.length s2' = Seq.length (Seq.slice s' (n+1) (Seq.length s)));
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length (Seq.slice s (n+1) (Seq.length s))));
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s));
  Classical.forall_intro (SeqUtils.lemma_index_slice s' (n+1) (Seq.length s));
  assert (forall x. Seq.index s2' x + n+1 == Seq.index (Seq.slice s' (n+1) (Seq.length s)) x);
  SeqUtils.map_seq_weakening
    f'
    f2'
    (Seq.slice s' (n+1) (Seq.length s))
    s2';
  assert (r2 == Seq.map_seq f' (Seq.slice s' (n+1) (Seq.length s)));
  SeqUtils.map_seq_slice f' s' (n+1) (Seq.length s);
  assert (r1 == Seq.map_seq f' (Seq.slice s' (n+1) (Seq.length s)));
  ()

let starseq_unpack_lemma (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m
  )
  (ensures (
    f_lemma (Seq.index s n);
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m /\
    (let v = sel_of (starseq #a #b f f_lemma s) m in
    SM.interp (hp_of (
      f (Seq.index s n) `star`
      (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
      starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))
    )) m /\
    Seq.length v == Seq.length s /\
    sel_of (f (Seq.index s n)) m
      == G.reveal (Seq.index v n) /\
    sel_of (starseq #a #b f f_lemma (Seq.slice s 0 n)) m
      == Seq.slice v 0 n /\
    sel_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) m
      == Seq.slice v (n+1) (Seq.length s)
  )))
  =
  let p1 = starseq #a #b f f_lemma s in
  let p2 =
    f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) in
  starseq_unpack #a #b f f_lemma s n;
  reveal_equiv p1 p2;
  starseq_sel_index #a #b f f_lemma s n m;
  starseq_sel_slice_1 #a #b f f_lemma s n m;
  starseq_sel_slice_2 #a #b f f_lemma s n m

let starseq_pack_lemma (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      f (Seq.index s n) `star`
      (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
      starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))
    )) m)
  (ensures (
    f_lemma (Seq.index s n);
    SM.interp (hp_of (f (Seq.index s n))) m /\
    SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s 0 n))) m /\
    SM.interp (hp_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))) m /\
    (let v_0 = sel_of (f (Seq.index s n)) m in
    let v_1 = sel_of (starseq #a #b f f_lemma (Seq.slice s 0 n)) m in
    let v_2 = sel_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) m in
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m /\
    (let v = sel_of (starseq #a #b f f_lemma s) m in
    Seq.length v == Seq.length s /\
    v_0 == G.reveal (Seq.index v n) /\
    v_1 == Seq.slice v 0 n /\
    v_2 == Seq.slice v (n+1) (Seq.length s)
  ))))
  =
  let p1 = starseq #a #b f f_lemma s in
  let p2 =
    f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) in
  starseq_pack #a #b f f_lemma s n;
  reveal_equiv p2 p1;
  let v = sel_of (starseq #a #b f f_lemma s) m in
  let v_0 = sel_of (f (Seq.index s n)) m in
  let v_1 = sel_of (starseq #a #b f f_lemma (Seq.slice s 0 n)) m in
  let v_2 = sel_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) m in
  f_lemma (Seq.index s n);
  starseq_sel_index #a #b f f_lemma s n m;
  starseq_sel_slice_1 #a #b f f_lemma s n m;
  starseq_sel_slice_2 #a #b f f_lemma s n m

let starseq_empty_equiv_emp (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : Lemma
  (requires Seq.length s == 0)
  (ensures hp_of (starseq #a #b f f_lemma s) == hp_of emp)
  =
  Seq.map_seq_len f s

let starseq_singleton_equiv (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : Lemma
  (requires Seq.length s == 1)
  (ensures hp_of (starseq #a #b f f_lemma s) == hp_of (f (Seq.index s 0) `star` emp))
  =
  Seq.map_seq_len f s;
  Seq.map_seq_index f s 0;
  Seq.lemma_index_is_nth (Seq.map_seq f s) 0;
  assert (hp_of (starseq #a #b f f_lemma s) == hp_of (f (Seq.index s 0) `star` emp))

let starseq_unpack_s (#opened:_) (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : SteelGhost unit opened
  (starseq #a #b f f_lemma s)
  (fun _ ->
    f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))
  )
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    f_lemma (Seq.index s n);
    let v = v_starseq #a #b f f_lemma s h0 in
    Seq.length v = Seq.length s /\
    h1 (f (Seq.index s n)) == G.reveal (Seq.index v n) /\
    v_starseq #a #b f f_lemma (Seq.slice s 0 n) h1
      == Seq.slice v 0 n /\
    v_starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) h1
      == Seq.slice v (n+1) (Seq.length s)
  )
  =
  change_slprop_rel
    (starseq #a #b f f_lemma s)
    (f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
    (fun v (x, (y, z)) ->
      Seq.length v = Seq.length s /\
      (f_lemma (Seq.index s n);
      x == G.reveal (Seq.index v n) /\
      y == Seq.slice v 0 n /\
      z == Seq.slice v (n+1) (Seq.length s))
    )
    (fun m -> starseq_unpack_lemma #a #b f f_lemma s n m)

let starseq_pack_s (#opened:_) (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : SteelGhost unit opened
  (f (Seq.index s n) `star`
  (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
  starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
  (fun _ ->
    starseq #a #b f f_lemma s
  )
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    f_lemma (Seq.index s n);
    let v = v_starseq #a #b f f_lemma s h1 in
    Seq.length v = Seq.length s /\
    h0 (f (Seq.index s n)) == G.reveal (Seq.index v n) /\
    v_starseq #a #b f f_lemma (Seq.slice s 0 n) h0
      == Seq.slice v 0 n /\
    v_starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) h0
      == Seq.slice v (n+1) (Seq.length s)
  )
  =
  change_slprop_rel
    (f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
    (starseq #a #b f f_lemma s)
    (fun (x, (y, z)) v ->
      Seq.length v = Seq.length s /\
      (f_lemma (Seq.index s n);
      x == G.reveal (Seq.index v n) /\
      y == Seq.slice v 0 n /\
      z == Seq.slice v (n+1) (Seq.length s))
    )
    (fun m -> starseq_pack_lemma #a #b f f_lemma s n m)

#push-options "--z3rlimit 20"
let starseq_idem (#opened:_) (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : SteelGhost unit opened
  (starseq #a #b f f_lemma s)
  (fun _ -> starseq #a #b f f_lemma s)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    v_starseq #a #b f f_lemma s h0
    ==
    v_starseq #a #b f f_lemma s h1
  )
  =
  let h0 = get () in
  let v0 = G.hide (v_starseq #a #b f f_lemma s h0) in
  starseq_unpack_s #_ #a #b f f_lemma s n;
  starseq_pack_s #_ #a #b f f_lemma s n;
  let h1 = get () in
  let v1 = G.hide (v_starseq #a #b f f_lemma s h1) in
  assert (Seq.length v0 = Seq.length v1);
  assert (Seq.slice v0 0 n == Seq.slice v1 0 n);
  assert (Seq.index v0 n == Seq.index v1 n);
  assert (Seq.slice v0 (n+1) (Seq.length s) == Seq.slice v1 (n+1) (Seq.length s));
  Classical.forall_intro (Classical.move_requires (
    SeqUtils.lemma_slice_index v0 v1 0 n));
  Classical.forall_intro (Classical.move_requires (
    SeqUtils.lemma_slice_index v0 v1 (n+1) (Seq.length s)));
  assert (forall (x:nat{x < Seq.length s}).
    Seq.index v0 x == Seq.index v1 x);
  Seq.lemma_eq_intro v0 v1
#pop-options

let rec starseq_weakening_lemma_aux_generic
  (#a1 #a2 #b1 #b2: Type0)
  (f1: a1 -> vprop)
  (f2: a2 -> vprop)
  (f1_lemma: (x:a1 -> Lemma (t_of (f1 x) == b1)))
  (f2_lemma: (x:a2 -> Lemma (t_of (f2 x) == b2)))
  (s1: Seq.seq a1)
  (s2: Seq.seq a2)
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}). (
      hp_of (f1 (Seq.index s1 k))
      ==
      hp_of (f2 (Seq.index s2 k))
    )))
  (ensures
    starseq #a1 #b1 f1 f1_lemma s1
    `equiv`
    starseq #a2 #b2 f2 f2_lemma s2
  )
  (decreases Seq.length s1)
  = match Seq.length s1 with
  | 0 ->
    starseq_empty_equiv_emp #a1 #b1 f1 f1_lemma s1;
    starseq_empty_equiv_emp #a2 #b2 f2 f2_lemma s2;
    reveal_equiv
      (starseq #a1 #b1 f1 f1_lemma s1)
      (starseq #a2 #b2 f2 f2_lemma s2)
  | _ ->
    assert (Seq.length s1 > 0);
    if (Seq.length s1 = 1) then (
      starseq_singleton_equiv #a1 #b1 f1 f1_lemma s1;
      starseq_singleton_equiv #a2 #b2 f2 f2_lemma s2;
      reveal_equiv
        (starseq #a1 #b1 f1 f1_lemma s1)
        (starseq #a2 #b2 f2 f2_lemma s2)
    ) else (
      let s11, s12 = Seq.split s1 (Seq.length s1 - 1) in
      let s21, s22 = Seq.split s2 (Seq.length s1 - 1) in
      Seq.lemma_split s1 (Seq.length s1 - 1);
      Seq.lemma_split s2 (Seq.length s1 - 1);
      starseq_append #a1 #b1 f1 f1_lemma s11 s12;
      starseq_append #a2 #b2 f2 f2_lemma s21 s22;
      starseq_weakening_lemma_aux_generic #a1 #a2 #b1 #b2 f1 f2 f1_lemma f2_lemma s11 s21;
      starseq_weakening_lemma_aux_generic #a1 #a2 #b1 #b2 f1 f2 f1_lemma f2_lemma s12 s22;
      star_congruence
        (starseq #a1 #b1 f1 f1_lemma s11)
        (starseq #a1 #b1 f1 f1_lemma s12)
        (starseq #a2 #b2 f2 f2_lemma s21)
        (starseq #a2 #b2 f2 f2_lemma s22);
      equiv_sym
        (starseq #a2 #b2 f2 f2_lemma s2)
        (starseq #a2 #b2 f2 f2_lemma s21 `star`
        starseq #a2 #b2 f2 f2_lemma s22);
      equiv_trans
        (starseq #a1 #b1 f1 f1_lemma s1)
        (starseq #a1 #b1 f1 f1_lemma s11 `star`
        starseq #a1 #b1 f1 f1_lemma s12)
        (starseq #a2 #b2 f2 f2_lemma s21 `star`
        starseq #a2 #b2 f2 f2_lemma s22);
      equiv_trans
        (starseq #a1 #b1 f1 f1_lemma s1)
        (starseq #a2 #b2 f2 f2_lemma s21 `star`
        starseq #a2 #b2 f2 f2_lemma s22)
        (starseq #a2 #b2 f2 f2_lemma s2)
    )

let starseq_weakening_rel_some_lemma_aux_rel (#a #b: Type0)
  (f1: a -> vprop)
  (f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == option b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a)
  (m: SM.mem)
  (k: nat{k < Seq.length s1})
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}). (
      f1_lemma (Seq.index s1 k);
      f2 (Seq.index s2 k)
      ==
      some_as_vp #b (f1 (Seq.index s1 k))
    )) /\
    SM.interp (hp_of (starseq #a #b f1 f1_lemma s1)) m /\
    SM.interp (hp_of (starseq #a #(option b) f2 f2_lemma s2)) m)
  (ensures
    SM.interp (hp_of (f1 (Seq.index s1 k))) m /\
    SM.interp (hp_of (f2 (Seq.index s2 k))) m /\
    starl_seq_sel_aux #a #(option b) f2 f2_lemma s2 m k
    ==
    G.hide (Some (G.reveal (starl_seq_sel_aux #a #b f1 f1_lemma s1 m k)))
  )
  =
  starl_seq_map_imp #a #b f1 s1 k;
  Seq.map_seq_len f1 s1;
  can_be_split_interp
    (starl_seq (Seq.map_seq f1 s1))
    (f1 (Seq.index s1 k)) m;
  ()

let starseq_weakening_rel_some_lemma (#a #b: Type0)
  (f1: a -> vprop)
  (f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == option b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a)
  (m: SM.mem)
  : Lemma
  (requires
    Seq.length s1 == Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}). (
      f1_lemma (Seq.index s1 k);
      f2 (Seq.index s2 k)
      ==
      some_as_vp #b (f1 (Seq.index s1 k))
    )) /\
    SM.interp (hp_of (starseq #a #b f1 f1_lemma s1)) m)
  (ensures (
    let f = fun x -> G.hide (Some (G.reveal x)) in
    SM.interp (hp_of (starseq #a #(option b) f2 f2_lemma s2)) m /\
    (let v2 : Seq.seq (G.erased (option b))
      = sel_of (starseq #a #(option b) f2 f2_lemma s2) m in
    let v1 : Seq.seq (G.erased b)
      = sel_of (starseq #a #b f1 f1_lemma s1) m in
    Seq.map_seq_len f v1;
    v2 == Seq.map_seq f v1
  )))
  =
  let p1 = starseq #a #b f1 f1_lemma s1 in
  let p2 = starseq #a #(option b) f2 f2_lemma s2 in
  starseq_weakening_lemma_aux_generic #a #a #b #(option b) f1 f2 f1_lemma f2_lemma s1 s2;
  reveal_equiv p1 p2;
  assert (SM.interp (hp_of (starseq #a #(option b) f2 f2_lemma s2)) m);
  let v1 : Seq.seq (G.erased b)
    = sel_of (starseq #a #b f1 f1_lemma s1) m in
  let v2 : Seq.seq (G.erased (option b))
    = sel_of (starseq #a #(option b) f2 f2_lemma s2) m in
  assert (Seq.length v1 = Seq.length v2);
  let f1' = starl_seq_sel_aux #a #b f1 f1_lemma s1 m in
  let f2' = starl_seq_sel_aux #a #(option b) f2 f2_lemma s2 m in
  let s1' = SeqUtils.init_nat (Seq.length s1) in
  let s2' = SeqUtils.init_nat (Seq.length s2) in
  assert (v1 == starl_seq_sel #a #b f1 f1_lemma s1 m);
  assert (v2 == starl_seq_sel #a #(option b) f2 f2_lemma s2 m);
  Seq.map_seq_len f1' s1';
  Seq.map_seq_len f2' s2';
  assert (v1 == Seq.map_seq f1' s1');
  assert (v2 == Seq.map_seq f2' s2');
  Classical.forall_intro (Seq.map_seq_index f1' s1');
  Classical.forall_intro (Seq.map_seq_index f2' s2');
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s1));
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s2));
  Classical.forall_intro (fun k -> f1_lemma (Seq.index s1 k));
  Classical.forall_intro (Classical.move_requires (
    starseq_weakening_rel_some_lemma_aux_rel #a #b f1 f2 f1_lemma f2_lemma s1 s2 m
  ));
  let f = fun x -> G.hide (Some (G.reveal x)) in
  Seq.map_seq_len f v1;
  Classical.forall_intro (Seq.map_seq_index f v1);
  Seq.lemma_eq_intro (Seq.map_seq f v1) v2

let starseq_weakening_rel_some (#opened:_)
  (#a #b: Type0)
  (f1: a -> vprop)
  (f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == option b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a)
  : SteelGhost unit opened
  (starseq #a #b f1 f1_lemma s1)
  (fun _ -> starseq #a #(option b) f2 f2_lemma s2)
  (requires fun _ ->
    Seq.length s1 == Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}). (
      f1_lemma (Seq.index s1 k);
      f2 (Seq.index s2 k)
      ==
      some_as_vp #b (f1 (Seq.index s1 k))
    ))
  )
  (ensures fun h0 _ h1 ->
    let f = fun x -> G.hide (Some (G.reveal x)) in
    Seq.map_seq_len f (v_starseq #a #b f1 f1_lemma s1 h0);
    Seq.length s1 = Seq.length s2 /\
    Seq.map_seq f (v_starseq #a #b f1 f1_lemma s1 h0)
    ==
    v_starseq #a #(option b) f2 f2_lemma s2 h1
  )
  =
  let f = fun x -> G.hide (Some (G.reveal x)) in
  change_slprop_rel
    (starseq #a #b f1 f1_lemma s1)
    (starseq #a #(option b) f2 f2_lemma s2)
    (fun x y -> y == Seq.map_seq f x)
    (fun m -> starseq_weakening_rel_some_lemma #a #b
      f1 f2
      f1_lemma f2_lemma
      s1 s2
    m)

let starseq_weakening_lemma (#a1 #a2 #b: Type0)
  (f1: a1 -> vprop)
  (f2: a2 -> vprop)
  (f1_lemma: (x:a1 -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a2 -> Lemma (t_of (f2 x) == b)))
  (s1: Seq.seq a1)
  (s2: Seq.seq a2)
  (m: SM.mem)
  : Lemma
  (requires
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)) /\
    SM.interp (hp_of (starseq #a1 #b f1 f1_lemma s1)) m)
  (ensures
    SM.interp (hp_of (starseq #a2 #b f2 f2_lemma s2)) m /\
    (let v2 : Seq.seq (G.erased b)
      = sel_of (starseq #a2 #b f2 f2_lemma s2) m in
    let v1 : Seq.seq (G.erased b)
      = sel_of (starseq #a1 #b f1 f1_lemma s1) m
    in
    v2 == v1)
  )
  =
  let p1 = starseq #a1 #b f1 f1_lemma s1 in
  let p2 = starseq #a2 #b f2 f2_lemma s2 in
  starseq_weakening_lemma_aux_generic #a1 #a2 #b #b f1 f2 f1_lemma f2_lemma s1 s2;
  reveal_equiv p1 p2;
  assert (SM.interp (hp_of (starseq #a2 #b f2 f2_lemma s2)) m);
  let v1 : Seq.seq (G.erased b)
    = sel_of (starseq #a1 #b f1 f1_lemma s1) m in
  let v2 : Seq.seq (G.erased b)
    = sel_of (starseq #a2 #b f2 f2_lemma s2) m in
  assert (Seq.length v1 = Seq.length v2);
  let f1' = starl_seq_sel_aux #a1 #b f1 f1_lemma s1 m in
  let f2' = starl_seq_sel_aux #a2 #b f2 f2_lemma s2 m in
  let s1' = SeqUtils.init_nat (Seq.length s1) in
  let s2' = SeqUtils.init_nat (Seq.length s2) in
  assert (v1 == starl_seq_sel #a1 #b f1 f1_lemma s1 m);
  assert (v2 == starl_seq_sel #a2 #b f2 f2_lemma s2 m);
  Seq.map_seq_len f1' s1';
  Seq.map_seq_len f2' s2';
  assert (v1 == Seq.map_seq f1' s1');
  assert (v2 == Seq.map_seq f2' s2');
  Classical.forall_intro (Seq.map_seq_index f1' s1');
  Classical.forall_intro (Seq.map_seq_index f2' s2');
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s1));
  Classical.forall_intro (SeqUtils.init_nat_index (Seq.length s2));
  Seq.lemma_eq_intro v1 v2;
  assert (v1 == v2);
  ()

let starseq_weakening_ref (#opened:_)
  (#a1 #a2 #b: Type0)
  (f1: a1 -> vprop)
  (f2: a2 -> vprop)
  (f1_lemma: (x:a1 -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a2 -> Lemma (t_of (f2 x) == b)))
  (s1: Seq.seq a1)
  (s2: Seq.seq a2)
  : SteelGhost unit opened
  (starseq #a1 #b f1 f1_lemma s1)
  (fun _ -> starseq #a2 #b f2 f2_lemma s2)
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)))
  (ensures fun h0 _ h1 ->
    Seq.length s1 = Seq.length s2 /\
    v_starseq #a1 #b f1 f1_lemma s1 h0
    ==
    v_starseq #a2 #b f2 f2_lemma s2 h1
  )
  =
  change_slprop_rel
    (starseq #a1 #b f1 f1_lemma s1)
    (starseq #a2 #b f2 f2_lemma s2)
    (fun x y -> x == y)
    (fun m -> starseq_weakening_lemma #a1 #a2 #b
      f1 f2
      f1_lemma f2_lemma
      s1 s2
    m)

let starseq_weakening (#opened:_) (#a #b: Type0)
  (f1 f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == b)))
  (s1 s2: Seq.seq a)
  : SteelGhost unit opened
  (starseq #a #b f1 f1_lemma s1)
  (fun _ -> starseq #a #b f2 f2_lemma s2)
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)))
  (ensures fun h0 _ h1 ->
    Seq.length s1 = Seq.length s2 /\
    v_starseq #a #b f1 f1_lemma s1 h0
    ==
    v_starseq #a #b f2 f2_lemma s2 h1
  )
  =
  starseq_weakening_ref #_ #a #a #b f1 f2 f1_lemma f2_lemma s1 s2

let starseq_upd (#opened:_) (#a #b: Type0)
  (f1 f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a{Seq.length s1 = Seq.length s2})
  (n: nat{n < Seq.length s1})
  : SteelGhost unit opened
  (f1 (Seq.index s1 n) `star`
  (starseq #a #b f1 f1_lemma (Seq.slice s1 0 n) `star`
  starseq #a #b f1 f1_lemma (Seq.slice s1 (n+1) (Seq.length s1))))
  (fun _ ->
  f1 (Seq.index s1 n) `star`
  (starseq #a #b f2 f2_lemma (Seq.slice s2 0 n) `star`
  starseq #a #b f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2))))
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k <> n /\ k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)))
  (ensures fun h0 _ h1 ->
    v_starseq #a #b f2 f2_lemma (Seq.slice s2 0 n) h1
    ==
    v_starseq #a #b f1 f1_lemma (Seq.slice s1 0 n) h0
    /\
    v_starseq #a #b f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2)) h1
    ==
    v_starseq #a #b f1 f1_lemma (Seq.slice s1 (n+1) (Seq.length s1)) h0
    /\
    h1 (f1 (Seq.index s1 n))
    ==
    h0 (f1 (Seq.index s1 n))
  )
  =
  starseq_weakening #_ #a #b f1 f2 f1_lemma f2_lemma
    (Seq.slice s1 0 n)
    (Seq.slice s2 0 n);
  starseq_weakening #_ #a #b f1 f2 f1_lemma f2_lemma
    (Seq.slice s1 (n+1) (Seq.length s1))
    (Seq.slice s2 (n+1) (Seq.length s2))

#push-options "--print_implicits"
let starseq_upd2_lemma (#a #b: Type0)
  (f1 f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == option b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == option b)))
  (s1 s2: Seq.seq a)
  (n: nat{n < Seq.length s1})
  (m: SM.mem)
  : Lemma
  (requires
    Seq.length s1 = Seq.length s2 /\
    f2 (Seq.index s2 n) == none_as_emp #b /\
    SM.interp (hp_of (
      (f1 (Seq.index s1 n) `star`
      (starseq #a #(option b) f2 f2_lemma (Seq.slice s2 0 n) `star`
      starseq #a #(option b) f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2))))
    )) m)
  (ensures
    SM.interp (hp_of (
      (f1 (Seq.index s1 n) `star`
      ((f2 (Seq.index s2 n)) `star`
      (starseq #a #(option b) f2 f2_lemma (Seq.slice s2 0 n) `star`
      starseq #a #(option b) f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2)))))
    )) m /\
    sel_of (none_as_emp #b) m == None
  )
  =
  cm_identity (f1 (Seq.index s1 n));
  equiv_sym
    (emp `star` f1 (Seq.index s1 n))
    (f1 (Seq.index s1 n));
  star_commutative emp (f1 (Seq.index s1 n));
  equiv_trans
    (f1 (Seq.index s1 n))
    (emp `star` f1 (Seq.index s1 n))
    (f1 (Seq.index s1 n) `star` emp);
  none_as_emp_equiv #b;
  assert (equiv emp (f2 (Seq.index s2 n)));
  equiv_refl (f1 (Seq.index s1 n));
  star_congruence
    (f1 (Seq.index s1 n)) emp
    (f1 (Seq.index s1 n)) (f2 (Seq.index s2 n));
  equiv_trans
    (f1 (Seq.index s1 n))
    (f1 (Seq.index s1 n) `star` emp)
    (f1 (Seq.index s1 n) `star` f2 (Seq.index s2 n));
  let p_aux =
    (starseq #a #(option b) f2 f2_lemma (Seq.slice s2 0 n) `star`
    starseq #a #(option b) f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s1))) in
  equiv_refl p_aux;
  star_congruence
    (f1 (Seq.index s1 n)) p_aux
    (f1 (Seq.index s1 n) `star` f2 (Seq.index s2 n)) p_aux;
  star_associative
    (f1 (Seq.index s1 n))
    (f2 (Seq.index s2 n))
    p_aux;
  equiv_trans
    (f1 (Seq.index s1 n) `star` p_aux)
    (f1 (Seq.index s1 n) `star` f2 (Seq.index s2 n) `star` p_aux)
    (f1 (Seq.index s1 n) `star` (f2 (Seq.index s2 n) `star` p_aux));
  reveal_equiv
    (f1 (Seq.index s1 n) `star` p_aux)
    (f1 (Seq.index s1 n) `star` (f2 (Seq.index s2 n) `star` p_aux))

let starseq_upd2 (#opened:_) (#a #b: Type0)
  (f1 f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == option b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == option b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a{Seq.length s1 = Seq.length s2})
  (n: nat{n < Seq.length s1})
  : SteelGhost unit opened
  (f1 (Seq.index s1 n) `star`
  (starseq #a #(option b) f1 f1_lemma (Seq.slice s1 0 n) `star`
  starseq #a #(option b) f1 f1_lemma (Seq.slice s1 (n+1) (Seq.length s1))))
  (fun _ ->
  f1 (Seq.index s1 n) `star`
  (f2 (Seq.index s2 n) `star`
  (starseq #a #(option b) f2 f2_lemma (Seq.slice s2 0 n) `star`
  starseq #a #(option b) f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2)))))
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k <> n /\ k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)) /\
    f2 (Seq.index s2 n) == none_as_emp #b)
  (ensures fun h0 _ h1 ->
    v_starseq #a #(option b) f2 f2_lemma (Seq.slice s2 0 n) h1
    ==
    v_starseq #a #(option b) f1 f1_lemma (Seq.slice s1 0 n) h0
    /\
    v_starseq #a #(option b) f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2)) h1
    ==
    v_starseq #a #(option b) f1 f1_lemma (Seq.slice s1 (n+1) (Seq.length s1)) h0
    /\
    h1 (f1 (Seq.index s1 n))
    ==
    h0 (f1 (Seq.index s1 n))
  )
  =
  starseq_upd #_ #a #(option b) f1 f2 f1_lemma f2_lemma s1 s2 n;
  change_slprop_rel
    (f1 (Seq.index s1 n) `star`
     (starseq #a #(option b) f2 f2_lemma (Seq.slice s2 0 n) `star`
     starseq #a #(option b) f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2))))
    (f1 (Seq.index s1 n) `star`
     (f2 (Seq.index s2 n) `star`
     (starseq #a #(option b) f2 f2_lemma (Seq.slice s2 0 n) `star`
     starseq #a #(option b) f2 f2_lemma (Seq.slice s2 (n+1) (Seq.length s2)))))
    (fun (a1, (b1, c1)) (a2, (_, (b2, c2))) ->
      a1 == a2 /\
      b1 == b2 /\
      c1 == c2
    )
    (fun m -> starseq_upd2_lemma #a #b f1 f2 f1_lemma f2_lemma s1 s2 n m);
  ()

#push-options "--z3rlimit 30"
let starseq_upd3 (#opened:_) (#a #b: Type0)
  (f1 f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == option b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == option b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a{Seq.length s1 = Seq.length s2})
  (n: nat{n < Seq.length s1})
  : SteelGhost unit opened
  (starseq #a #(option b) f1 f1_lemma s1)
  (fun _ ->
    f1 (Seq.index s1 n) `star`
    starseq #a #(option b) f2 f2_lemma s2)
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k <> n /\ k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)) /\
    f2 (Seq.index s2 n) == none_as_emp #b)
  (ensures fun h0 _ h1 ->
    v_starseq_len #a #(option b) f1 f1_lemma s1 h0;
    v_starseq_len #a #(option b) f2 f2_lemma s2 h1;
    let v0 = v_starseq #a #(option b) f1 f1_lemma s1 h0 in
    let v1 = v_starseq #a #(option b) f2 f2_lemma s2 h1 in
    v1 == Seq.upd v0 n None
  )
  =
  let h0 = get () in
  let vs0 = v_starseq #a #(option b) f1 f1_lemma s1 h0 in
  starseq_unpack_s #_ #a #(option b) f1 f1_lemma s1 n;
  starseq_upd2 #_ #a #b f1 f2 f1_lemma f2_lemma s1 s2 n;
  let v1 = gget (f2 (Seq.index s2 n)) in
  starseq_pack_s #_ #a #(option b) f2 f2_lemma s2 n;
  let h2 = get () in
  let vs2 = v_starseq #a #(option b) f2 f2_lemma s2 h2 in
  let v2 = Seq.index vs2 n in
  assert (v2 == v1);
  assert (None? v2);
  let vs3 = Seq.upd vs0 n None in
  assert (Seq.length vs2 = Seq.length vs3);
  assert (Seq.slice vs2 0 n == Seq.slice vs3 0 n);
  assert (Seq.slice vs2 (n+1) (Seq.length s1) == Seq.slice vs3 (n+1) (Seq.length s1));
  Classical.forall_intro (Classical.move_requires (
    SeqUtils.lemma_slice_index vs2 vs3 0 n));
  Classical.forall_intro (Classical.move_requires (
    SeqUtils.lemma_slice_index vs2 vs3 (n+1) (Seq.length s1)));
  assert (forall (x:nat{x < Seq.length s1}).
    Seq.index vs2 x == Seq.index vs3 x);
  Seq.lemma_eq_intro vs2 vs3;
  ()
#pop-options

// [ok] starseq_unpack (pure equiv)
//   [ok] aux lemma
// [ok] starseq_pack (pure equiv, equiv_sym of starseq_unpack)
// [ok] starseq_unpack_lemma (pure on SM.mem)
//   [ok] aux lemma
// [ok] starseq_pack_lemma (pure on SM.mem)
// [ok] starseq_unpack (Steel)
// [ok] starseq_pack (Steel)
// [ok] starseq_idem (Steel)
// [sk?] remove refined type n:nat{n < Seq.length s} and add req/ens again
// [ok?] reduce as much as possible # of assert_norm calls
// [ok?] simplify code (remove old tricky casts for f with refinement)
