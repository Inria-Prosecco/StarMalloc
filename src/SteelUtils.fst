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
  : selector' (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))
  =
  Seq.map_seq_len f s;
  fun (h:hmem (starl_seq (Seq.map_seq f s))) ->
    let f' = fun k -> starl_seq_sel_aux #a #b f f_lemma s h k in
    let s' = SeqUtils.init_nat (Seq.length s) in
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
  let f1 = fun k -> starl_seq_sel_aux #a #b f f_lemma s m0 k in
  let f2 = fun k -> starl_seq_sel_aux #a #b f f_lemma s m' k in
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
  let f1 = fun k -> starl_seq_sel_aux #a #b f f_lemma s m0 k in
  let f2 = fun k -> starl_seq_sel_aux #a #b f f_lemma s m' k in
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
  : selector (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))
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
    Seq.length (starl_seq_sel' #a #b f f_lemma s m) = Seq.length s
  )
  =
  Seq.map_seq_len f s;
  let f' = fun k -> starl_seq_sel_aux #a #b f f_lemma  s m k in
  let s' = SeqUtils.init_nat (Seq.length s) in
  SeqUtils.init_nat_len (Seq.length s);
  assert (Seq.length s' = Seq.length s);
  Seq.map_seq_len f' s'

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
  let f' = fun k -> starl_seq_sel_aux #a #b f f_lemma s m k in
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
  let f' = fun k -> starl_seq_sel_aux #a #b f f_lemma s m k in
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
  let f' = fun (k:nat{k < Seq.length s}) -> starl_seq_sel_aux #a #b f f_lemma s m k in
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
  // 2 weakenings are likely required
  assume (r1 == r2)

let starseq_unpack_lemma (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  //(v: Seq.seq (G.erased b))
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m /\
    //sel_of (starseq #a #b f f_lemma s) m == v
    True
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
  starseq_sel_len #a #b f f_lemma s m;
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
  (requires (
    SM.interp (hp_of (
      f (Seq.index s n) `star`
      (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
      starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))
    )) m /\
    True
    //Seq.length v == Seq.length s /\
    //sel_of (f (Seq.index s n)) m
    //  == G.reveal (Seq.index v n) /\
    //sel_of (starseq #a #b f f_lemma (Seq.slice s 0 n)) m
    //  == Seq.slice v 0 n /\
    //sel_of (starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) m
    //  == Seq.slice v (n+1) (Seq.length s)
  ))
  (ensures
    SM.interp (hp_of (starseq #a #b f f_lemma s)) m /\
    True
    //sel_of (starseq #a #b f f_lemma s) m == v
  )
  =
  let p1 = starseq #a #b f f_lemma  s in
  let p2 =
    f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))) in
  starseq_pack #a #b f f_lemma s n;
  reveal_equiv p2 p1;
  ()

let starseq_unpack_s (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : Steel unit
  (starseq #a #b f f_lemma s)
  (fun _ ->
    f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)))
  )
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    f_lemma (Seq.index s n);
    let v = G.reveal (v_starseq #a #b f f_lemma s h0) in
    Seq.length v = Seq.length s /\
    //TODO: FIXME
    //starseq #a #b f f_lemma s `can_be_split` f (Seq.index s n) /\
    //(normalize_term (sel_of (f (Seq.index s n)))) h1
    //  == Seq.index v n /\
    v_starseq #a #b f f_lemma (Seq.slice s 0 n) h1
      == Seq.slice v 0 n /\
    v_starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) h1
      == Seq.slice v (n+1) (Seq.length s)
  )
  =
  let h0 = get () in
  let v = G.hide (v_starseq #a #b f f_lemma s h0) in
  change_slprop_rel
    (starseq #a #b f f_lemma s)
    (f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
    (fun v (x, (y, z)) ->
      Seq.length (G.reveal v) = Seq.length s /\
      y == Seq.slice v 0 n /\
      z == Seq.slice v (n+1) (Seq.length s)
    )
    (fun m -> starseq_unpack_lemma #a #b f f_lemma s n m);
  return ()

let starseq_pack_s (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : SteelT unit
  (f (Seq.index s n) `star`
  (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
  starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
  (fun _ ->
    starseq #a #b f f_lemma s
  )
  //(requires fun _ -> True)
  //(ensures fun h0 _ h1 ->
  //  f_lemma (Seq.index s n);
  //  let v = G.reveal (v_starseq #a #b f f_lemma s h0) in
  //  Seq.length v = Seq.length s /\
  //  //TODO: FIXME
  //  //starseq #a #b f f_lemma s `can_be_split` f (Seq.index s n) /\
  //  //(normalize_term (sel_of (f (Seq.index s n)))) h1
  //  //  == Seq.index v n /\
  //  v_starseq #a #b f f_lemma (Seq.slice s 0 n) h1
  //    == Seq.slice v 0 n /\
  //  v_starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) h1
  //    == Seq.slice v (n+1) (Seq.length s)
  //)
  =
  rewrite_slprop
    (f (Seq.index s n) `star`
    (starseq #a #b f f_lemma (Seq.slice s 0 n) `star`
    starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s))))
    (starseq #a #b f f_lemma s)
    (fun m -> starseq_pack_lemma #a #b f f_lemma s n m);
  return ()

// TODO
// [ok] starseq_unpack (pure equiv)
//   [ok] aux lemma
// [ok] starseq_pack (pure equiv, equiv_sym of starseq_unpack)
// [ok] starseq_unpack_lemma (pure on SM.mem)
//   [on] aux lemma (1 remaining)
// [on] starseq_pack_lemma (pure on SM.mem)
// [idle] starseq_unpack (Steel) (waiting for fix)
// [on] starseq_pack (Steel)
// remove refined type n:nat{n < Seq.length s} and add req/ens again
// simplify code (remove old tricky casts for f with refinement)
