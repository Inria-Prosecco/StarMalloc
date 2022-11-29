module SteelUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory
module L = FStar.List.Tot
module G = FStar.Ghost

let starl (l: list vprop)
  : vprop
  =
  L.fold_right star l emp


let rec partition_equiv_filter (#a: Type) (f: a -> Tot bool) (l: list a)
  : Lemma
  (L.partition f l == (L.filter f l, L.filter (fun x -> not (f x)) l))
  = match l with
  | [] -> ()
  | hd::tl -> partition_equiv_filter f tl

let rec count_equiv_filter (#a: eqtype) (l: list a) (x: a)
  : Lemma
  (ensures L.count x l = L.length (L.filter (fun y -> y = x) l))
  (decreases l)
  = match l with
  | [] -> ()
  | hd::tl -> count_equiv_filter tl x

let rec filter_equiv (#a: Type) (l: list a) (f1 f2: a -> Tot bool)
  : Lemma
  (requires forall x. f1 x = f2 x)
  (ensures L.filter f1 l == L.filter f2 l)
  (decreases l)
  = match l with
  | [] -> ()
  | hd::tl -> filter_equiv tl f1 f2


let filter_lemma (#a: eqtype) (l: list a) (x: a)
  : Lemma
  (requires L.count x l == 1)
  (ensures ([x], L.filter (fun y -> y <> x) l) == L.partition (fun y -> y = x) l)
  =
  let f = fun y -> y = x in
  let r = L.partition f l in
  partition_equiv_filter f l;
  L.partition_count f l x;
  assert (L.count x l == L.count x (fst r) + L.count x (snd r));
  assert (1 == L.count x (fst r) + L.count x (snd r));
  assert (L.count x (fst r) = 1 || L.count x (snd r) = 1);
  if (L.count x (snd r) = 1) then (
    L.mem_count (snd r) x;
    L.mem_memP x (snd r);
    assert (L.memP x (snd r));
    L.mem_filter (fun x -> not (f x)) (snd r) x;
    assert (not (f x));
    assert (f x)
  );
  assert (L.count x (fst r) = 1);
  count_equiv_filter l x;
  assert (L.length (fst r) = 1);
  L.mem_count (fst r) x;
  assert (L.mem x (fst r));
  assert (fst r = [x]);
  filter_equiv l (fun y -> not (y = x)) (fun y -> y <> x)


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



let starl_singleton (#a: Type) (f: a -> Tot vprop) (l: list a)
  : Lemma
  (requires L.length l == 1)
  (ensures starl (L.map f l) `equiv` f (L.hd l))
  =
  assert (l == [L.hd l]);
  assert (L.map f l == [f (L.hd l)]);
  let p1 = starl (L.map f l) in
  let p3 = f (L.hd l) in
  let p2 = p3 `star` emp in
  assert (starl [f (L.hd l)] == f (L.hd l) `star` emp);
  equiv_refl p1;
  assert (p1 `equiv` p2);
  cm_identity p3;
  assert ((emp `star` p3) `equiv` p3);
  star_commutative emp p3;
  assert ((emp `star` p3) `equiv` p2);
  equiv_sym (emp `star` p3) p2;
  equiv_trans
    p2
    (emp `star` p3)
    p3;
  assert (p2 `equiv` p3);
  equiv_trans p1 p2 p3

let starl_append_hd_map (#a: Type) (f: a -> vprop) (l: list a) (x: a)
  : Lemma
  (starl (L.map f (x::l)) `equiv` (f x `star` starl (L.map f l)))
  =
  let p0 = starl (L.map f (x::l)) in
  let p1 = starl (L.map f l) in
  L.map_append f [x] l;
  assert (L.map f (x::l) == L.append (L.map f [x]) (L.map f l));
  starl_append (L.map f [x]) (L.map f l);
  assert (p0 `equiv` (starl (L.map f [x]) `star` p1));
  starl_singleton f [x];
  assert (starl (L.map f [x]) `equiv` f x);
  equiv_refl p1;
  star_congruence
    (starl (L.map f [x])) p1
    (f x) p1;
  equiv_trans
    p0
    (starl (L.map f [x]) `star` p1)
    (f x `star` p1)

let starl_seq (s: Seq.seq vprop)
  : vprop
  =
  L.fold_right star (Seq.seq_to_list s) emp

let starl_seq_append (s1 s2: Seq.seq vprop)
  : Lemma
  (starl_seq (Seq.append s1 s2) `equiv` (starl_seq s1 `star` starl_seq s2))
  =
  let l1 = Seq.seq_to_list s1 in
  let l2 = Seq.seq_to_list s2 in
  Utils.lemma_seq_to_list_append s1 s2;
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

let starl_seq_imp2 (#a #b: Type)
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

let starl_seq_sel_aux (#a #b: Type)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  (h: hmem (starl_seq (Seq.map_seq f s)))
  (k: nat{k < Seq.length (Seq.map_seq f s)})
  : G.erased b
  =
  Seq.map_seq_len f s;
  let v = Seq.index s k in
  starl_seq_imp2 #a #b #(Seq.length s) f s k;
  assert (starl_seq (Seq.map_seq f s) `can_be_split` (f (Seq.index s k)));
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) h;
  let s : selector b (hp_of (f (Seq.index s k))) = sel_of (f v) in
  G.hide (s h)

let starl_seq_sel' (#a #b: Type)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  : selector' (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))
  =
  Seq.map_seq_len f s;
  fun (h:hmem (starl_seq (Seq.map_seq f s))) ->
    Seq.map_seq
      (fun (k:nat{k < Seq.length (Seq.map_seq f s)}) ->
        starl_seq_sel_aux f s h k)
      (SeqUtils.init_nat (Seq.length s))

let starl_seq_sel_depends_only_on_aux (#a #b: Type)
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
  starl_seq_imp2 #a #b #(Seq.length s) f s k;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m0;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m'

let starl_seq_sel_depends_only_on_core_aux (#a #b: Type)
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
  starl_seq_imp2 #a #b #(Seq.length s) f s k;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) m0;
  can_be_split_interp
    (starl_seq (Seq.map_seq f s))
    (f (Seq.index s k)) (SM.core_mem m0)

let starl_seq_sel_depends_only_on (#a #b: Type)
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
    starl_seq_sel_depends_only_on_aux #a #b f s m0 m1
  );
  Seq.lemma_eq_intro #(G.erased b) s1 s2

let starl_seq_sel_depends_only_on_core (#a #b: Type)
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

let starl_seq_sel (#a #b: Type)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  : selector (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))
  =
  Seq.map_seq_len f s;
  Classical.forall_intro_2 (starl_seq_sel_depends_only_on #a #b f s);
  Classical.forall_intro (starl_seq_sel_depends_only_on_core #a #b f s);
  starl_seq_sel' f s

//let starl_seq_sel (#a: Type)
//  //(s: Seq.seq vprop)
//  (s: Seq.seq (vp:vprop{t_of vp == a}))
//  : selector' (Seq.seq (G.erased a)) (hp_of (starl_seq (s <: Seq.seq vprop)))
//  =
//  fun (h:hmem (starl_seq s)) ->
//    Seq.map_seq
//      (fun k ->
//        let v = Seq.index s k in
//        starl_seq_imp s k;
//        assert (starl_seq s `can_be_split` (Seq.index s k));
//        //admit ();
//        //let h' = focus_rmem h (hp_of (Seq.index s k)) in
//        assume (t_of v == a);
//        let sel : selector a (hp_of (Seq.index s k)) = sel_of v in
//        can_be_split_interp (starl_seq s) (Seq.index s k) h;
//        let r : a = sel h in
//        G.hide r)
//      (SeqUtils.init_nat (Seq.length s))

(*)
let rec starl_filter (#a: Type) (g: a -> bool) (f: a -> vprop) (l: list a)
  : Lemma
  (ensures (let l1, l2 = L.partition g l in
  starl (L.map f l) `equiv` (starl (L.map f l1) `star` starl (L.map f l2))))
  (decreases l)
  =
  // arbitrary permutation do not change validity of vprop
  // no need for permutation, induction should be ok
  match l with
  | [] ->
      let l1, l2 = L.partition g l in
      assert (L.map f l == []);
      L.partition_length g l;
      assert (L.map f l1 == []);
      assert (L.map f l2 == []);
      cm_identity emp;
      equiv_sym (emp `star` emp) emp

  | hd::tl ->
      let l1, l2 = L.partition g tl in
      starl_filter g f tl;
      let p0 = starl (L.map f l) in
      let p1 = starl (L.map f tl) in
      let p2 = starl (L.map f l1) in
      let p3 = starl (L.map f l2) in
      assert (p1 `equiv` (p2 `star` p3));
      starl_append_hd_map f tl hd;
      assert (p0 `equiv` (f hd `star` p1));
      equiv_refl (f hd);
      star_congruence
        (f hd) p1
        (f hd) (p2 `star` p3);
      assert ((f hd `star` p1) `equiv` (f hd `star` (p2 `star` p3)));
      if g hd then (
        star_associative (f hd) p2 p3;
        equiv_sym
          ((f hd `star` p2) `star` p3)
          (f hd `star` (p2 `star` p3));
        equiv_trans
          (f hd `star` p1)
          (f hd `star` (p2 `star` p3))
          ((f hd `star` p2) `star` p3);
        assert ((f hd `star` p1) `equiv` ((f hd `star` p2) `star` p3));
        let p2' = starl (L.map f (hd::l1)) in
        assert (hd::l1 == fst (L.partition g l));
        starl_append_hd_map f l1 hd;
        equiv_sym p2' (f hd `star` p2);
        assert ((f hd `star` p2) `equiv` p2');
        equiv_refl p3;
        star_congruence
          (f hd `star` p2) p3
          p2' p3;
        equiv_trans
          p0
          (f hd `star` (p2 `star` p3))
          (p2' `star` p3)
      ) else (
        star_commutative (f hd) (p2 `star` p3);
        equiv_trans
          (f hd `star` p1)
          (f hd `star` (p2 `star` p3))
          ((p2 `star` p3) `star` f hd);
        star_associative p2 p3 (f hd);
        equiv_refl p2;
        star_commutative p3 (f hd);
        star_congruence
          p2 (p3 `star` f hd)
          p2 (f hd `star` p3);
        equiv_trans
          (f hd `star` p1)
          ((p2 `star` p3) `star` f hd)
          (p2 `star` (p3 `star` f hd));
        equiv_trans
          (f hd `star` p1)
          (p2 `star` (p3 `star` f hd))
          (p2 `star` (f hd `star` p3));
        assert ((f hd `star` p1) `equiv` (p2 `star` (f hd `star` p3)));
        let p3' = starl (L.map f (hd::l2)) in
        assert (hd::l2 == snd (L.partition g l));
        starl_append_hd_map f l2 hd;
        equiv_sym p3' (f hd `star` p3);
        assert ((f hd `star` p3) `equiv` p3');
        equiv_refl p2;
        star_congruence
          p2 (f hd `star` p3)
          p2 p3';
        equiv_trans
          p0
          (f hd `star` p1)
          (p2 `star` p3')
      )

let starl_partition_equiv (#a: eqtype)
  (f: a -> Tot vprop)
  (l: list a)
  (x: a)
  : Lemma
  (requires L.count x l == 1)
  (ensures
    starl (L.map f l)
    `equiv`
    (f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l))))
  =
  L.mem_count l x;
  filter_lemma l x;
  starl_filter (fun y -> y = x) f l;
  let p1 = starl (L.map f l) in
  let p21 = starl (L.map f [x]) in
  let p22 = starl (L.map f (L.filter (fun y -> y <> x) l)) in
  let p31 = f x in
  let p2 = p21 `star` p22 in
  let p3 = p31 `star` p22 in
  assert (p1 `equiv` p2);
  assert_norm (L.length [x] == 1);
  starl_singleton f [x];
  equiv_refl p22;
  star_congruence
    p21 p22
    p31 p22;
  assert (p2 `equiv` p3);
  equiv_trans p1 p2 p3;
  assert (p1 `equiv` p3)

let starl_partition_unpack (#a: eqtype)
  (f: a -> Tot vprop)
  (l: list a)
  (x: a)
  (m: SM.mem)
  : Lemma
  (requires L.count x l == 1 /\
  SM.interp (hp_of (
    starl (L.map f l)
  )) m)
  (ensures SM.interp (hp_of (
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l))
  )) m)
  =
  let p1 = starl (L.map f l) in
  let p2 =
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l)) in
  starl_partition_equiv f l x;
  reveal_equiv p1 p2;
  SM.reveal_equiv (hp_of p1) (hp_of p2)

let starl_partition_pack (#a: eqtype)
  (f: a -> Tot vprop)
  (l: list a)
  (x: a)
  (m: SM.mem)
  : Lemma
  (requires L.count x l == 1 /\
  SM.interp (hp_of (
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l))
  )) m)
  (ensures SM.interp (hp_of (
    starl (L.map f l)
  )) m)
  =
  let p1 = starl (L.map f l) in
  let p2 =
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l)) in
  starl_partition_equiv f l x;
  equiv_sym p1 p2;
  reveal_equiv p2 p1;
  SM.reveal_equiv (hp_of p2) (hp_of p1)

#push-options "--print_implicits --print_universes"

let starl_sl (l: list SM.slprop)
  : SM.slprop u#1
  =
  L.fold_right SM.star l SM.emp

//let rec norm_lemma
//  (#a: Type)
//  (f: a -> vprop)
//  (l: list a)
//  : Lemma
//  (hp_of (starl (L.map f l))
//  ==
//  starl_sl (L.map (fun y -> hp_of (f y)) l))
//  = match l with
//  | [] -> admit ()
//  | _ -> admit ()

let starl_sel'
  (#a #b: Type0)
  (f: a -> (p:vprop{t_of p == b}))
  (l: list a)
  : selector' (list b) (hp_of (starl (L.map f l)))
  =
  fun h ->
    assert (SM.interp (hp_of (starl (L.map f l))) h);
    let r = L.map_gtot
      (fun (y: a) ->
        assume (SM.interp (hp_of (f y)) h);
        let v : b = sel_of (f y) h in v)
      l
    in
    G.reveal r

let starl_sel_depends_only_on (#a #b: Type0)
  (f: a -> (p:vprop{t_of p == b}))
  (l: list a)
  (m0: SM.hmem (hp_of (starl (L.map f l))))
  (m1: SM.mem{SM.disjoint m0 m1})
  : Lemma
  (starl_sel' #a #b f l m0 == starl_sel' #a #b f l (SM.join m0 m1))
  =
  let m' = SM.join m0 m1 in
  admit ();
  ()

let starl_sel_depends_only_on_core (#a #b: Type0)
  (f: a -> (p:vprop{t_of p == b}))
  (l: list a)
  (m0: SM.hmem (hp_of (starl (L.map f l))))
  : Lemma
  (starl_sel' #a #b f l m0 == starl_sel' #a #b f l (SM.core_mem m0))
  =
  admit ();
  ()

let starl_sel
  (#a #b: Type0)
  (f: a -> (p:vprop{t_of p == b}))
  (l: list a)
  : selector (list b) (hp_of (starl (L.map f l)))
  =
  Classical.forall_intro_2 (starl_sel_depends_only_on #a #b f l);
  Classical.forall_intro (starl_sel_depends_only_on_core #a #b f l);
  starl_sel' f l


[@@ __steel_reduce__]
let starl'_v
  (#a #b: Type)
  (f: a -> (p:vprop{t_of p == b}))
  (l: list a)
  : vprop'
  =
  {
    hp = hp_of (starl (L.map f l));
    t = list b;
    sel = fun h -> starl_sel f l h
  }
unfold
let starl_v
  (#a #b: Type)
  (f: a -> (p:vprop{t_of p == b}))
  (l: list a)
  = VUnit (starl'_v #a #b f l)
