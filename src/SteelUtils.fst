module SteelUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory
module L = FStar.List.Tot


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


let starl (l: list vprop)
  : vprop
  =
  L.fold_right star l emp

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