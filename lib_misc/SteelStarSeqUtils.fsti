module SteelStarSeqUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory
module L = FStar.List.Tot
module G = FStar.Ghost
open SteelOptUtils

val starl (l: list vprop)
  : vprop

val starl_seq (s: Seq.seq vprop)
  : vprop

val starl_append (l1 l2: list vprop)
  : Lemma
  (starl (L.append l1 l2) `equiv` (starl l1 `star` starl l2))

val starl_seq_append (s1 s2: Seq.seq vprop)
  : Lemma
  (starl_seq (Seq.append s1 s2) `equiv` (starl_seq s1 `star` starl_seq s2))

val starl_seq_unpack (s: Seq.seq vprop) (n: nat{n < Seq.length s})
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

val starl_seq_pack (s: Seq.seq vprop) (n: nat)
  : Lemma
  (requires n < Seq.length s)
  (ensures
    (Seq.index s n `star`
      (starl_seq (Seq.slice s 0 n) `star`
       starl_seq (Seq.slice s (n+1) (Seq.length s))))
    `equiv`
    starl_seq s
  )

val starl_seq_imp (s: Seq.seq vprop) (k: nat)
  : Lemma
  (requires k < Seq.length s)
  (ensures
    starl_seq s
    `can_be_split`
    Seq.index s k
  )

val starl_seq_map_imp (#a #b: Type0)
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

val starl_seq_sel (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : selector (Seq.lseq (G.erased b) (Seq.length s)) (hp_of (starl_seq (Seq.map_seq f s)))

[@@ __steel_reduce__]
let starseq' (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : vprop'
  = {
    hp = hp_of (starl_seq (Seq.map_seq f s));
    t = Seq.lseq (G.erased b) (Seq.length s);
    sel = starl_seq_sel f f_lemma s;
  }
unfold
let starseq (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  = VUnit (starseq' #a #b f f_lemma s)

val starseq_empty_equiv_emp (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : Lemma
  (requires Seq.length s == 0)
  (ensures hp_of (starseq #a #b f f_lemma s) == hp_of emp)

val starseq_singleton_equiv (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : Lemma
  (requires Seq.length s == 1)
  (ensures hp_of (starseq #a #b f f_lemma s) == hp_of (f (Seq.index s 0) `star` emp))

[@@ __steel_reduce__]
let v_starseq (#a #b: Type)
  (#p: vprop)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (starseq #a #b f f_lemma s) /\ True)})
  : GTot (Seq.lseq (G.erased b) (Seq.length s))
  = h (starseq #a #b f f_lemma s)

let v_starseq_len (#a #b: Type)
  (#p: vprop)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (starseq #a #b f f_lemma s) /\ True)})
  : Lemma
  (Seq.length (v_starseq #a #b f f_lemma s h) = Seq.length s)
  =
  ()

val starseq_unpack_s (#opened:_) (#a #b: Type0)
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

val starseq_pack_s (#opened:_) (#a #b: Type0)
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

val starseq_weakening_rel_some (#opened:_)
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

val starseq_weakening_ref (#opened:_)
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

val starseq_weakening (#opened:_) (#a #b: Type0)
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

val starseq_upd (#opened:_) (#a #b: Type0)
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

val starseq_upd_pack (#opened:_) (#a #b: Type0)
  (f1 f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a{Seq.length s1 = Seq.length s2})
  (n: nat{n < Seq.length s1})
  : SteelGhost unit opened
  (f2 (Seq.index s2 n) `star`
  (starseq #a #b f1 f1_lemma (Seq.slice s1 0 n) `star`
  starseq #a #b f1 f1_lemma (Seq.slice s1 (n+1) (Seq.length s1))))
  (fun _ -> starseq #a #b f2 f2_lemma s2)
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k <> n /\ k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)))
  (ensures fun h0 _ h1 ->
    f2_lemma (Seq.index s2 n);
    let v = v_starseq #a #b f2 f2_lemma s2 h1 in
    Seq.length v = Seq.length s1 /\
    h0 (f2 (Seq.index s2 n)) == G.reveal (Seq.index v n) /\
    v_starseq #a #b f1 f1_lemma (Seq.slice s1 0 n) h0
      == Seq.slice v 0 n /\
    v_starseq #a #b f1 f1_lemma (Seq.slice s1 (n+1) (Seq.length s1)) h0
      == Seq.slice v (n+1) (Seq.length s1)
  )



val starseq_upd2 (#opened:_) (#a #b: Type0)
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
  ((f2 (Seq.index s2 n)) `star`
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

val starseq_upd3 (#opened:_) (#a #b: Type0)
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

let starseq_upd4 (#opened:_) (#a #b: Type0)
  (f1 f2: a -> vprop)
  (f1_lemma: (x:a -> Lemma (t_of (f1 x) == option b)))
  (f2_lemma: (x:a -> Lemma (t_of (f2 x) == option b)))
  (s1: Seq.seq a)
  (s2: Seq.seq a{Seq.length s1 = Seq.length s2})
  (n: nat{n < Seq.length s1})
  : SteelGhost unit opened
  (f2 (Seq.index s2 n) `star`
    starseq #a #(option b) f1 f1_lemma s1)
  (fun _ ->
    starseq #a #(option b) f2 f2_lemma s2)
  (requires fun _ ->
    Seq.length s1 = Seq.length s2 /\
    (forall (k:nat{k <> n /\ k < Seq.length s1}).
      f1 (Seq.index s1 k) == f2 (Seq.index s2 k)) /\
    f1 (Seq.index s1 n) == none_as_emp #b)
  (ensures fun h0 _ h1 ->
    f2_lemma (Seq.index s2 n);
    v_starseq_len #a #(option b) f1 f1_lemma s1 h0;
    v_starseq_len #a #(option b) f2 f2_lemma s2 h1;
    let v0 = v_starseq #a #(option b) f1 f1_lemma s1 h0 in
    let v1 = v_starseq #a #(option b) f2 f2_lemma s2 h1 in
    let x : normal (t_of (f2 (Seq.index s2 n))) = h0 (f2 (Seq.index s2 n)) in
    v1 == Seq.upd v0 n x
  )
  = sladmit ()
