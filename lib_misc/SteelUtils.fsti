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

let starl_seq (s: Seq.seq vprop)
  : vprop
  =
  starl (Seq.seq_to_list s)


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
  : selector (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))

[@@ __steel_reduce__]
let starseq' (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  : vprop'
  = {
    hp = hp_of (starl_seq (Seq.map_seq f s));
    t = Seq.seq (G.erased b);
    sel = starl_seq_sel f f_lemma s;
  }
unfold
let starseq (#a #b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  = VUnit (starseq' #a #b f f_lemma s)

[@@ __steel_reduce__]
let v_starseq (#a #b: Type)
  (#p: vprop)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (starseq #a #b f f_lemma s) /\ True)})
  = h (starseq #a #b f f_lemma s)

val starseq_unpack_s (#a #b: Type0)
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
    let v = v_starseq #a #b f f_lemma s h0 in
    Seq.length v = Seq.length s /\
    h1 (f (Seq.index s n)) == G.reveal (Seq.index v n) /\
    v_starseq #a #b f f_lemma (Seq.slice s 0 n) h1
      == Seq.slice v 0 n /\
    v_starseq #a #b f f_lemma (Seq.slice s (n+1) (Seq.length s)) h1
      == Seq.slice v (n+1) (Seq.length s)
  )

val starseq_pack_s (#a #b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: Seq.seq a)
  (n: nat{n < Seq.length s})
  : Steel unit
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
