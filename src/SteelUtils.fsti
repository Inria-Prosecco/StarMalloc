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

val starl_seq_unpack (s: Seq.seq vprop) (n: nat)
  : Lemma
  (requires n < Seq.length s)
  (ensures
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

val starl_seq_sel (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  : selector (Seq.seq (G.erased b)) (hp_of (starl_seq (Seq.map_seq f s)))

[@@ __steel_reduce__]
let starseq' (#a #b: Type)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  : vprop'
  = {
    hp = hp_of (starl_seq (Seq.map_seq f s));
    t = Seq.seq (G.erased b);
    sel = starl_seq_sel f s;
  }
unfold
let starseq (#a #b: Type)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  = VUnit (starseq' #a #b f s)

[@@ __steel_reduce__]
let v_starseq (#a #b: Type)
  (#p: vprop)
  (f: a -> (vp:vprop{t_of vp == b}))
  (s: Seq.seq a)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (starseq #a #b f s) /\ True)})
  = h (starseq #a #b f s)

// TODO: pack/unpack
// TODO: starl_seq_sel without f/map?
// TODO: wrapper around v_stars for selector over starl and not only starl_seq?
