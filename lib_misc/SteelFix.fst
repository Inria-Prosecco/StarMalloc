module SteelFix

open Steel.Effect.Atomic
open Steel.Effect
module Mem = Steel.Memory

let change_slprop_rel_with_cond (#opened:Mem.inames)
  (p q:vprop)
  (cond: normal (t_of p) -> prop)
  (rel : normal (t_of p) -> normal (t_of q) -> prop)
  (l:(m:Mem.mem) -> Lemma
    (requires Mem.interp (hp_of p) m /\ cond (sel_of p m))
    (ensures Mem.interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  )
  : SteelGhost unit opened
  p
  (fun _ -> q)
  (fun h0 -> cond (h0 p))
  (fun h0 _ h1 -> rel (h0 p) (h1 q))
  =
  change_slprop_rel_with_cond #opened p q cond rel l
