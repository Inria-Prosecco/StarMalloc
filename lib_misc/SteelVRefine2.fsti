module SteelVRefine2

open Steel.Effect.Atomic
open Steel.Effect

module Mem = Steel.Memory
open Steel.Memory

(*** Vprop combinators ***)

(* Refining a vprop with a selector predicate *)

/// Separation logic predicate stating the validity of a vprop with an additional refinement on its selector
val vrefine_hp (v: vprop) (p: (normal (t_of v) -> Tot prop)) : Tot (slprop u#1)

/// Exposing the validity of the above predicate when needed for proof purposes
val interp_vrefine_hp (v: vprop) (p: (normal (t_of v) -> Tot prop)) (m: mem) : Lemma
  (interp (vrefine_hp v p) m <==> (interp (hp_of v) m /\ p (sel_of v m)))

/// Selector of a refined vprop. Returns a value which satisfies the refinement predicate
val vrefine_sel (v: vprop) (p: (normal (t_of v) -> Tot prop)) : Tot (selector (vrefine_t v p) (vrefine_hp v p))

/// Exposing the definition of the refined selector
val vrefine_sel_eq (v: vprop) (p: (normal (t_of v) -> Tot prop)) (m: Mem.hmem (vrefine_hp v p)) : Lemma
  (
    interp (hp_of v) m /\
    vrefine_sel v p m == sel_of v m
  )
//  [SMTPat ((vrefine_sel v p) m)] // FIXME: this pattern causes Z3 "wrong number of argument" errors

/// Combining the above pieces to define a vprop refined by a selector prediacte
[@__steel_reduce__]
let vrefine' (v: vprop) (p: (normal (t_of v) -> Tot prop)) : Tot vprop' = {
  hp = vrefine_hp v p;
  t = t_of v;
  sel = vrefine_sel v p;
}

[@__steel_reduce__]
let vrefine (v: vprop) (p: (normal (t_of v) -> Tot prop)) = VUnit (vrefine' v p)
(* Introduction and elimination principles for vprop combinators *)

/// If predicate [p] iniitally holds for the selector of vprop [v],
/// then we can refine [v] with [p]
val intro_vrefine (#opened:inames)
  (v: vprop) (p: (normal (t_of v) -> Tot prop))
: SteelGhost unit opened v (fun _ -> vrefine v p)
  (requires fun h -> p (h v))
  (ensures fun h _ h' -> h' (vrefine v p) == h v)

/// We can transform back vprop [v] refined with predicate [p] to the underlying [v],
/// where [p] holds on the selector of [v]
val elim_vrefine (#opened:inames)
  (v: vprop) (p: (normal (t_of v) -> Tot prop))
: SteelGhost unit opened (vrefine v p) (fun _ -> v)
  (requires fun _ -> True)
  (ensures fun h _ h' -> h' v == h (vrefine v p) /\ p (h' v))
