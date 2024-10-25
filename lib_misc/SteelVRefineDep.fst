module SteelVRefineDep

open Steel.Effect.Atomic
open Steel.Effect

module SM = Steel.Memory
module G = FStar.Ghost

let vrefine_f
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  (x: normal (t_of (vrefine v p)))
  = f x

let vrefinedep_aux
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : vprop
  = vdep (vrefine v p) (vrefine_f v p f)

let vrefinedep_hp
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  : Tot (SM.slprop u#1)
  = hp_of (vrefinedep_aux v p f)

let vrefinedep_sel
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  : Tot (selector (vrefinedep_t v p f) (vrefinedep_hp v p f))
  = sel_of (vrefinedep_aux v p f)

let vrefinedep_lemma
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  (m:SM.mem) : Lemma
  (requires SM.interp (hp_of (vrefinedep v p f)) m)
  (ensures
    SM.interp (hp_of (vdep (vrefine v p) (vrefine_f v p f))) m /\
    dfst (sel_of (vrefinedep v p f) m) == dfst (sel_of (vdep (vrefine v p) (vrefine_f v p f)) m) /\
    dsnd (sel_of (vrefinedep v p f) m) == dsnd (sel_of (vdep (vrefine v p) (vrefine_f v p f)) m) )
  = ()

let vrefinedep_lemma2
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  (m:SM.mem) : Lemma
  (requires SM.interp (hp_of (vdep (vrefine v p) (vrefine_f v p f))) m)
  (ensures
    SM.interp (hp_of (vrefinedep v p f)) m /\
    dfst (sel_of (vrefinedep v p f) m) == dfst (sel_of (vdep (vrefine v p) (vrefine_f v p f)) m) /\
    dsnd (sel_of (vrefinedep v p f) m) == dsnd (sel_of (vdep (vrefine v p) (vrefine_f v p f)) m) )
  = ()

#push-options "--compat_pre_typed_indexed_effects"
let elim_vrefinedep
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  =
    change_slprop_rel (vrefinedep v p f) (vdep (vrefine v p) (vrefine_f v p f))
      (fun x y -> dfst x == dfst y /\ dsnd x == dsnd y)
      (vrefinedep_lemma v p f);
    let x = elim_vdep (vrefine v p) (vrefine_f v p f) in
    elim_vrefine v p;
    change_equal_slprop (vrefine_f v p f x) (f x);
    x

let intro_vrefinedep
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  (f': vprop)
  : SteelGhost unit opened
  (v `star` f')
  (fun _ -> vrefinedep v p f)
  (requires fun h ->
    p (h v) /\
    f' == f (h v))
  (ensures fun h _ h' ->
    p (h v) /\
    f' == f (h v) /\
    (let x2 = h' (vrefinedep v p f) in
    let sn : t_of f' = h f' in
    dfst x2 == h v /\
    dsnd x2 == sn)
  )
  = intro_vrefine v p;
    intro_vdep (vrefine v p) f' (vrefine_f v p f);
    change_slprop_rel (vdep (vrefine v p) (vrefine_f v p f)) (vrefinedep v p f)
      (fun x y -> dfst x == dfst y /\ dsnd x == dsnd y)
      (vrefinedep_lemma2 v p f)

#pop-options
