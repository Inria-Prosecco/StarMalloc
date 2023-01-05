module SlabsOverlay

open Utils2
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

open Slabs

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module SL = Selectors.LList

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

let elim_vrefinedep
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : SteelGhost (G.erased (t_of (vrefine v p))) opened
  (vrefinedep v p f)
  (fun res -> v `star` f (G.reveal res))
  (requires fun _ -> True)
  (ensures fun h res h' ->
    let (res : normal (t_of v){p res}) = res in
    p res /\
    G.reveal res == h' v /\
    (let fs : x:t_of v{p x} = h' v in
    let sn : t_of (f (G.reveal res)) = h' (f (G.reveal res)) in
    let x2 = h (vrefinedep v p f) in
    G.reveal res == fs /\
    dfst x2 == fs /\
    dsnd x2 == sn /\
    True)
  )
  =
    change_slprop_rel (vrefinedep v p f) (vdep (vrefine v p) (vrefine_f v p f))
      (fun x y -> dfst x == dfst y /\ dsnd x == dsnd y) (vrefinedep_lemma v p f);
    let x = elim_vdep (vrefine v p) (vrefine_f v p f) in
    elim_vrefine v p;
    change_equal_slprop (vrefine_f v p f x) (f x);
    x

assume val intro_vrefinedep
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (x:t_of v{p x}) -> Tot vprop))
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
