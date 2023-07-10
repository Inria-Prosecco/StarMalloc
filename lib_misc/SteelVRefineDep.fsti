module SteelVRefineDep

open Steel.Effect.Atomic
open Steel.Effect

module SM = Steel.Memory
module G = FStar.Ghost

val vrefinedep_hp
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  : Tot (SM.slprop u#1)

[@__steel_reduce__]
let vrefinedep_t
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  : Tot Type
  =
  dtuple2 (t_of (vrefine v p)) (fun x -> t_of (f x))

val vrefinedep_sel
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : Tot (selector (vrefinedep_t v p f) (vrefinedep_hp v p f))

[@@__steel_reduce__]
let vrefinedep'
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : Tot vprop' = {
  hp = vrefinedep_hp v p f;
  t = vrefinedep_t v p f;
  sel = vrefinedep_sel v p f;
}
[@@__steel_reduce__]
let vrefinedep
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  = VUnit (vrefinedep' v p f)

val elim_vrefinedep
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
    h' v == res /\
    (let fs : x:t_of v{p x} = h' v in
    let sn : t_of (f (G.reveal res)) = h' (f (G.reveal res)) in
    let x2 = h (vrefinedep v p f) in
    G.reveal res == fs /\
    dfst x2 == fs /\
    dsnd x2 == sn /\
    True)
  )

val intro_vrefinedep
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

#push-options "--compat_pre_typed_indexed_effects"
#push-options "--z3rlimit 20"
let vrefinedep_idem
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : SteelGhost unit opened
  (vrefinedep v p f)
  (fun _ -> vrefinedep v p f)
  (requires fun _ -> True)
  (ensures fun h _ h' ->
    h (vrefinedep v p f)
    ==
    h' (vrefinedep v p f)
  )
  =
  let x0 = gget (vrefinedep v p f) in
  let x = elim_vrefinedep v p f in
  intro_vrefinedep v p  f (f (G.reveal x));
  let x1 = gget (vrefinedep v p f) in
  assert (dfst x0 == dfst x1);
  assert (dsnd x0 == dsnd x1);
  assert (x0 == x1)
#pop-options
#pop-options
