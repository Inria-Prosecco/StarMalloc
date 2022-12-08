module BugSteelCompatIndexedEffectsExtractInfo

module G = FStar.Ghost
module Mem = Steel.Memory

open Steel.Effect.Atomic
open Steel.Effect

assume val t0 (a: Type0) : Type
assume val p1 (#a: Type0) (x: t0 a) : bool
assume val p2 (#a: Type0) (x: t0 a) : bool

let t1 (a: Type0) = x:t0 a{p1 x}
let t2 (a: Type0) = x:t1 a{p2 x}

assume val t (a: Type0) : Type0
assume val vprop_sl (#a: Type0) (ptr: t a) : Mem.slprop
assume val vprop_sel (#a: Type0) (r: t a) : selector (t2 a) (vprop_sl r)

[@@__steel_reduce__]
let wrapped_vprop' (#a: Type0) (r: t a) : vprop' = {
  hp = vprop_sl r;
  t = t2 a;
  sel = vprop_sel r
}
unfold let wrapped_vprop (#a: Type0) (tr: t a) : vprop = VUnit (wrapped_vprop' tr)

assume val lemma (#a:Type) (ptr:t a) (t:t2 a) (m:Mem.mem)
  : Lemma
  (requires Mem.interp (vprop_sl ptr) m)
  (ensures True)

[@@ __steel_reduce__]
let v_wrapped_vprop
  (#a:Type0)
  (#p:vprop)
  (r:t a)
  (h:rmem p{
    FStar.Tactics.with_tactic selector_tactic (can_be_split p (wrapped_vprop r) /\ True)
  })
  = h (wrapped_vprop r)

#push-options "--compat_pre_typed_indexed_effects"
let extract_info1 (#a:Type0) (ptr: t a)
  : SteelT unit
  (wrapped_vprop ptr) (fun _ -> wrapped_vprop ptr)
  =
  let h = get () in
  let t = G.hide (v_wrapped_vprop ptr h) in
  extract_info (wrapped_vprop ptr) t True
    (lemma ptr t)
#pop-options

// regression
[@@ expect_failure]
let extract_info2 (#a:Type0) (ptr: t a)
  : SteelT unit
  (wrapped_vprop ptr) (fun _ -> wrapped_vprop ptr)
  =
  let h = get () in
  let t = G.hide (v_wrapped_vprop ptr h) in
  extract_info (wrapped_vprop ptr) t True
    (lemma ptr t)
