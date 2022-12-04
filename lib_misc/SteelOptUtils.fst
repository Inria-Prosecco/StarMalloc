module SteelOptUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory

let none_as_emp
  (#a: Type0)
  : Pure vprop
  (requires True)
  (ensures fun r -> t_of r == option a)
  =
  VUnit ({
    hp = SM.emp;
    t = option a;
    sel = fun _ -> None
  })

let some_as_vp
  (#a: Type0)
  (vp: vprop)
  : Pure vprop
  (requires t_of vp == a /\ VUnit? vp)
  (ensures fun r -> t_of r == option a)
  =
  VUnit ({
    hp = hp_of vp;
    t = option a;
    sel = fun h -> Some (sel_of vp h)
  })


let c2
 (#a: Type0)
 (b: bool)
 (vp: vprop{t_of vp == a /\ VUnit? vp})
 : vprop
 =
 if b
 then some_as_vp #a vp
 else none_as_emp #a

let c2_t
 (#a: Type0)
 (b: bool)
 (vp: vprop{t_of vp == a /\ VUnit? vp})
 : Lemma
 (t_of (c2 #a b vp) == option a)
 = ()

let c2_lemma
  (#a: Type0)
  (b: bool)
  (vp: vprop{t_of vp == a /\ VUnit? vp})
  (h: hmem (c2 #a b vp))
  : Lemma
  (
    c2_t #a b vp;
    (b ==> Some? (sel_of (c2 #a b vp) h <: option a)) /\
    (not b ==> None? (sel_of (c2 #a b vp) h <: option a))
  )
  = ()
