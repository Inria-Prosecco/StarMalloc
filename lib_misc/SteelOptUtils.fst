module SteelOptUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory

let none_as_emp
  (#a: Type0)
  : Tot vprop
  =
  VUnit ({
    hp = SM.emp;
    t = option a;
    sel = fun _ -> None
  })

let none_as_emp_equiv (#a: Type0)
  : Lemma
  (equiv emp (none_as_emp #a))
  =
  reveal_emp ();
  assert (hp_of emp == SM.emp);
  assert_norm (hp_of (none_as_emp #a) == SM.emp);
  SM.reveal_equiv (hp_of emp) (hp_of (none_as_emp #a));
  reveal_equiv emp (none_as_emp #a)

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

//let c2_sel_lemma
//  (#a: Type0)
//  (b: bool)
//  (vp: vprop{t_of vp == a /\ VUnit? vp})
//  (m: SM.mem)
//  : Lemma
//  (requires SM.interp (hp_of (c2 #a b vp)) m)
//  (ensures
//    (b ==> Some? (sel_of (c2 #a b vp) m <: option a)) /\
//    (not b ==> None? (sel_of (c2 #a b vp) m <: option a))
//  )
//  = ()
