module BugSteelRefinementType

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

[@@ expect_failure]
let ref_fail (#a #b: Type0)
  (f: a -> (vp:vprop{t_of vp == b}))
  (x: a)
  : SteelT unit
  (f x)
  (fun _ -> f x)
  =
  return ()

let vp = vp:vprop{t_of vp == nat}

[@@ expect_failure]
let ref_fail (#a: Type0)
  (f: a -> vp)
  (x: a)
  : SteelT unit
  (f x)
  (fun _ -> f x)
  =
  assert (t_of (f x) == nat);
  return ()

let ref_workaround (#a #b: Type0)
  (f: a -> vprop)
  (x: a)
  (_: unit{forall x. t_of (f x) == b})
  : SteelT unit
  (f x)
  (fun _ -> f x)
  =
  assert (t_of (f x) == b);
  return ()
