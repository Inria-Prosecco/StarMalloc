module BugSteelCompatRefine

open Steel.Effect.Atomic
open Steel.Effect
module SR = Steel.Reference

let f (r: SR.ref nat)
  =
  SR.vptr r `vdep` (fun (k:nat) -> emp)

#push-options "--compat_pre_typed_indexed_effects"
let mini_test
  (r: SR.ref nat)
  : SteelT unit
  (
    f r
    `vrefine`
    (fun (|a,b|) -> True))
  (fun _ ->
    f r
    `vrefine`
    (fun (|a,b|) -> True))
  =
  elim_vrefine
    (f r)
    (fun (|a,b|) -> True);
  intro_vrefine
    (f r)
    (fun (|a,b|) -> True)
#pop-options

// regression
[@@ expect_failure]
let mini_test2
  (r: SR.ref nat)
  : SteelT unit
  (
    f r
    `vrefine`
    (fun (|a,b|) -> True))
  (fun _ ->
    f r
    `vrefine`
    (fun (|a,b|) -> True))
  =
  elim_vrefine
    (f r)
    (fun (|a,b|) -> True);
  intro_vrefine
    (f r)
    (fun (|a,b|) -> True)
