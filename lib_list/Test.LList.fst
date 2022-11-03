module Test.LList


open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U64 = FStar.UInt64

open Selectors.LList

let temp (_:unit)
  : Steel (t U64.t)
  emp
  (fun ptr -> llist (fun _ -> emp) ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_llist (fun _ -> emp) ptr h1 == [ 1UL ; 0UL ]
  )
  =
  let c1 = mk_cell null_t 0UL in
  let r1 = malloc c1 in
  let c2 = mk_cell r1 1UL in
  let r2 = malloc c2 in
  intro_llist_nil U64.t (fun _ -> emp);
  intro_llist_cons (fun _ -> emp) r1 null_t 0UL;
  intro_llist_cons (fun _ -> emp) r2 r1 1UL;
  r2
