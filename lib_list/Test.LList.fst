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
  intro_llist_nil (fun _ -> emp);
  pack_list (fun _ -> emp) r1 null_t 0UL;
  pack_list (fun _ -> emp) r2 r1 1UL;
  cons_is_not_null (fun _ -> emp) r2;
  let n = unpack_list (fun _ -> emp) r2 in
  pack_list (fun _ -> emp) r2 (get_next n) 1UL;
  return r2
