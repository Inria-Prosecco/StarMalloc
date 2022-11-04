module Test.LList


open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U64 = FStar.UInt64

open Selectors.LList

[@@__reduce__]
unfold let p = fun _ -> emp

let temp (_:unit)
  : Steel (t U64.t)
  emp
  (fun ptr -> llist p ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_llist p ptr h1 == [ 1UL ; 0UL ]
  )
  =
  let c1 = mk_cell null_t 0UL in
  let r1 = malloc c1 in
  let c2 = mk_cell r1 1UL in
  let r2 = malloc c2 in
  intro_llist_nil p;
  pack_list p r1 null_t 0UL;
  pack_list p r2 r1 1UL;
  cons_is_not_null p r2;
  let n = unpack_list p r2 in
  pack_list p r2 (get_next n) 1UL;
  return r2
