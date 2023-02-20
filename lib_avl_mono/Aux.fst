module Aux

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

open Impl.Core

module US = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8

let array = Steel.ST.Array.array

let a = array U8.t & US.t

noextract
assume val trees_malloc (x: U64.t) : Steel (ref U64.t)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

noextract
assume val trees_malloc2 (x: node a)
  : Steel (ref (node a))
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

noextract
assume val trees_free (r: ref U64.t) : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)

noextract
assume val trees_free2 (r: ref (node a)) : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
