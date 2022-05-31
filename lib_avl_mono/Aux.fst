module Aux

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

open Impl.Core

module U = FStar.UInt64

let a = U.t & U.t

noextract
assume val trees_malloc (x: U.t) : Steel (ref U.t)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

noextract
assume val trees_malloc2 (x: node a)
  : Steel (ref (node a))
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))
