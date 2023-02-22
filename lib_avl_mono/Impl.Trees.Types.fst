module Impl.Trees.Types

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

open Impl.Core

module US = FStar.SizeT
module U64 = FStar.UInt64
module U8 = FStar.UInt8

noextract inline_for_extraction
let array = Steel.ST.Array.array

noeq
type data = { ptr: array U8.t; size: US.t}

let node = node data
let t = t data

noextract
assume val trees_malloc (x: U64.t) : Steel (ref U64.t)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

noextract
assume val trees_malloc2 (x: node)
  : Steel (ref node)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

noextract
assume val trees_free (r: ref U64.t) : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)

noextract
assume val trees_free2 (r: ref node) : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
