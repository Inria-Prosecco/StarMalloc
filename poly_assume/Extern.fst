module Extern

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U64 = FStar.UInt64
//open Impl.Core

noextract
assume val f1 (x: U64.t) : SteelT (ref U64.t)
  emp (fun r -> vptr r)

noextract
assume val f2 (#a: Type0) (x: a) : SteelT (ref a)
  emp (fun r -> vptr r)

//let f2_mono = f2 U64.t
