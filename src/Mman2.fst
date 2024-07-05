module Mman2

open Steel.Effect.Atomic
open Steel.Effect
module R = Steel.Reference

open Impl.Trees.Types
module G = FStar.Ghost

assume val mmap_ptr_metadata (_:unit)
  : SteelT (R.ref t)
  emp
  (fun r -> R.vptr r)
