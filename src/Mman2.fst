module Mman2

open Steel.Effect.Atomic
open Steel.Effect
module R = Steel.Reference

open Impl.Trees.Types
module G = FStar.Ghost

/// Memory management axiomatizations

assume val mmap_ptr_metadata_init (_:unit)
  : SteelT (R.ref t)
  emp
  (fun r -> R.vptr r)
