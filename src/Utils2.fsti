module Utils2

module U64 = FStar.UInt64
module U32 = FStar.UInt32

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array


let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr

unfold let slab_metadata = r:array U64.t{A.length r = 4}

//TODO: should not be hardcoded
let page_size = 4096ul
let slab_max_number = 4096ul

noextract
let min_sc = 16
noextract
let max_sc = 64

//TODO: second constraint should be relaxed
//currently does not support size classes with <64 slots
//that require a subtle loop to read only possible
//corresponding slots in the bitmap
let sc = x:U32.t{min_sc <= U32.v x /\ U32.v x <= max_sc}


let nb_slots (size_class: sc)
  : Pure U32.t
  (requires True)
  (ensures fun r ->
    U32.v r >= 1 /\
    U32.v r <= 256
  )
  =
  U32.div page_size size_class
