module Guards

open Utils2
open SlotsAlloc

open Steel.Effect

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module A = Steel.Array

val is_guard
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  (x: normal (t_of (slab_vprop size_class arr md)))
  : prop
