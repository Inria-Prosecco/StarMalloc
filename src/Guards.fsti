module Guards

open Utils2
module U8 = FStar.UInt8

val is_guard (size_class: sc) (slab: array U8.t) : prop
