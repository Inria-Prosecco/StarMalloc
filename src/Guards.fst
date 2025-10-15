module Guards

open Constants
open Config

let guard_slab sc arr = if enable_guard_pages then trap_array sc arr else A.varray arr

let mmap_trap_guard sc arr len =
  if enable_guard_pages then (
    mmap_strict_trap sc arr len;
    change_equal_slprop (trap_array sc arr) (guard_slab sc arr)
  ) else (
    noop ();
    change_equal_slprop (A.varray arr) (guard_slab sc arr)
  )
