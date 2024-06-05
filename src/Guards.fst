module Guards

open Constants
open Config

let guard_slab arr = if enable_guard_pages then trap_array arr else A.varray arr

let mmap_trap_guard arr len =
  if enable_guard_pages then (
    mmap_strict_trap arr len;
    change_equal_slprop (trap_array arr) (guard_slab arr)
  ) else (
    noop ();
    change_equal_slprop (A.varray arr) (guard_slab arr)
  )
