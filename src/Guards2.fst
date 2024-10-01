module Guards2

let guard_slab size_class arr
  = if enable_guard_pages then trap_array arr else A.varray arr

let mmap_trap_guard size_class arr len =
  if enable_guard_pages then (
    mmap_strict_trap arr len;
    change_equal_slprop (trap_array arr) (guard_slab size_class arr)
  ) else (
    noop ();
    change_equal_slprop (A.varray arr) (guard_slab size_class arr)
  )
