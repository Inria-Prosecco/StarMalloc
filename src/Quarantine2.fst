module Quarantine2

let quarantine_slab size_class arr =
  if enable_quarantine_trap
  then trap_array arr
  else A.varray arr

let mmap_trap_quarantine size_class arr len =
  if enable_quarantine_trap then (
    if enable_quarantine_strict_trap then (
      mmap_strict_trap arr len
    ) else (
      mmap_trap arr len
    );
    change_equal_slprop
      (trap_array arr)
      (quarantine_slab size_class arr)
  ) else (
    noop ();
    change_equal_slprop
      (A.varray arr)
      (quarantine_slab size_class arr)
  )

let mmap_untrap_quarantine size_class arr len =
  if enable_quarantine_trap then (
    change_equal_slprop
      (quarantine_slab size_class arr)
      (trap_array arr);
    if enable_quarantine_strict_trap then (
      mmap_strict_untrap arr len
    ) else (
      mmap_untrap arr len
    )
  ) else (
    noop ();
    change_equal_slprop
      (quarantine_slab size_class arr)
      (A.varray arr)
  )
