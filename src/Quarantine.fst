module Quarantine

open Constants
open Config

let quarantine_slab arr =
  if enable_quarantine_trap
  then trap_array arr
  else A.varray arr

let mmap_trap_quarantine arr len =
  if enable_quarantine_trap then (
    if enable_quarantine_strict_trap then (
      mmap_strict_trap arr len
    ) else (
      mmap_trap arr len
    );
    change_equal_slprop (trap_array arr) (quarantine_slab arr)
  ) else (
    noop ();
    change_equal_slprop (A.varray arr) (quarantine_slab arr)
  )

let mmap_untrap_quarantine arr len =
  if enable_quarantine_trap then (
    change_equal_slprop (quarantine_slab arr) (trap_array arr);
    if enable_quarantine_strict_trap then (
      mmap_strict_untrap arr len
    ) else (
      mmap_untrap arr len
    )
  ) else (
    noop ();
    change_equal_slprop (quarantine_slab arr) (A.varray arr)
  )
