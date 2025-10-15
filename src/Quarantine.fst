module Quarantine

open Constants
open Config

let quarantine_slab sc arr =
  if enable_quarantine_trap
  then trap_array sc arr
  else A.varray arr

let mmap_trap_quarantine sc arr len =
  if enable_quarantine_trap then (
    if enable_quarantine_strict_trap then (
      mmap_strict_trap (G.hide sc) arr len
    ) else (
      mmap_trap (G.hide sc) arr len
    );
    change_equal_slprop (trap_array sc arr) (quarantine_slab sc arr)
  ) else (
    noop ();
    change_equal_slprop (A.varray arr) (quarantine_slab sc arr)
  )

let mmap_untrap_quarantine sc arr len =
  if enable_quarantine_trap then (
    change_equal_slprop (quarantine_slab sc arr) (trap_array sc arr);
    if enable_quarantine_strict_trap then (
      mmap_strict_untrap sc arr len
    ) else (
      mmap_untrap sc arr len
    )
  ) else (
    noop ();
    change_equal_slprop (quarantine_slab sc arr) (A.varray arr)
  )
