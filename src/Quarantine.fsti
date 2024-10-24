module Quarantine

open Utils2
open SlotsAlloc

open Steel.Effect.Atomic
open Steel.Effect

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

module A = Steel.Array
module G = FStar.Ghost

open Constants
open Config
open MemoryTrap

/// Depending on whether the config flag
/// `enable_quarantine_trap` is enabled, this either
/// corresponds to `trap_array` or to `varray`
val quarantine_slab
  (arr: array U8.t{A.length arr = U32.v page_size})
  : vprop

inline_for_extraction noextract
val mmap_trap_quarantine
  (arr: array U8.t{A.length arr = U32.v page_size})
  (len: US.t{US.v len = U32.v page_size})
  : SteelT unit (A.varray arr) (fun _ -> quarantine_slab arr)

inline_for_extraction noextract
val mmap_untrap_quarantine
  (arr: array U8.t{A.length arr = U32.v page_size})
  (len: US.t{US.v len = U32.v page_size})
  : SteelT unit (quarantine_slab arr) (fun _ -> A.varray arr)
