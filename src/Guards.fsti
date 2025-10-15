module Guards

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
/// `enable_guard_pages` is enabled, this either
/// corresponds to `trap_array` or to `varray`
val guard_slab
  (size_class: sc_full)
  (arr: array U8.t{A.length arr = U32.v size_class.slab_size})
  : vprop

inline_for_extraction noextract
val mmap_trap_guard
  (size_class: sc_full)
  (arr: array U8.t{A.length arr = U32.v size_class.slab_size})
  (len: US.t{US.v len = U32.v size_class.slab_size})
  : SteelT unit (A.varray arr) (fun _ -> guard_slab size_class arr)
