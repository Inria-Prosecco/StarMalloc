 module MemoryTrap

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

open Config

/// A model of "trap" memory, representing that the array
/// pointed to by [arr] is mapped by the OS, but that
/// any access to it will yield an OS fault (SIGSEGV).
/// To avoid any misuse of this predicate and model,
/// this predicate is abstract, does not expose any
/// primitive to use it, and can only be introduced
/// through the mmap_trap function below
assume val trap_array (sc: sc_full)
  (arr: array U8.t{A.length arr = U32.v sc.slab_size}) : vprop

/// Introduction function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a mmap(PROT_NONE)
assume val mmap_strict_trap (sc: G.erased sc_full)
  (arr: array U8.t{A.length arr = U32.v (G.reveal sc).slab_size})
  (len: US.t{US.v len == A.length arr /\ US.v len > 0})
  : SteelT unit
  (A.varray arr)
  (fun _ -> trap_array sc arr)

/// Introduction function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a madvise(MADV_DONTNEED)
assume val mmap_trap (sc: G.erased sc_full)
  (arr: array U8.t{A.length arr = U32.v (G.reveal sc).slab_size})
  (len: US.t{US.v len == A.length arr /\ US.v len > 0})
  : SteelT unit
  (A.varray arr)
  (fun _ -> trap_array sc arr)

/// Elimination function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a mmap(PROT_READ|PROT_WRITE)
assume val mmap_strict_untrap (sc: G.erased sc_full)
  (arr: array U8.t{A.length arr = U32.v (G.reveal sc).slab_size})
  (len: US.t{US.v len == A.length arr /\ US.v len > 0})
  : SteelT unit
  (trap_array sc arr)
  (fun _ -> A.varray arr)

/// Elimination function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a noop.
assume val mmap_untrap (sc: G.erased sc_full)
  (arr: array U8.t{A.length arr = U32.v (G.reveal sc).slab_size})
  (len: US.t{US.v len == A.length arr /\ US.v len > 0})
  : SteelT unit
  (trap_array sc arr)
  (fun _ -> A.varray arr)
