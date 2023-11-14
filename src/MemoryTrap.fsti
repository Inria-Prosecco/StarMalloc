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
val trap_array (arr: array U8.t) : vprop

/// Introduction function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a mmap(PROT_NONE)
val mmap_strict_trap
  (arr: array U8.t)
  (len: US.t{US.v len == A.length arr /\ US.v len > 0})
  : SteelT unit
  (A.varray arr)
  (fun _ -> trap_array arr)
///
/// Introduction function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a madvise(MADV_DONTNEED)
val mmap_trap
  (arr: array U8.t)
  (len: US.t{US.v len == A.length arr /\ US.v len > 0})
  : SteelT unit
  (A.varray arr)
  (fun _ -> trap_array arr)

/// Elimination function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a mmap(PROT_READ|PROT_WRITE)
val mmap_untrap
  (arr: array U8.t)
  (len: US.t{US.v len == A.length arr /\ US.v len > 0})
  : SteelT unit
  (trap_array arr)
  (fun _ -> A.varray arr)
