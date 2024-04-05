module MemoryTrap

open Utils2

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
// assume val
val mmap_strict_trap
  (arr: array U8.t)
  (len: US.t)
  : Steel unit
  (A.varray arr)
  (fun _ -> trap_array arr)
  (requires fun _ ->
    A.length arr == US.v len /\
    US.v len % U32.v page_size == 0 /\
    US.v len > 0
  )
  (ensures fun _ _ _ -> True)
///
/// Introduction function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a madvise(MADV_DONTNEED)
// assume val
val mmap_trap
  (arr: array U8.t)
  (len: US.t)
  : Steel unit
  (A.varray arr)
  (fun _ -> trap_array arr)
  (requires fun _ ->
    A.length arr == US.v len /\
    US.v len % U32.v page_size == 0 /\
    US.v len > 0
  )
  (ensures fun _ _ _ -> True)

/// Elimination function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a mmap(PROT_READ|PROT_WRITE)
// assume val
val mmap_strict_untrap
  (arr: array U8.t)
  (len: US.t)
  : Steel unit
  (trap_array arr)
  (fun _ -> A.varray arr)
  (requires fun _ ->
    A.length arr == US.v len /\
    US.v len % U32.v page_size == 0 /\
    US.v len > 0
  )
  (ensures fun _ _ _ -> True)

/// Elimination function for the abstract `trap_array`
/// predicate above. Under the hood, this function will
/// be implemented in C as a noop.
// assume val
val mmap_untrap
  (arr: array U8.t)
  (len: US.t)
  : Steel unit
  (trap_array arr)
  (fun _ -> A.varray arr)
  (requires fun _ ->
    A.length arr == US.v len /\
    US.v len % U32.v page_size == 0 /\
    US.v len > 0
  )
  (ensures fun _ _ _ -> True)
