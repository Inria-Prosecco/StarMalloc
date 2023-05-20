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

open Config
open MemoryTrap

val is_guard
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  (x: normal (t_of (slab_vprop size_class arr md)))
  : prop

let trap_implies_guard
  (size_class: sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: slab_metadata)
  (x: normal (t_of (slab_vprop size_class arr md)))
  : Lemma
  (requires is_trap size_class arr md x)
  (ensures is_guard size_class arr md x)
  = admit ()

let mmap_trap_guard
  (size_class: G.erased sc)
  (arr: array U8.t{A.length arr = U32.v page_size})
  (md: G.erased (array U64.t){A.length md = 4})
  (len: US.t{US.v len = U32.v page_size})
  : Steel unit
  (slab_vprop size_class arr md)
  (fun _ -> slab_vprop size_class arr md)
  (requires fun _ -> True)
  (ensures fun _ _ h1 ->
    let v = h1 (slab_vprop size_class arr md) in
    is_guard size_class arr md v
  )
  =
  if enable_guard_pages then (
    mmap_trap size_class arr md len;
    let v = gget (slab_vprop size_class arr md) in
    trap_implies_guard size_class arr md v
  ) else (
    let v = gget (slab_vprop size_class arr md) in
    assume (is_guard size_class arr md v)
  )
