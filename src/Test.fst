module Test

module US = FStar.SizeT
module U8 = FStar.UInt8
open FStar.Mul
open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

open Config
open Main
open Main.Meta
open StarMalloc

noeq type r_struct = {
  r: A.array U8.t;
  b: bool;
}

let test (arena_id: US.t{US.v arena_id < US.v nb_arenas}) (_:unit)
  : Steel r_struct
  (
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (fun result ->
    (if result.b then emp else A.varray result.r) `star`
    A.varray (A.split_l sc_all.slab_region 0sz) `star`
    A.varray (A.split_r sc_all.slab_region slab_region_size)
  )
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  let ptr = malloc arena_id 16sz in
  assume (within_size_classes_pred ptr);
  let b = free ptr in
  {
    r = ptr;
    b = b;
  }
