module RegionSelect

open Steel.FractionalPermission
open Steel.Array
open Steel.Effect
open Steel.ArrayArith

module U8 = FStar.UInt8

(** This module is a wrapper around Steel.ArrayArith that can be used to determine whether a given pointer is inside a slab_region *)

/// A duplicable read-only permission on arrays. It is internally implemented
/// as an invariant stating that there exists a valid permission on array r.
/// Hence, it will be extracted to unit, and erased by karamel
inline_for_extraction noextract
val ro_array (#a:Type) (r: array a) : Type0

/// Creates a new ro_array associated to array [r], assuming
/// we have initially permission on [r]
inline_for_extraction noextract
val create_ro_array (#a:Type) (#p:perm) (r:array a)
  : SteelT (ro_array r) (varrayp r p) (fun _ -> emp)

/// Wrapper around within_bounds_intro.
/// Note, it does not require permission on arr1 and arr2, only
/// the two tokens [ro1] and [ro2]
inline_for_extraction noextract
val within_bounds_intro
  (#pp:perm)
  (arr1 p arr2: array U8.t)
  (ro1:ro_array arr1)
  (ro2:ro_array arr2)
  : Steel bool
  (varrayp p pp)
  (fun _ -> varrayp p pp)
  (requires fun h0 -> same_base_array arr1 arr2)
  (ensures fun h0 r h1 ->
    (if r then within_bounds arr1 p arr2 else True) /\
    aselp p pp h1 ==  aselp p pp h0
  )
