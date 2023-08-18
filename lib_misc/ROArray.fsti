module ROArray

open Steel.FractionalPermission
open Steel.Array
open Steel.Effect

module US = FStar.SizeT

(** This module provides a model for read-only arrays. This model corresponds to "frozen" arrays,
    that cannot be updated anymore. In exchange, the permission on a read-only array is freely duplicable *)

/// Read-only arrays are eraseable values, representing a read-only permission on [r].
/// As a value, it is therefore freely duplicable
/// It is also indexed by a sequence [s] corresponding to its contents
inline_for_extraction noextract
val ro_array (#a:Type) (r: array a) (s:Ghost.erased (Seq.lseq a (length r))) : Type0

/// Creates a new ro_array associated to array [r], assuming
/// we have initially permission on [r]
inline_for_extraction noextract
val create_ro_array (#a:Type) (#p:perm) (r:array a) (s:Ghost.erased (Seq.lseq a (length r)))
  : Steel (ro_array r s) (varrayp r p) (fun _ -> emp)
          (requires fun h -> aselp r p h == Ghost.reveal s)
          (ensures fun _ _ _ -> True)

/// Wrapper around Steel.Array.index, to access element [i] of array [r]
inline_for_extraction noextract
val index (#a:Type) (#r:array a) (#s:Ghost.erased (Seq.lseq a (length r)))
  (ro: ro_array r s)
  (i: US.t{US.v i < length r})
  : Steel a emp (fun _ -> emp)
            (requires fun _ -> True)
            (ensures fun _ x _ -> x == Seq.index s (US.v i))
