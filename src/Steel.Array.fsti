module Steel.Array

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
module Mem = Steel.Memory
module H = Steel.HigherArray
module U = FStar.Universe
module U32 = FStar.UInt32

#set-options "--ide_id_info_off"
//#set-options "--print_implicits"

open FStar.Seq
open Seq.Aux
module A = Steel.Array.Aux
open Steel.Array.Aux

noeq type array (a: Type0) : Type u#0
  =
  {
    max_length: nat;
    content: A.array_ref a #max_length;
    idx: nat;
    length: l:nat{idx + l <= max_length};
  }

unfold let get_max_length (#a: Type0) (arr: array a)
  = arr.max_length
unfold let get_content (#a: Type0) (arr: array a)
  = arr.content
unfold let get_i1 (#a: Type0) (arr: array a)
  = arr.idx
unfold let get_i2 (#a: Type0) (arr: array a)
  = arr.idx + arr.length
unfold let get_length (#a: Type0) (arr: array a)
  = get_i2 arr - get_i1 arr


//[@@ __steel_reduce__; __reduce__]
unfold let varrayp (#a: Type0)
  (arr: array a)
  (p: lseq (option perm) (get_max_length arr){perm_ok p})
  : vprop
  = varrp
    (get_content arr)
    (get_i1 arr)
    (get_i2 arr)
    p

//[@@ __steel_reduce__; __reduce__]
unfold let varray (#a: Type0) (arr: array a) : vprop
  =
  varr
    (get_content arr)
    (get_i1 arr)
    (get_i2 arr)

[@@ __steel_reduce__]
let aselp (#a: Type0) (#vp: vprop)
  (arr: array a)
  (p: lseq (option perm) (get_max_length arr){perm_ok p})
  (h: rmem vp{FStar.Tactics.with_tactic selector_tactic
    (can_be_split vp (varrayp arr p) /\ True)})
  : GTot (lseq a (get_length arr))
  = h (varrayp arr p)

[@@ __steel_reduce__]
let asel (#a: Type0) (#vp: vprop)
  (arr: array a)
  (h: rmem vp{FStar.Tactics.with_tactic selector_tactic
    (can_be_split vp (varray arr) /\ True)})
  : GTot (lseq a (get_length arr))
  = h (varray arr)

val malloc (#a: Type0) (v: a) (n: U32.t)
  : Steel (array a)
  emp
  (fun arr -> varray arr)
  (requires fun _ -> True)
  (ensures fun _ arr h1 ->
    get_i1 arr = 0 /\
    get_i2 arr = (U32.v n) /\
    get_max_length arr == (U32.v n) /\
    asel arr h1 == Seq.create (U32.v n) v /\
    not (is_null (get_content arr)))

val free (#a: Type0) (arr: array a)
  : Steel unit
  (varray arr)
  (fun _ -> emp)
  (requires fun _ ->
    get_i1 arr = 0 /\
    get_i2 arr = get_max_length arr)
  (ensures fun _ _ _ -> True)

val index (#a: Type0)
  (arr: array a)
  (i: U32.t)
  : Steel a
  (varray arr)
  (fun _ -> varray arr)
  (requires fun _ ->
    U32.v i < get_length arr)
  (ensures fun h0 v h1 ->
    U32.v i < get_length arr /\
    asel arr h1 == asel arr h0 /\
    Seq.index (asel arr h1) (U32.v i) == v)

val upd (#a: Type0)
  (arr: array a)
  (i: U32.t)
  (v_write: a)
  : Steel unit
  (varray arr)
  (fun _ -> varray arr)
  (requires fun _ ->
    U32.v i < get_length arr)
  (ensures fun h0 v h1 ->
    U32.v i < get_length arr /\
    Seq.index (asel arr h1) (U32.v i) == v_write)
    //asel arr h1 = Seq.upd (asel arr h0) i v_write

val split_l (#a: Type)
  (arr: array a)
  (i: nat)
  : Pure (array a)
  (requires
    get_i1 arr <= i /\
    i < get_i2 arr)
  (ensures fun arr' ->
    get_i1 arr' = get_i1 arr /\
    get_i2 arr' = i /\
    get_length arr' = i - get_i1 arr)

val split_r (#a: Type)
  (arr: array a)
  (i: nat)
  : Pure (array a)
  (requires
    get_i1 arr <= i /\
    i < get_i2 arr)
  (ensures fun arr' ->
    get_i1 arr' = i /\
    get_i2 arr' = get_i2 arr /\
    get_length arr' = get_i2 arr - i)

val split (#a: Type) (#opened:_)
  (arr: array a)
  (i: nat{get_i1 arr <= i /\ i < get_i2 arr})
  : SteelGhost unit opened
  (varray arr)
  (fun _ -> varray (split_l arr i) `star` varray (split_r arr i))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel arr h0
    == Seq.append
      (asel (split_l arr i) h1)
      (asel (split_r arr i) h1))

val merge (#a: Type) (#opened:_)
  (arr: array a)
  (i: nat{get_i1 arr <= i /\ i < get_i2 arr})
  : SteelGhost unit opened
  (varray (split_l arr i) `star` varray (split_r arr i))
  (fun _ -> varray arr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel arr h1
    == Seq.append
      (asel (split_l arr i) h0)
      (asel (split_r arr i) h0))
