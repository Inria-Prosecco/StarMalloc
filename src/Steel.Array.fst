module Steel.Array

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
module Mem = Steel.Memory
module H = Steel.HigherArray
module U = FStar.Universe
module U32 = FStar.UInt32

[@@ __steel_reduce__]
unfold let mk_array (#a: Type0)
  (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : arr:array a{
    get_max_length arr = n /\
    get_content arr == r /\
    get_i1 arr = i1 /\
    get_i2 arr = i2 /\
    get_length arr = i2 - i1
  }
  = {
    max_length = n;
    content = r;
    idx = i1;
    length = i2 - i1;
  }

let varray_to_varr (#a: Type0) (#opened:_) (arr: array a)
  : SteelGhost unit opened
  (varray arr)
  (fun _ -> varr (get_content arr) (get_i1 arr) (get_i2 arr))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel (get_content arr) (get_i1 arr) (get_i2 arr) h1
    ==
    asel arr h0)
  =
  change_slprop_rel
    (varray arr)
    (varr (get_content arr) (get_i1 arr) (get_i2 arr))
    (fun x y -> x == y)
    (fun _ -> ())

let varr_to_varray (#a: Type0) (#opened:_)
  (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : SteelGhost unit opened
  (varr r i1 i2)
  (fun _ -> varray (mk_array n r i1 i2))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel (mk_array n r i1 i2) h1
    ==
    A.asel r i1 i2 h0)
  =
  change_slprop_rel
    (varr r i1 i2)
    (varray (mk_array n r i1 i2))
    (fun x y -> x == y)
    (fun _ -> ())

let malloc (#a: Type0) (v: a) (n: U32.t)
  //(v: lseq a n)
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
  =
  let v = Seq.create (U32.v n) v in
  let r = A.malloc (U32.v n) v in
  varr_to_varray r 0 (U32.v n);
  let arr = mk_array (U32.v n) r 0 (U32.v n) in
  return arr

let free (#a: Type0) (arr: array a)
  : Steel unit
  (varray arr)
  (fun _ -> emp)
  (requires fun _ ->
    get_length arr = get_max_length arr)
  (ensures fun _ _ _ -> True)
  =
  varray_to_varr arr;
  change_slprop_rel
    (varr (get_content arr) (get_i1 arr) (get_i2 arr))
    (varr (get_content arr) 0 (get_max_length arr))
    (fun x y -> x == y)
    (fun _ -> ());
  A.free (get_content arr)

let index (#a: Type0)
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
  =
  varray_to_varr arr;
  let v = A.read (get_content arr) (get_i1 arr) (get_i2 arr) (U32.v i + get_i1 arr) in
  varr_to_varray (get_content arr) (get_i1 arr) (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      (get_i2 arr)))
    (varray arr)
    (fun x y -> x == y)
    (fun _ -> ());
  return v

let upd (#a: Type0)
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
  =
  varray_to_varr arr;
  A.write (get_content arr) (get_i1 arr) (get_i2 arr) (U32.v i + get_i1 arr) v_write;
  varr_to_varray (get_content arr) (get_i1 arr) (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      (get_i2 arr)))
    (varray arr)
    (fun x y -> x == y)
    (fun _ -> ());
  return ()

let split_l (#a: Type)
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
  =
  {arr with length = i - get_i1 arr}

let split_r (#a: Type)
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
  =
  let arr = {arr with length = get_i2 arr - i} in
  {arr with idx = i}

let split (#a: Type) (#opened:_)
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
  =
  varray_to_varr arr;
  A.split (get_content arr) (get_i1 arr) (get_i2 arr) i;
  varr_to_varray (get_content arr) (get_i1 arr) i;
  varr_to_varray (get_content arr) i (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      i))
    (varray (split_l arr i))
    (fun x y -> x == y)
    (fun _ -> ());
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      i
      (get_i2 arr)
    ))
    (varray (split_r arr i))
    (fun x y -> x == y)
    (fun _ -> ());
  return ()

let merge (#a: Type) (#opened:_)
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
  =
  varray_to_varr (split_l arr i);
  varray_to_varr (split_r arr i);
  change_slprop_rel
    (varr
      (get_content (split_l arr i))
      (get_i1 (split_l arr i))
      (get_i2 (split_l arr i)))
    (varr (get_content arr) (get_i1 arr) i)
    (fun x y -> x == y)
    (fun _ -> ());
  change_slprop_rel
    (varr
      (get_content (split_r arr i))
      (get_i1 (split_r arr i))
      (get_i2 (split_r arr i)))
    (varr (get_content arr) i (get_i2 arr))
    (fun x y -> x == y)
    (fun _ -> ());
  A.merge (get_content arr) (get_i1 arr) (get_i2 arr) i;
  varr_to_varray (get_content arr) (get_i1 arr) (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      (get_i2 arr)))
    (varray arr)
    (fun x y -> x == y)
    (fun _ -> ());
  return ()
