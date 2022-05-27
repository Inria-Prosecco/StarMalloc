module ArrayTest

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array0
open Steel.Array0
module P = Steel.FractionalPermission
module U32 = FStar.UInt32

let temp (v1 v2: U32.t) (n: U32.t{U32.v n > 1})
  : SteelT U32.t
  emp
  (fun _ -> emp)
  =
  let arr = A.malloc v1 n in
  let v1' = A.index arr 1ul in
  A.upd arr 0ul v1';
  A.upd arr 1ul v2;
  let v2' = A.index arr 1ul in
  assert (v1 == v1');
  assert (v2 == v2');
  A.free arr;
  return v2'

let temp2 (v1 v2: U32.t)
  : SteelT U32.t
  emp (fun _ -> emp)
  =
  let arr = A.malloc 0ul 8ul in
  let h0 = get () in
  assert (aselp arr P.full_perm h0 =!= Seq.empty);
  A.ghost_split arr 4ul;
  slassert (
    A.varrayp (A.split_l arr 4ul) P.full_perm `star`
    A.varrayp (A.split_r arr 4ul) P.full_perm
  );
  let arr1 = A.split_l arr 4ul in
  let arr2 = A.split_r arr 4ul in
  let arr'' = A.join arr1 arr2 in
  let h1 = get () in
  assert (asel arr h0 == asel arr'' h1);
  //drop (A.varrayp arr'' P.full_perm);
  free arr'';
  return 0ul

let temp3 (v1 v2: U32.t)
  : SteelT U32.t
  emp (fun _ -> emp)
  =
  let arr = A.malloc 0ul 8ul in
  let h0 = get () in
  A.ghost_split arr 4ul;
  slassert (
    A.varrayp (A.split_l arr 4ul) P.full_perm `star`
    A.varrayp (A.split_r arr 4ul) P.full_perm
  );
  A.ghost_split (A.split_l arr 4ul) 2ul;
  slassert (
    A.varrayp (A.split_l (A.split_l arr 4ul) 2ul) P.full_perm `star`
    A.varrayp (A.split_r (A.split_l arr 4ul) 2ul) P.full_perm `star`
    A.varrayp (A.split_r arr 4ul) P.full_perm
  );
  let arr' = A.join
    (A.split_r (A.split_l arr 4ul) 2ul)
    (A.split_r arr 4ul) in
  let arr'' = A.join
    (A.split_l (A.split_l arr 4ul) 2ul)
    arr' in
  let h1 = get () in
  //drop (A.varrayp arr'' P.full_perm);
  free arr'';
  //let arr1 = A.split_l arr 4ul in
  let arr11 = A.split_l (A.split_l arr 4ul) 2ul in
  let arr12 = A.split_r (A.split_l arr 4ul) 2ul in
  let arr2 = A.split_r arr 4ul in
  A.merge_assoc arr11 arr12 arr2;
  assert (asel arr h0 `Seq.equal` asel arr'' h1);
  assert (asel arr h0 == asel arr'' h1);

  //sladmit ();
  return 0ul


let temp4 (v1 v2: U32.t)
  : SteelT U32.t
  emp (fun _ -> emp)
  =
  let arr = A.malloc 0ul 8ul in
  let h0 = get () in
  let arr1 = A.split_l arr 4ul in
  let arr11 = A.split_l (A.split_l arr 4ul) 2ul in
  let arr12 = A.split_r (A.split_l arr 4ul) 2ul in
  let arr2 = A.split_r arr 4ul in
  A.ghost_split arr 4ul;
  slassert (
    A.varrayp (A.split_l arr 4ul) P.full_perm `star`
    A.varrayp (A.split_r arr 4ul) P.full_perm
  );
  A.ghost_split (A.split_l arr 4ul) 2ul;
  slassert (
    A.varrayp (A.split_l (A.split_l arr 4ul) 2ul) P.full_perm `star`
    A.varrayp (A.split_r (A.split_l arr 4ul) 2ul) P.full_perm `star`
    A.varrayp (A.split_r arr 4ul) P.full_perm
  );
  let arr' = A.join
    (A.split_r (A.split_l arr 4ul) 2ul)
    (A.split_r arr 4ul) in
  let arr'' = A.join
    (A.split_l (A.split_l arr 4ul) 2ul)
    arr' in
  let h1 = get () in
  drop (A.varrayp arr'' P.full_perm);
  A.merge_assoc arr11 arr12 arr2;
  assert (asel arr h0 `Seq.equal` asel arr'' h1);
  assert (asel arr h0 == asel arr'' h1);

  //sladmit ();
  return 0ul
