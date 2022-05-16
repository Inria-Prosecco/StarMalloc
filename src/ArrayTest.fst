module ArrayTest

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
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
  let arr = A.malloc 0ul 50ul in
  A.split arr 5;
  A.split (A.split_r arr 5) 7;
  A.merge (A.split_r arr 5) 7;
  A.merge arr 5;
  A.free arr;
  return 0ul
