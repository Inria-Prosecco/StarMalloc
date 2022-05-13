module Test

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

let temp (#a: Type0) (v1 v2: a) (n: nat{n > 0})
  : SteelT unit
  emp
  (fun _ -> emp)
  =
  let arr = A.malloc2 v1 n in
  let v1' = A.read2 arr 0 in
  A.write2 arr 0 v2;
  let v2' = A.read2 arr 0 in
  assert (v1 == v1');
  assert (v2 == v2');
  A.free2 arr
