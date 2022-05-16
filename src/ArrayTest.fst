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
  let arr = A.malloc2 v1 n  in
  let v1' = A.read2 arr 1ul in
  A.write2 arr 0ul v1';
  A.write2 arr 1ul v2;
  let v2' = A.read2 arr 1ul in
  assert (v1 == v1');
  assert (v2 == v2');
  A.free2 arr;
  return v2'
