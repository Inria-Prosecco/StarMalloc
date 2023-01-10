module TestArrayRef

open Steel.Effect.Atomic
open Steel.Effect

module A = Steel.Array
module SAR = Steel.ArrayRef


let array = Steel.ST.Array.array

let test (#a: Type)
  (arr: array a{A.length arr = 1})
  : Steel unit
  (A.varray arr)
  (fun _ -> SAR.vptr arr)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    Seq.index (A.asel arr h0) 0 == SAR.sel arr h1
  )
  =
  change_slprop_rel
    (A.varray arr)
    (SAR.vptr arr)
    (fun x y -> Seq.index x 0 == y)
    (fun _ -> admit ())

let test2 (#a: Type)
  (arr: array a{A.length arr = 1})
  : Steel unit
  (A.varray arr)
  (fun _ -> SAR.vptr arr)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    A.asel arr h0 == Seq.create 1 (SAR.sel arr h1)
  )
  =
  change_slprop_rel
    (A.varray arr)
    (SAR.vptr arr)
    (fun x y -> x == Seq.create 1 y)
    (fun _ -> admit ())
