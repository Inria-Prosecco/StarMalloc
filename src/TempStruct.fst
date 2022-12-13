module TempStruct

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module U64 = FStar.UInt64
module U8 = FStar.UInt8

let array = Steel.ST.Array.array
let ptr = Steel.ST.Array.ptr

unfold
let blob
  =
  (arr:array U8.t{A.length arr = 12})
  & (arr:array U64.t{A.length arr = 4})

noeq
type blob2 = {
  a: arr:array U64.t{A.length arr = 4};
  b: ref U64.t;
}

let temp (b: blob2)
  : SteelT blob2
  emp (fun _ -> emp)
  = return b
