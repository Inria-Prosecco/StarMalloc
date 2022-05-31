module Impl.Common

module U = FStar.UInt64
module I = FStar.Int64

inline_for_extraction noextract
let one = U.uint_to_t 1
inline_for_extraction noextract
let zero = U.uint_to_t 0

inline_for_extraction noextract
let sone = I.int_to_t 1
inline_for_extraction noextract
let szero = I.int_to_t 0

inline_for_extraction noextract
let umax (x y: U.t) : U.t
  = if U.gt x y then x else y

type cmp (a: Type) = compare: (a -> a -> I.t){
  squash (forall x. I.eq (compare x x) I.zero) /\
  squash (forall x y. I.gt (compare x y) I.zero
                 <==> I.lt (compare y x) I.zero) /\
  squash (forall x  y z. I.gte (compare x y) I.zero /\
                         I.gte (compare y z) I.zero ==>
                         I.gte (compare x z) I.zero)
}

let convert (#a: Type) (cmp: cmp a) : GTot (Spec.BST.cmp a)
  = fun x y -> I.v (cmp x y)
