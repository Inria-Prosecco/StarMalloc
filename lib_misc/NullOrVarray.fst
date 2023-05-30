module NullOrVarray

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory

module A = Steel.Array

open SteelOptUtils

let array = Steel.ST.Array.array

let null_or_varray (#a:Type) (r:array a)
  : vprop
  = c2 #(Seq.lseq a (A.length r))
    (not (A.is_null r)) (A.varray r)

let null_or_varray_t (#a: Type) (r:array a)
  : Lemma
  (t_of (null_or_varray #a r) == option (Seq.lseq a (A.length r)))
  = ()

noextract inline_for_extraction
let intro_null_null_or_varray (#a: Type)
  : Steel (array a)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> A.is_null r)
  =
  sladmit ();
  return (A.null #a)

let elim_null_null_or_varray (#opened:_) (#a: Type) (r: array a)
  : SteelGhost unit opened
  (null_or_varray r)
  (fun _ -> emp)
  (requires fun _ -> A.is_null r)
  (ensures fun _ _ _ -> True)
  =
  sladmit ()
