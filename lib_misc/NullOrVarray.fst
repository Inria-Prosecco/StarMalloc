module NullOrVarray

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory

module A = Steel.Array

let array = Steel.ST.Array.array

let null_or_varray_f (#a: Type)
  (r: array a)
  (v: normal (t_of (if A.is_null r then emp else A.varray r)))
  : Seq.lseq a (A.length r)
  =
  if A.is_null r
  then Seq.empty #a
  else (
    assert (normal (t_of (if A.is_null r then emp else A.varray r))
    == normal (t_of (A.varray r)));
    assert (normal (t_of (A.varray r)) == Seq.lseq a (A.length r));
    let v : normal (t_of (if A.is_null r then emp else A.varray r)) = v in
    let v : normal (t_of (A.varray r)) = v in
    let v : Seq.lseq a (A.length r) = v in
    v
  )

let null_or_varray (#a:Type) (r:array a)
  : vprop
  =
  vrewrite
    (if A.is_null r then emp else A.varray r)
    #(Seq.lseq a (A.length r))
    (null_or_varray_f r)

let null_or_varray_t (#a: Type) (r:array a)
  : Lemma
  (t_of (null_or_varray #a r) == Seq.lseq a (A.length r))
  = ()

noextract inline_for_extraction
let intro_null_null_or_varray (#a: Type)
  : Steel (array a)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> A.is_null r)
  =
  [@inline_let] let r = A.null #a in
  change_equal_slprop
    emp
    (if A.is_null r then emp else A.varray r);
  intro_vrewrite
    (if A.is_null r then emp else A.varray r)
    (null_or_varray_f r);
  ();
  return r

let elim_null_null_or_varray (#opened:_) (#a: Type) (r: array a)
  : SteelGhost unit opened
  (null_or_varray r)
  (fun _ -> emp)
  (requires fun _ -> A.is_null r)
  (ensures fun _ _ _ -> True)
  =
  elim_vrewrite
    (if A.is_null r then emp else A.varray r)
    (null_or_varray_f r);
  change_equal_slprop
    (if A.is_null r then emp else A.varray r)
    emp

module P = Steel.FractionalPermission

let intro_live_null_or_varray (#opened:_) (#a: Type)
  (r: array a)
  : SteelGhost unit opened
  (A.varray r)
  (fun _ -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    let v0 = A.asel r h0 in
    let v1 : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    v0 == v1
  )
  =
  A.varrayp_not_null r P.full_perm;
  change_equal_slprop
    (A.varray r)
    (if A.is_null r then emp else A.varray r);
  intro_vrewrite
    (if A.is_null r then emp else A.varray r)
    (null_or_varray_f r)

let elim_live_null_or_varray (#opened:_) (#a: Type)
  (r: array a)
  : SteelGhost unit opened
  (null_or_varray r)
  (fun _ -> A.varray r)
  (requires fun _ -> not (A.is_null r))
  (ensures fun h0 _ h1 ->
    let v0 : t_of (null_or_varray r)
      = h0 (null_or_varray r) in
    let v1 = A.asel r h1 in
    v0 == v1
  )
  =
  elim_vrewrite
    (if A.is_null r then emp else A.varray r)
    (null_or_varray_f r);
  change_equal_slprop
    (if A.is_null r then emp else A.varray r)
    (A.varray r)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Utils2
let array_u8_alignment_lemma2
  (arr: array U8.t)
  (v1 v2: (v:U32.t{U32.v v > 0}))
  : Lemma
  (requires
    (U32.v v1) % (U32.v v2) == 0 /\
    (not (A.is_null arr) ==> array_u8_alignment arr v1)
  )
  (ensures
    (not (A.is_null arr) ==> array_u8_alignment arr v2)
  )
  =
  if not (A.is_null arr) then
    array_u8_alignment_lemma arr arr v1 v2
  else ()
