module Steel.Array

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
//open FStar.Real
//open FStar.PCM
open Steel.FractionalPermission
//module PR = Steel.PCMReference
module Mem = Steel.Memory
module H = Steel.HigherArray
module U = FStar.Universe

#set-options "--ide_id_info_off"

open FStar.Seq
open Seq.Aux

let perm = option perm

let array_ref (a: Type0) (#n: nat) : Type u#0
  = H.array_ref (U.raise_t a) #n

let null (#a: Type0) (#n: nat)
  = H.null #(U.raise_t a) #n

let is_null (#a: Type0) (#n: nat)
  = H.is_null #(U.raise_t a) #n

let pts_to_sl (#a: Type0)
  (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 <= n})
  (p: lseq perm n)
  =
  fun (x: lseq a (i2 - i1 + 1)) ->
    map_seq_len (U.raise_val) x;
    let x' = map_seq (U.raise_val) x in
    H.pts_to_sl n r i1 i2 p x'

let raise_val_inj (#a: Type) (x y: a)
  : Lemma
  (requires U.raise_val x == U.raise_val y)
  (ensures x == y)
  =
  U.downgrade_val_raise_val x;
  U.downgrade_val_raise_val y

let raise_val_seq_inj (#a: Type) (x y: seq a)
  : Lemma
  (requires
    map_seq U.raise_val x == map_seq U.raise_val y
  )
  (ensures x == y)
  =
  map_seq_len U.raise_val x;
  map_seq_len U.raise_val y;
  let x' = map_seq U.raise_val x in
  let y' = map_seq U.raise_val y in
  assert (length x' == length y');
  assert (length x == length y);
  let n = Seq.length x in
  Classical.forall_intro (map_seq_index U.raise_val x);
  Classical.forall_intro (map_seq_index U.raise_val y);
  assert(forall (i:nat{i < n}).
    U.raise_val (index x i) == U.raise_val (index y i) /\
    U.raise_val (index x i) == index x' i /\
    U.raise_val (index y i) == index y' i
  );
  let aux (i: nat{i < n})
  : Lemma
  (index x i == index y i)
  = raise_val_inj (index x i) (index y i)
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro x y;
  ()

let pts_to_ref_injective (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 <= n})
  (p1 p2: lseq perm n)
  (subv1 subv2: lseq a (i2 - i1 + 1))
  (m:Mem.mem)
  : Lemma
    (requires Mem.interp (
      pts_to_sl r i1 i2 p1 subv1 `Mem.star`
      pts_to_sl r i1 i2 p2 subv2) m)
    (ensures subv1 == subv2)
  =
  map_seq_len U.raise_val subv1;
  map_seq_len U.raise_val subv2;
  let subv1' = map_seq U.raise_val subv1 in
  let subv2' = map_seq U.raise_val subv2 in
  H.pts_to_ref_injective r i1 i2 p1 p2 subv1' subv2' m;
  raise_val_seq_inj subv1 subv2

let pts_to_not_null (#a:Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 <= n})
  (p: lseq perm n)
  (subv: lseq a (i2 - i1 + 1))
  (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl r i1 i2 p subv) m)
          (ensures r =!= null)
  =
  map_seq_len U.raise_val subv;
  let subv' = map_seq U.raise_val subv in
  H.pts_to_not_null r i1 i2 p subv' m

let aux_sl (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 <= n})
  (p: lseq perm n)
  (subv1 subv2: lseq a (i2 - i1 + 1))
  (m:Mem.mem)
  : Lemma
  (requires
    Mem.interp (pts_to_sl r i1 i2 p subv1) m /\
    Mem.interp (pts_to_sl r i1 i2 p subv2) m
  )
  (ensures subv1 == subv2)
  =
  map_seq_len U.raise_val subv1;
  map_seq_len U.raise_val subv2;
  let subv1' : lseq (U.raise_t a) (i2 - i1 + 1)
    = map_seq U.raise_val subv1 in
  let subv2' : lseq (U.raise_t a) (i2 - i1 + 1)
    = map_seq U.raise_val subv2 in
  assert (Mem.interp (
    H.pts_to_sl n r i1 i2 p subv1'
  ) m);
  assert (Mem.interp (
    H.pts_to_sl n r i1 i2 p subv2'
  ) m);
  H.aux_sl r i1 i2 p subv1' subv2' m;
  raise_val_seq_inj subv1 subv2;
  ()

let pts_to_witinv (#a:Type) (#n: nat)
  (r:array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 < n})
  (p: lseq perm n)
  : Lemma (Mem.is_witness_invariant (
      pts_to_sl r i1 i2 p
    ))
  =
  Classical.forall_intro_3 (
    Classical.move_requires_3 (
      aux_sl r i1 i2 p
    )
  )

let pts_to (#a: Type) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 <= n})
  ([@@@smt_fallback] p: lseq perm n)
  ([@@@smt_fallback] subv: lseq a (i2 - i1 + 1))
  : vprop
  = to_vprop (pts_to_sl r i1 i2 p subv)

let pts_to_injectiv_eq (#a: Type)
  (#n: nat)
  (#opened:Mem.inames)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 < n})
  (p1 p2: lseq perm n)
  (subv1 subv2: lseq a (i2 - i1 + 1))
  : SteelGhost unit opened
  (pts_to r i1 i2 p1 subv1 `star`
   pts_to r i1 i2 p2 subv2)
  (fun _ -> pts_to r i1 i2 p1 subv1 `star`
   pts_to r i1 i2 p2 subv1)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> subv1 == subv2)
  =
  extract_info_raw
    (pts_to r i1 i2 p1 subv1 `star`
     pts_to r i1 i2 p2 subv2)
    (subv1 == subv2)
    (fun m -> pts_to_ref_injective r i1 i2 p1 p2 subv1 subv2 m);
  rewrite_slprop
    (pts_to r i1 i2 p2 subv2)
    (pts_to r i1 i2 p2 subv1)
    (fun _ -> ())

let mk_perm (n: nat) (p: perm)
  = Seq.create n p

let alloc_pt (#a: Type)
  (n: nat)
  (v: lseq a n)
  : Steel
  (array_ref a #n)
  emp
  (fun r -> pts_to r 0 (n-1) (mk_perm n (Some full_perm)) v)
  (requires fun _ -> True)
  (ensures fun _ r _ -> not (is_null r))
  =
  admit ()
