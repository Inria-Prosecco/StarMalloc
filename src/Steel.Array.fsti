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

let array_ref (a: Type0) (#n: nat) : Type u#0
  = H.array_ref (U.raise_t a) #n

let null (#a: Type0) (#n: nat)
  = H.null #(U.raise_t a) #n

let is_null (#a: Type0) (#n: nat)
  = H.is_null #(U.raise_t a) #n

#set-options "--print_implicits"

let perm_ok
  (#n: nat)
  //(#[@@@smt_fallback] n: nat)
  = H.perm_ok #n

let raise_val_seq (#a: Type0)
  (#n: nat)
  (s: lseq a n)
  : lseq (U.raise_t a) n
  =
  map_seq_len U.raise_val s;
  map_seq U.raise_val s

let downgrade_val_seq (#a: Type0)
  (#[@@@smt_fallback] n: nat)
  (s: lseq (U.raise_t a) n)
  : lseq a n
  =
  map_seq_len U.downgrade_val s;
  map_seq U.downgrade_val s

let downgrade_raise_val_bij (#a: Type0) (#n: nat) (s: lseq a n)
  : Lemma
  (downgrade_val_seq (raise_val_seq s) == s)
  =
  admit ();
  let s' = raise_val_seq s in
  Classical.forall_intro (map_seq_index U.raise_val s);
  let s'' = downgrade_val_seq s' in
  Classical.forall_intro (map_seq_index U.downgrade_val s');
  ()

let pts_to_sl (#a: Type0)
  (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (subv: lseq a (i2 - i1))
  =
  let subv' = raise_val_seq subv in
  H.pts_to_sl n r i1 i2 p subv'

let raise_val_inj (#a: Type) (x y: a)
  : Lemma
  (requires U.raise_val x == U.raise_val y)
  (ensures x == y)
  =
  U.downgrade_val_raise_val x;
  U.downgrade_val_raise_val y

let raise_val_seq_inj (#a: Type) (#n: nat) (x y: lseq a n)
  : Lemma
  (requires
    raise_val_seq x == raise_val_seq y
  )
  (ensures x == y)
  =
  let x' = raise_val_seq x in
  let y' = raise_val_seq y in
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
  Seq.lemma_eq_intro x y

let pts_to_ref_injective (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p1 p2: (p:lseq (option perm) n{perm_ok p}))
  (subv1 subv2: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma
    (requires Mem.interp (
      pts_to_sl r i1 i2 p1 subv1 `Mem.star`
      pts_to_sl r i1 i2 p2 subv2) m)
    (ensures subv1 == subv2)
  =
  let subv1' = raise_val_seq subv1 in
  let subv2' = raise_val_seq subv2 in
  H.pts_to_ref_injective r i1 i2 p1 p2 subv1' subv2' m;
  raise_val_seq_inj subv1 subv2

let pts_to_not_null (#a:Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (subv: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl r i1 i2 p subv) m)
          (ensures r =!= null)
  =
  let subv' = raise_val_seq subv in
  H.pts_to_not_null r i1 i2 p subv' m

let aux_sl (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (subv1 subv2: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma
  (requires
    Mem.interp (pts_to_sl r i1 i2 p subv1) m /\
    Mem.interp (pts_to_sl r i1 i2 p subv2) m
  )
  (ensures subv1 == subv2)
  =
  let subv1' : lseq (U.raise_t a) (i2 - i1)
    = raise_val_seq subv1 in
  let subv2' : lseq (U.raise_t a) (i2 - i1)
    = raise_val_seq subv2 in
  assert (Mem.interp (
    H.pts_to_sl n r i1 i2 p subv1'
  ) m);
  assert (Mem.interp (
    H.pts_to_sl n r i1 i2 p subv2'
  ) m);
  H.aux_sl r i1 i2 p subv1' subv2' m;
  raise_val_seq_inj subv1 subv2

let pts_to_witinv (#a:Type) (#n: nat)
  (r:array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
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
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (subv: lseq a (i2 - i1))
  : vprop
  = to_vprop (pts_to_sl r i1 i2 p subv)

let pts_to_injective_eq (#a: Type)
  (#n: nat)
  (#opened:Mem.inames)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 < n})
  (p1 p2: (p:lseq (option perm) n{perm_ok p}))
  (subv1 subv2: lseq a (i2 - i1))
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

//let mk_perm n p : lseq (option perm) n = Seq.create n p
let slu_downgrade (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (j1: nat)
  (j2: nat{j1 <= j2 /\ j2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (subv: lseq a (i2 - i1))
  (f: lseq a (i2 - i1) -> lseq a (j2 - j1))
  : SteelT unit
  (H.pts_to r j1 j2 p (raise_val_seq (f subv)))
  (fun _ -> pts_to r j1 j2 p (f subv))
  =
  rewrite_slprop
    (H.pts_to r j1 j2 p (raise_val_seq (f subv)))
    (pts_to r j1 j2 p (f subv))
    (fun m -> assert_norm (
      hp_of (H.pts_to r j1 j2 p (raise_val_seq (f subv)))
   == hp_of (pts_to r j1 j2 p (f subv))
    ))

let slu_raise (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (j1: nat)
  (j2: nat{j1 <= j2 /\ j2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (subv: lseq a (i2 - i1))
  (f: lseq a (i2 - i1) -> lseq a (j2 - j1))
  : SteelT unit
  (pts_to r j1 j2 p (f subv))
  (fun _ -> H.pts_to r j1 j2 p (raise_val_seq (f subv)))
  =
  rewrite_slprop
    (H.pts_to r j1 j2 p (raise_val_seq (f subv)))
    (pts_to r j1 j2 p (f subv))
    (fun m -> assert_norm (
      hp_of (H.pts_to r j1 j2 p (raise_val_seq (f subv)))
   == hp_of (pts_to r j1 j2 p (f subv))
    ))

let alloc_pt (#a: Type0)
  (n: nat)
  (v: lseq a n)
  : Steel
  (array_ref a #n)
  emp
  (fun r -> pts_to r 0 n (H.full_perm_seq n) v)
  (requires fun _ -> True)
  (ensures fun _ r _ -> not (is_null r))
  =
  let r = H.alloc2 n (raise_val_seq v) in
  slu_downgrade r 0 n (H.full_perm_seq n) 0 n v (fun v -> v);
  return r

let read_pt (#a: Type0) (n:nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  (#subv: lseq a (i2 - i1))
  : Steel (lseq a (i2 - i1))
  (pts_to #a #n r i1 i2 p subv)
  (fun _ -> pts_to #a #n r i1 i2 p subv)
  (requires fun _ -> True)
  (ensures fun _ subv' _ -> subv' == subv)
  =
  slu_raise r i1 i2 p i1 i2 subv (fun v -> v);
  let subv' = H.read2 n r i1 i2 p #_ in
  let subv' = downgrade_val_seq subv' in
  downgrade_raise_val_bij subv;
  slu_downgrade r i1 i2 p i1 i2 subv (fun v -> v);
  return subv'

let write_pt (#a: Type0) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{
    perm_ok p /\ H.zeroed (i1, i2) p /\ H.full_p (i1, i2) p})
  (subv: lseq a (i2 - i1))
  (subv_to_write: lseq a (i2 - i1))
  : SteelT unit
  (pts_to #a #n r i1 i2 p subv)
  (fun _ -> pts_to #a #n r i1 i2 p subv_to_write)
  =
  slu_raise r i1 i2 p i1 i2 subv (fun v -> v);
  H.write2 n r i1 i2 p
    (raise_val_seq subv)
    (raise_val_seq subv_to_write);
  slu_downgrade r i1 i2 p i1 i2 subv_to_write (fun v -> v)

let free_pt (#a: Type) (n:nat)
  (r: array_ref a #n)
  (p: lseq (option perm) n{p == H.full_perm_seq n})
  (subv: lseq a n)
  : SteelT unit
  (pts_to #a #n r 0 n p subv)
  (fun _ -> emp)
  =
  slu_raise r 0 n p 0 n subv (fun v -> v);
  H.free2 n r p (raise_val_seq subv)

let split_pt (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  (subv: lseq a (i2 - i1))
  : SteelT unit
  (pts_to #a #n r i1 i2 p subv)
  (fun _ ->
    pts_to #a #n r i1 j
      (fst (H.split_aux n p j))
      (fst (Seq.split subv (j - i1)))
    `star`
    pts_to #a #n r j i2
      (snd (H.split_aux n p j))
      (snd (Seq.split subv (j - i1)))
  )
  =
  slu_raise r i1 i2 p i1 i2 subv (fun v -> v);
  H.split2 n r i1 i2 j p (raise_val_seq subv);
  slassert (
      (H.pts_to r i1 j
      (fst (H.split_aux n p j))
      (fst (Seq.split (raise_val_seq subv) (j - i1))))
     `star`
      (H.pts_to r j i2
      (snd (H.split_aux n p j))
      (snd (Seq.split (raise_val_seq subv) (j - i1))))
  );
  sladmit ();
  slu_downgrade r i1 j
    (fst (H.split_aux n p j))
    i1 i2
    subv
    (fun v -> fst (Seq.split v (j - i1)));
  slu_downgrade r j i2
    (snd (H.split_aux n p j))
    i1 i2
    subv
    (fun v -> snd (Seq.split v (j - i1)));
  ()

let merge_pt (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p1: lseq (option perm) n{perm_ok p1 /\ H.zeroed (i1, j) p1})
  (subv1: lseq a (j - i1))
  (p2: lseq (option perm) n{perm_ok p2 /\ H.zeroed (j, i2) p2})
  (subv2: lseq a (i2 - j))
  (_: unit{H.composable
    (H.complete n i1 j p1 (raise_val_seq subv1), p1)
    (H.complete n j i2 p2 (raise_val_seq subv2), p2)})
  : SteelT unit
  (pts_to #a #n r i1 j p1 subv1 `star`
  pts_to #a #n r j i2 p2 subv2)
  //(fun _ -> emp)
  (fun _ ->
    //admit ();
    map_seq2_len H.f2 p1 p2;
    let v1 = H.complete n i1 j p1 (raise_val_seq subv1) in
    let v2 = H.complete n j i2 p2 (raise_val_seq subv2) in
    assert (H.composable (v1, p1) (v2, p2));
    assert (map_seq2 H.f2 p1 p2 == snd (H.op (v1, p1) (v2, p2)));
    assert (perm_ok #n (map_seq2 H.f2 p1 p2));
    assert (H.perm_ok #n (map_seq2 H.f2 p1 p2));
    assert (Seq.length (append subv1 subv2) == i2 - i1);
    pts_to #a #n r i1 i2
      //(map_seq2 H.f2 p1 p2)
      (H.full_perm_seq n)
      (append subv1 subv2)
  )
  =
  sladmit ()