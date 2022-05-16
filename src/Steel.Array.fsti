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
module U32 = FStar.UInt32

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
  let s' = raise_val_seq s in
  map_seq_len U.raise_val s;
  Classical.forall_intro (map_seq_index U.raise_val s);
  let s'' = downgrade_val_seq s' in
  map_seq_len U.downgrade_val s';
  Classical.forall_intro (map_seq_index U.downgrade_val s');
  assert (forall (i:nat{i < n}).
    index s'' i == U.downgrade_val (U.raise_val (index s i)));
  Seq.lemma_eq_intro s s''

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

let raise_val_seq_move_split (#a: Type) (#n: nat)
  (s: lseq a n) (j: nat{j <= n})
  : Lemma
  (ensures (
    let s1, s2 = Seq.split (raise_val_seq s) j in
    s1 == raise_val_seq #a #j (fst (Seq.split s j)) /\
    s2 == raise_val_seq #a #(n - j) (snd (Seq.split s j))
  ))
  =
  let s1, s2 = Seq.split (raise_val_seq s) j in
  Seq.lemma_split (raise_val_seq s) j;
  assert (append s1 s2 == raise_val_seq s);
  let t1', t2' = Seq.split s j in
  Seq.lemma_split s j;
  let t1 = raise_val_seq #a #j t1' in
  let t2 = raise_val_seq #a #(n - j) t2' in
  assert (t1 == map_seq U.raise_val t1');
  assert (t2 == map_seq U.raise_val t2');
  assert (raise_val_seq s == map_seq U.raise_val s);
  Seq.map_seq_append U.raise_val t1' t2';
  assert (raise_val_seq s == Seq.append t1 t2);
  assert (Seq.equal (append s1 s2) (append t1 t2));
  Seq.lemma_eq_intro t1 s1;
  Seq.lemma_eq_intro t2 s2;
  assert (s1 == t1);
  assert (s2 == t2)

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
  ([@@@smt_fallback] subv: lseq a (i2 - i1))
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

let slu_downgrade (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (subv: lseq a (i2 - i1))
  : SteelGhostT unit opened
  (H.pts_to r i1 i2 p (raise_val_seq subv))
  (fun _ -> pts_to r i1 i2 p subv)
  =
  rewrite_slprop
    (H.pts_to r i1 i2 p (raise_val_seq subv))
    (pts_to r i1 i2 p subv)
    (fun m -> assert_norm (
      hp_of (H.pts_to r i1 i2 p (raise_val_seq subv))
   == hp_of (pts_to r i1 i2 p subv)
    ))

let slu_raise (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (subv: erased (lseq a (i2 - i1)))
  : SteelGhostT unit opened
  (pts_to r i1 i2 p (reveal subv))
  (fun _ -> H.pts_to r i1 i2 p (raise_val_seq (reveal subv)))
  =
  rewrite_slprop
    (H.pts_to r i1 i2 p (raise_val_seq (reveal subv)))
    (pts_to r i1 i2 p (reveal subv))
    (fun m -> assert_norm (
      hp_of (H.pts_to r i1 i2 p (raise_val_seq (reveal subv)))
   == hp_of (pts_to r i1 i2 p (reveal subv))
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
  slu_downgrade r 0 n (H.full_perm_seq n) v;
  return r

let read_pt (#a: Type0) (n:nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  (#subv: erased (lseq a (i2 - i1)))
  : Steel (lseq a (i2 - i1))
  (pts_to #a #n r i1 i2 p subv)
  (fun _ -> pts_to #a #n r i1 i2 p subv)
  (requires fun _ -> True)
  (ensures fun _ subv' _ -> subv' == reveal subv)
  =
  slu_raise r i1 i2 p subv;
  let subv' = H.read2 n r i1 i2 p #_ in
  let subv' = downgrade_val_seq subv' in
  downgrade_raise_val_bij subv;
  slu_downgrade r i1 i2 p (reveal subv);
  return subv'

let write_pt (#a: Type0) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{
    perm_ok p /\ H.zeroed (i1, i2) p /\ H.full_p (i1, i2) p})
  (subv: erased (lseq a (i2 - i1)))
  (subv_to_write: lseq a (i2 - i1))
  : SteelT unit
  (pts_to #a #n r i1 i2 p subv)
  (fun _ -> pts_to #a #n r i1 i2 p subv_to_write)
  =
  slu_raise r i1 i2 p subv;
  H.write2 n r i1 i2 p
    (raise_val_seq subv)
    (raise_val_seq subv_to_write);
  slu_downgrade r i1 i2 p subv_to_write

let free_pt (#a: Type) (n:nat)
  (r: array_ref a #n)
  (p: lseq (option perm) n{p == H.full_perm_seq n})
  (#subv: erased (lseq a n))
  : SteelT unit
  (pts_to #a #n r 0 n p subv)
  (fun _ -> emp)
  =
  slu_raise r 0 n p subv;
  H.free2 n r p (raise_val_seq subv)

let pts_to_sl_lemma (#a: Type)
  (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (x y: lseq (U.raise_t a) (i2 - i1))
  : Lemma
  (requires x == y)
  (ensures H.pts_to_sl n r i1 i2 p x == H.pts_to_sl n r i1 i2 p y)
  =
  ()

let split_pt_lemma1 (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  (subv: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma
  (requires Mem.interp (
      H.pts_to_sl n r i1 j
      (fst (H.split_aux n p j))
      (fst (Seq.split (raise_val_seq subv) (j - i1)))
  ) m)
  (ensures Mem.interp (
      H.pts_to_sl n r i1 j
      (fst (H.split_aux n p j))
      (raise_val_seq #a #(j - i1) (fst (Seq.split subv (j - i1))))
  ) m)
  =
  raise_val_seq_move_split subv (j - i1);
  assert (
    fst (Seq.split (raise_val_seq subv) (j - i1))
    ==
    raise_val_seq #a #(j - i1) (fst (Seq.split subv (j - i1)))
  );
  pts_to_sl_lemma n r i1 j
    (fst (H.split_aux n p j))
    (fst (Seq.split (raise_val_seq subv) (j - i1)))
    (raise_val_seq #a #(j - i1) (fst (Seq.split subv (j - i1))))

let split_pt_lemma2 (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  (subv: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma
  (requires Mem.interp (
      H.pts_to_sl n r j i2
      (snd (H.split_aux n p j))
      (snd (Seq.split (raise_val_seq subv) (j - i1)))
  ) m)
  (ensures Mem.interp (
      H.pts_to_sl n r j i2
      (snd (H.split_aux n p j))
      (raise_val_seq #a #(i2 - j) (snd (Seq.split subv (j - i1))))
  ) m)
  =
  raise_val_seq_move_split subv (j - i1);
  assert (
    snd (Seq.split (raise_val_seq subv) (j - i1))
    ==
    raise_val_seq #a #(i2 - j) (snd (Seq.split subv (j - i1)))
  );
  pts_to_sl_lemma n r j i2
    (snd (H.split_aux n p j))
    (snd (Seq.split (raise_val_seq subv) (j - i1)))
    (raise_val_seq #a #(i2 - j) (snd (Seq.split subv (j - i1))))

#push-options "--z3rlimit 30 --print_implicits"
//#push-options "--print_implicits"

let split_pt (#a: Type) (#opened:_) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  (subv: erased (lseq a (i2 - i1)))
  : SteelGhostT unit opened
  (pts_to #a #n r i1 i2 p (reveal subv))
  (fun _ ->
    pts_to #a #n r i1 j
      (fst (H.split_aux n p j))
      (fst (Seq.split (reveal subv) (j - i1)))
    `star`
    pts_to #a #n r j i2
      (snd (H.split_aux n p j))
      (snd (Seq.split (reveal subv) (j - i1)))
  )
  =
  slu_raise r i1 i2 p (reveal subv);
  H.split2 n r i1 i2 j p (hide (raise_val_seq (reveal subv)));
  slassert (
      (H.pts_to r i1 j
      (fst (H.split_aux n p j))
      (fst (Seq.split (raise_val_seq (reveal subv)) (j - i1))))
     `star`
      (H.pts_to r j i2
      (snd (H.split_aux n p j))
      (snd (Seq.split (raise_val_seq (reveal subv)) (j - i1))))
  );
  rewrite_slprop
      (H.pts_to r i1 j
      (fst (H.split_aux n p j))
      (fst (Seq.split (raise_val_seq (reveal subv)) (j - i1))))
      (H.pts_to r i1 j
      (fst (H.split_aux n p j))
      (raise_val_seq #a #(j - i1) (fst (Seq.split (reveal subv) (j - i1)))))
      (fun m -> split_pt_lemma1 n r i1 i2 j p (reveal subv) m);
  rewrite_slprop
      (H.pts_to r j i2
      (snd (H.split_aux n p j))
      (snd (Seq.split (raise_val_seq (reveal subv)) (j - i1))))
      (H.pts_to r j i2
      (snd (H.split_aux n p j))
      (raise_val_seq #a #(i2 - j) (snd (Seq.split (reveal subv) (j - i1)))))
      (fun m -> split_pt_lemma2 n r i1 i2 j p (reveal subv) m);
  slu_downgrade r i1 j
    (fst (H.split_aux n p j))
    (fst (Seq.split subv (j - i1)));
  slu_downgrade r j i2
    (snd (H.split_aux n p j))
    (snd (Seq.split subv (j - i1)));
  ()
#pop-options

let merge_pt_lemma (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p1: lseq (option perm) n{perm_ok p1 /\ H.zeroed (i1, j) p1})
  (subv1: erased (lseq a (j - i1)))
  (p2: lseq (option perm) n{perm_ok p2 /\ H.zeroed (j, i2) p2})
  (subv2: erased (lseq a (i2 - j)))
  (m:Mem.mem)
  : Lemma
  (requires (
    map_seq2_len H.f2 p1 p2;
    H.disjoint_perms_are_composable n i1 i2 j p1 p2;
    Mem.interp (
    (H.pts_to_sl n r i1 i2
      (map_seq2 H.f2 p1 p2)
      (append (raise_val_seq (reveal subv1))
              (raise_val_seq (reveal subv2))))
  ) m))
  (ensures Mem.interp (
    (H.pts_to_sl n r i1 i2
      (map_seq2 H.f2 p1 p2)
      (raise_val_seq (append (reveal subv1) (reveal subv2))))
  ) m)
  =
  //Seq.lemma_len_append (reveal subv1) (reveal subv2);
  let subv : lseq a (i2 - i1) = append (reveal subv1) (reveal subv2) in
  Seq.lemma_split subv (j - i1);
  //raise_val_seq_move_split #a #(i2 - i1) subv (j - i1);
  map_seq_append U.raise_val (reveal subv1) (reveal subv2);
  assert (
    (raise_val_seq subv)
    ==
    (append (raise_val_seq (reveal subv1))
              (raise_val_seq (reveal subv2)))
  );
  map_seq2_len H.f2 p1 p2;
  H.disjoint_perms_are_composable n i1 i2 j p1 p2;
  pts_to_sl_lemma n r i1 i2 (map_seq2 H.f2 p1 p2)
    (raise_val_seq subv)
    (append (raise_val_seq (reveal subv1))
              (raise_val_seq (reveal subv2)))

let merge_pt (#a: Type) (#opened:_) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p1: lseq (option perm) n{perm_ok p1 /\ H.zeroed (i1, j) p1})
  (subv1: erased (lseq a (j - i1)))
  (p2: lseq (option perm) n{perm_ok p2 /\ H.zeroed (j, i2) p2})
  (subv2: erased (lseq a (i2 - j)))
  : SteelGhostT unit opened
  (pts_to #a #n r i1 j p1 (reveal subv1) `star`
  pts_to #a #n r j i2 p2 (reveal subv2))
  (fun _ ->
    map_seq2_len H.f2 p1 p2;
    let subv1' = raise_val_seq subv1 in
    let subv2' = raise_val_seq subv2 in
    let v1 = H.complete n i1 j p1 subv1' in
    let v2 = H.complete n j i2 p2 subv2' in
    H.disjoint_is_composable n i1 i2 j p1 subv1' p2 subv2';
    assert (H.composable (v1, p1) (v2, p2));
    assert (map_seq2 H.f2 p1 p2 == snd (H.op (v1, p1) (v2, p2)));
    assert (perm_ok #n (map_seq2 H.f2 p1 p2));
    assert (H.perm_ok #n (map_seq2 H.f2 p1 p2));
    assert (Seq.length (append subv1 subv2) == i2 - i1);
    pts_to #a #n r i1 i2
      (map_seq2 H.f2 p1 p2)
      (append (reveal subv1) (reveal subv2))
  )
  =
  slu_raise r i1 j p1 (reveal subv1);
  slu_raise r j i2 p2 (reveal subv2);
  H.merge2 n r i1 i2 j
    p1 (raise_val_seq (reveal subv1))
    p2 (raise_val_seq (reveal subv2));
  map_seq2_len H.f2 p1 p2;
  H.disjoint_perms_are_composable n i1 i2 j p1 p2;
  rewrite_slprop
    (H.pts_to r i1 i2
      (map_seq2 H.f2 p1 p2)
      (append (raise_val_seq (reveal subv1))
              (raise_val_seq (reveal subv2))))
    (H.pts_to r i1 i2
      (map_seq2 H.f2 p1 p2)
      (raise_val_seq (append (reveal subv1) (reveal subv2))))
    (fun m -> merge_pt_lemma n r i1 i2 j p1 subv1 p2 subv2 m);
  slu_downgrade r i1 i2
    (map_seq2 H.f2 p1 p2)
    (append (reveal subv1) (reveal subv2));
  ()

let arrp (#a: Type0) (#n: nat)
  //([@@@smt_fallback] i1: nat)
  //([@@@smt_fallback] i2: nat{i1 <= i2 /\ i2 <= n})
  //([@@@smt_fallback] p: lseq (option perm) n{perm_ok p})
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  = Mem.h_exists (pts_to_sl r i1 i2 p)

unfold let mk_full_perm (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : p:lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p}
  =
  let p' = Seq.create (i2 - i1) full_perm in
  H.complete' n i1 i2 p'

[@@ __steel_reduce__; __reduce__]
let arr (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  = arrp #a #n r i1 i2 (mk_full_perm n i1 i2)

let arrp_sel' (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  : selector' (lseq a (i2 - i1)) (arrp r i1 i2 p)
  = fun h -> Mem.id_elim_exists #(lseq a (i2 - i1)) (pts_to_sl r i1 i2 p) h

let arrp_sel_depends_only_on (#a:Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (m0:Mem.hmem (arrp r i1 i2 p))
  (m1:Mem.mem{Mem.disjoint m0 m1})
  : Lemma (arrp_sel' r i1 i2 p m0 == arrp_sel' r i1 i2 p (Mem.join m0 m1))
  =
  let x = reveal (Mem.id_elim_exists (pts_to_sl r i1 i2 p) m0) in
  let y = reveal (Mem.id_elim_exists (pts_to_sl r i1 i2 p) (Mem.join m0 m1)) in
  pts_to_witinv r i1 i2 p;
  Mem.elim_wi (pts_to_sl r i1 i2 p) x y (Mem.join m0 m1)

let arrp_sel_depends_only_on_core (#a:Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (m0:Mem.hmem (arrp r i1 i2 p))
  : Lemma (arrp_sel' r i1 i2 p m0 == arrp_sel' r i1 i2 p
    (Mem.core_mem m0))
  =
  let x = reveal (Mem.id_elim_exists (pts_to_sl r i1 i2 p) m0) in
  let y = reveal (Mem.id_elim_exists (pts_to_sl r i1 i2 p)
    (Mem.core_mem m0)) in
  pts_to_witinv r i1 i2 p;
  Mem.elim_wi (pts_to_sl r i1 i2 p) x y (Mem.core_mem m0)

let arrp_sel (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  : selector (lseq a (i2 - i1)) (arrp r i1 i2 p)
  =
  Classical.forall_intro_2 (arrp_sel_depends_only_on r i1 i2 p);
  Classical.forall_intro (arrp_sel_depends_only_on_core r i1 i2 p);
  arrp_sel' r i1 i2 p

[@@ __steel_reduce__; __reduce__]
let arr_sel (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : selector (lseq a (i2 - i1)) (arr r i1 i2)
  = arrp_sel r i1 i2 (mk_full_perm n i1 i2)

[@@ __steel_reduce__]
let varr' (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  : vprop'
  = {
    hp = arrp r i1 i2 p;
    t = lseq a (i2 - i1);
    sel = arrp_sel r i1 i2 p;
  }

[@@ __steel_reduce__; __reduce__]
let varrp (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  = VUnit (varr' r i1 i2 p)

[@@ __steel_reduce__; __reduce__]
unfold let varr (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  = varrp r i1 i2 (mk_full_perm n i1 i2)

[@@ __steel_reduce__]
let aselp (#a: Type0) (#n: nat) (#vp: vprop) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (h: rmem vp{FStar.Tactics.with_tactic selector_tactic (can_be_split vp (varrp r i1 i2 p) /\ True)})
  : GTot (lseq a (i2 - i1))
  = h (varrp r i1 i2 p)

[@@ __steel_reduce__]
unfold let asel (#a: Type0) (#n: nat) (#vp: vprop) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (h: rmem vp{FStar.Tactics.with_tactic selector_tactic (can_be_split vp (varr r i1 i2) /\ True)})
  : GTot (lseq a (i2 - i1))
  = h (varr r i1 i2)

let intro_varr_lemma (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (v: erased (lseq a (i2 - i1)))
  (m: Mem.mem)
  : Lemma
  (requires Mem.interp (pts_to_sl r i1 i2 p v) m)
  (ensures Mem.interp (arrp r i1 i2 p) m /\ arrp_sel r i1 i2 p m == reveal v)
  =
  Mem.intro_h_exists (reveal v) (pts_to_sl r i1 i2 p) m;
  pts_to_witinv r i1 i2 p

let elim_varr_lemma (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (v: erased (lseq a (i2 - i1)))
  (m: Mem.mem)
  : Lemma
  (requires Mem.interp (arrp r i1 i2 p) m /\ arrp_sel r i1 i2 p m == reveal v)
  (ensures Mem.interp (pts_to_sl r i1 i2 p v) m)
  =
  Mem.elim_h_exists (pts_to_sl r i1 i2 p) m;
  pts_to_witinv r i1 i2 p

let intro_varr (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (v: erased (lseq a (i2 - i1)))
  : SteelGhost unit opened
  (pts_to r i1 i2 p v)
  (fun _ -> varrp r i1 i2 p)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> h1 (varrp r i1 i2 p) == reveal v)
  =
  change_slprop_2
    (pts_to r i1 i2 p v)
    (varrp r i1  i2 p)
    v
    (intro_varr_lemma r i1 i2 p v)

let elim_varr (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  : SteelGhost (erased (lseq a (i2 - i1))) opened
  (varrp r i1 i2 p)
  (fun v -> pts_to r i1 i2 p v)
  (requires fun _ -> True)
  (ensures fun h0 v _ -> reveal v == h0 (varrp r i1 i2 p))
  =
  let v2 : erased (t_of (varrp r i1 i2 p))
    = gget (varrp r i1 i2 p) in
  let v1 : erased (t_of (pts_to r i1 i2 p v2))
    = () in
  change_slprop
    (varrp r i1 i2 p)
    (pts_to r i1 i2 p v2)
    v2
    v1
    (elim_varr_lemma r i1 i2 p v2);
  v2

let full_perm_seq_lemma (n: nat)
  : Lemma
  (H.full_perm_seq n == mk_full_perm n 0 n)
  =
  Seq.lemma_eq_intro
    (H.full_perm_seq n)
    (mk_full_perm n 0 n)

let malloc (#a: Type0) (n: nat) (v: lseq a n)
  : Steel (array_ref a #n)
  emp
  (fun r -> varr r 0 n)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> asel r 0 n h1 == v /\ not (is_null r))
  =
  let r = alloc_pt n v in
  rewrite_slprop
    (pts_to r 0 n (H.full_perm_seq n) v)
    (pts_to r 0 n (mk_full_perm n 0 n) v)
    (fun _ -> full_perm_seq_lemma n);
  intro_varr r 0 n (mk_full_perm n 0 n) (hide v);
  return r

let free (#a: Type0) (#n: nat) (r: array_ref a #n)
  : SteelT unit
  (varr r 0 n)
  (fun _ -> emp)
  =
  rewrite_slprop
    (varrp r 0 n (mk_full_perm n 0 n))
    (varrp r 0 n (H.full_perm_seq n))
    (fun _ -> full_perm_seq_lemma n);
  let v = elim_varr r 0 n (H.full_perm_seq n) in
      free_pt #a n r (H.full_perm_seq n) #_

let readp_seq (#a: Type0) (n: nat) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  : Steel (lseq a (i2 - i1))
  (varrp r i1 i2 p)
  (fun _ -> varrp r i1 i2 p)
  (requires fun _ -> True)
  (ensures  fun h0 v h1 ->
    v == reveal (aselp #a #n #(varrp r i1 i2 p) r i1 i2 p h1) /\
    aselp r i1 i2 p h0 == aselp r i1 i2 p h1)
  =
  let v = elim_varr r i1 i2 p in
  let content = read_pt n r i1 i2 p #v in
  intro_varr r i1 i2 p v;
  return content

let read_seq (#a: Type0) (#n: nat) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : Steel (lseq a (i2 - i1))
  (varr r i1 i2)
  (fun _ -> varr r i1 i2)
  (requires fun _ -> True)
  (ensures fun h0 v h1 ->
    v == asel r i1 i2 h1 /\
    asel r i1 i2 h0 == asel r i1 i2 h1)
  =
  let v = readp_seq n r i1 i2 (mk_full_perm n i1 i2) in
  return v

let write_seq (#a: Type0) (#n: nat) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (v_write: lseq a (i2 - i1))
  : Steel unit
  (varr r i1 i2)
  (fun _ -> varr r i1 i2)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> asel r i1 i2 h1 == v_write)
  =
  let v = elim_varr r i1 i2 (mk_full_perm n i1 i2) in
  write_pt n r i1 i2 (mk_full_perm n i1 i2) v v_write;
  intro_varr r i1 i2 (mk_full_perm n i1 i2) v_write

#push-options "--z3rlimit 20"
let splitp (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  : SteelGhost unit opened
  (varrp r i1 i2 p)
  (fun _ ->
    varrp r i1 j (fst (H.split_aux n p j)) `star`
    varrp r j i2 (snd (H.split_aux n p j)))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    aselp r i1 i2 p h0
    == append
      (aselp r i1 j (fst (H.split_aux n p j)) h1)
      (aselp r j i2 (snd (H.split_aux n p j)) h1)
  )
  =
  let v = elim_varr r i1 i2 p in
  slassert (pts_to #a #n r i1 i2 p (reveal v));
  split_pt n r i1 i2 j p v;
  slassert (
    pts_to #a #n r i1 j
      (fst (H.split_aux n p j))
      (fst (Seq.split (reveal v) (j - i1)))
    `star`
    pts_to #a #n r j i2
      (snd (H.split_aux n p j))
      (snd (Seq.split (reveal v) (j - i1)))
  );
  intro_varr #a #_ #n r i1 j (fst (H.split_aux n p j))
    (hide (fst (Seq.split (reveal v) (j - i1))));
  intro_varr #a #_ #n r j i2 (snd (H.split_aux n p j))
    (hide (snd (Seq.split (reveal v) (j - i1))));
  Seq.lemma_split (reveal v) (j - i1);
  ()
#pop-options

let split_aux_full_perm_lemma (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  : Lemma
  (fst (H.split_aux n (mk_full_perm n i1 i2) j) == mk_full_perm n i1 j /\
  snd (H.split_aux n (mk_full_perm n i1 i2) j) == mk_full_perm n j i2)
  =
  let p = mk_full_perm n i1 i2 in
  let s1 = fst (H.split_aux n p j) in
  let s2 = snd (H.split_aux n p j) in
  let t1 = mk_full_perm n i1 j in
  let t2 = mk_full_perm n j i2 in
  Seq.lemma_eq_intro s1 t1;
  assert (s1 == t1);
  Seq.lemma_eq_intro s2 t2;
  assert (s2 == t2)

let varrp_to_varr (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : SteelGhost unit opened
  (varrp r i1 i2 (mk_full_perm n i1 i2))
  (fun _ -> varr r i1 i2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    aselp r i1 i2 (mk_full_perm n i1 i2) h0
    ==
    asel r i1 i2 h1
  )
  =
  change_slprop_rel
    (varrp r i1 i2 (mk_full_perm n i1 i2))
    (varr r i1 i2)
    (fun x y -> x == y)
    (fun _ -> ())

let varr_to_varrp (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : SteelGhost unit opened
  (varr r i1 i2)
  (fun _ -> varrp r i1 i2 (mk_full_perm n i1 i2))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    aselp r i1 i2 (mk_full_perm n i1 i2) h1
    ==
    asel r i1 i2 h0
  )
  =
  change_slprop_rel
    (varr r i1 i2)
    (varrp r i1 i2 (mk_full_perm n i1 i2))
    (fun x y -> x == y)
    (fun _ -> ())

#push-options "--z3rlimit 20"
let split (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  : SteelGhost unit opened
  (varr r i1 i2)
  (fun _ ->
    varr r i1 j `star`
    varr r j i2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel r i1 i2 h0
    == append
      (asel r i1 j h1)
      (asel r j i2 h1))
  =
  //let h0 = get () in
  varr_to_varrp r i1 i2;
  //let h1 = get () in
  //assert (asel r i1 i2 h0 == aselp r i1 i2 (mk_full_perm n i1 i2) h1);
  splitp r i1 i2 j (mk_full_perm n i1 i2);
  //let h12 = get () in
  change_slprop_rel
    (varrp r i1 j (fst (H.split_aux n (mk_full_perm n i1 i2) j)) `star`
    varrp r j i2 (snd (H.split_aux n (mk_full_perm n i1 i2) j)))
    (varrp r i1 j (mk_full_perm n i1 j) `star`
    varrp r j i2 (mk_full_perm n j i2))
    (fun x y -> x == y)
    (fun _ -> split_aux_full_perm_lemma n i1 i2 j);
 // let h2 = get () in
 // assert (
 //   aselp r i1 j (fst (H.split_aux n (mk_full_perm n i1 i2) j)) h12
 //   ==
 //   aselp r i1 j (mk_full_perm n i1 j) h2
 // );
 // assert (
 //   aselp r j i2 (snd (H.split_aux n (mk_full_perm n i1 i2) j)) h12
 //   ==
 //   aselp r j i2 (mk_full_perm n j i2) h2
 // );
  varrp_to_varr r i1 j;
  varrp_to_varr r j i2;
  //let h3 = get () in
  //assert (
  //  aselp r i1 j (mk_full_perm n i1 j) h2 == asel r i1 j h3 /\
  //  aselp r j i2 (mk_full_perm n j i2) h2 == asel r j i2 h3
  //)
  ()
#pop-options

let mergep (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p1: lseq (option perm) n{perm_ok p1 /\ H.zeroed (i1, j) p1})
  (p2: lseq (option perm) n{perm_ok p2 /\ H.zeroed (j, i2) p2})
  : SteelGhost unit opened
  (varrp r i1 j p1 `star`
   varrp r j i2 p2)
  (fun _ ->
    map_seq2_len H.f2 p1 p2;
    H.disjoint_perms_are_composable n i1 i2 j p1 p2;
    varrp r i1 i2 (map_seq2 H.f2 p1 p2))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    map_seq2_len H.f2 p1 p2;
    H.disjoint_perms_are_composable n i1 i2 j p1 p2;
    aselp r i1 i2 (map_seq2 H.f2 p1 p2) h1
    == append (aselp r i1 j p1 h0) (aselp r j i2 p2 h0))
  =
  let v1 = elim_varr r i1 j p1 in
  let v2 = elim_varr r j i2 p2 in
  merge_pt n r i1 i2 j p1 v1 p2 v2;
  map_seq2_len H.f2 p1 p2;
  H.disjoint_perms_are_composable n i1 i2 j p1 p2;
  intro_varr #a #_ #n r i1 i2
    (map_seq2 H.f2 p1 p2)
    (hide (append (reveal v1) (reveal v2)))

let merge_aux_mk_full_perm_lemma (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  : Lemma
  (map_seq2_len H.f2
    (mk_full_perm n i1 j)
    (mk_full_perm n j i2);
  map_seq2 H.f2
    (mk_full_perm n i1 j)
    (mk_full_perm n j i2)
  == mk_full_perm n i1 i2)
  =
  let s1 = mk_full_perm n i1 j in
  let s2 = mk_full_perm n j i2 in
  let s = map_seq2 H.f2 s1 s2 in
  map_seq2_len H.f2 s1 s2;
  assert (Seq.length s == n);
  Classical.forall_intro (map_seq2_index H.f2 s1 s2);
  Seq.lemma_eq_intro s (mk_full_perm n i1 i2)

#push-options "--z3rlimit 20"
let merge (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  : SteelGhost unit opened
  (varr r i1 j `star`
   varr r j i2)
  (fun _ -> varr r i1 i2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel r i1 i2 h1
    == append
      (asel r i1 j h0)
      (asel r j i2 h0))
  =
  let h0 = get () in
  varr_to_varrp r i1 j;
  varr_to_varrp r j i2;
  let h1 = get () in
  let p1 = mk_full_perm n i1 j in
  let p2 = mk_full_perm n j i2 in
  assert (
    aselp r i1 j p1 h1 == asel r i1 j h0 /\
    aselp r j i2 p2 h1 == asel r j i2 h0
  );
  mergep r i1 i2 j
    (mk_full_perm n i1 j)
    (mk_full_perm n j i2);
  //TODO: file a bug
  //let h2 = get () in
  map_seq2_len H.f2 p1 p2;
  H.disjoint_perms_are_composable n i1 i2 j p1 p2;
  assert (perm_ok #n (map_seq2 H.f2 p1 p2));
  change_slprop_rel
    (varrp r i1 i2 (map_seq2 H.f2
      (mk_full_perm n i1 j)
      (mk_full_perm n j i2)
    ))
    (varrp r i1 i2 (mk_full_perm n i1 i2))
    (fun x y -> x == y)
    (fun _ -> merge_aux_mk_full_perm_lemma n i1 i2 j);
  varrp_to_varr r i1 i2
#pop-options

let append_eq_to_slice_eq (#a: Type) (#n: nat)
  (s: lseq a n)
  (j: nat{j <= n})
  (s1: lseq a j)
  (s2: lseq a (n -j))
  : Lemma
  (requires
    s == append s1 s2)
  (ensures
    s1 == slice s 0 j /\
    s2 == slice s j n)
  =
  let s1', s2' = Seq.split s j in
  Seq.lemma_split s j;
  assert (append s1' s2' == s);
  Seq.lemma_append_inj s1 s2 s1' s2';
  assert (s1 == s1');
  assert (s2 == s2')

#push-options "--z3rlimit 20"
let read (#a: Type0) (#n: nat) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j < i2})
  : Steel a
  (varr r i1 i2)
  (fun _ -> varr r i1 i2)
  (requires fun _ -> n > 0)
  (ensures fun h0 v h1 ->
    Seq.index (asel r i1 i2 h1) (j - i1) == v /\
    asel r i1 i2 h0 == asel r i1 i2 h1)
  =
  let arr : erased (lseq a (i2 - i1)) = gget (varr r i1 i2) in
  split r i1 i2 j;
  let arr1 = gget (varr r i1 j) in
  let arr2 : erased (lseq a (i2 - j)) = gget (varr r j i2) in
  append_eq_to_slice_eq (reveal arr) (j - i1)
    (reveal arr1) (reveal arr2);
  assert (reveal arr1 == slice (reveal arr) 0 (j - i1));
  assert (reveal arr2 == slice (reveal arr) (j - i1) (i2 - i1));
  split r j i2 (j+1);
  let arr21 = gget (varr r j (j+1)) in
  let arr22 = gget (varr r (j+1) i2) in
  append_eq_to_slice_eq (reveal arr2) 1
    (reveal arr21) (reveal arr22);
  assert (reveal arr21 == slice (reveal arr2) 0 1);
  assert (reveal arr22 == slice (reveal arr2) 1 (i2 - j));
  Seq.slice_slice (reveal arr) (j - i1) (i2 - i1) 0 1;
  assert (reveal arr21 == slice (reveal arr) (j - i1) (j - i1 + 1));
  let v' = read_seq r j (j+1) in
  let v = Seq.index v' 0 in
  merge r j i2 (j+1);
  merge r i1 i2 j;
  return v
#pop-options

#push-options "--z3rlimit 20"
let write (#a: Type0) (#n: nat) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 < i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j < i2})
  (v_write: a)
  : Steel unit
  (varr r i1 i2)
  (fun _ -> varr r i1 i2)
  (requires fun _ -> n > 0)
  (ensures fun h0 v h1 ->
    Seq.index (asel r i1 i2 h1) (j - i1) == v_write)
    ///\
    //TODO: missing lemma
    //asel r i1 i2 h1 == Seq.upd (asel r i1 i2 h0) (j - i1) v_write)
  =
  let arr : erased (lseq a (i2 - i1)) = gget (varr r i1 i2) in
  split r i1 i2 j;
  let arr1 = gget (varr r i1 j) in
  let arr2 : erased (lseq a (i2 - j)) = gget (varr r j i2) in
  append_eq_to_slice_eq (reveal arr) (j - i1)
    (reveal arr1) (reveal arr2);
  assert (reveal arr1 == slice (reveal arr) 0 (j - i1));
  assert (reveal arr2 == slice (reveal arr) (j - i1) (i2 - i1));
  split r j i2 (j+1);
  let arr21 = gget (varr r j (j+1)) in
  let arr22 = gget (varr r (j+1) i2) in
  append_eq_to_slice_eq (reveal arr2) 1
    (reveal arr21) (reveal arr22);
  assert (reveal arr21 == slice (reveal arr2) 0 1);
  assert (reveal arr22 == slice (reveal arr2) 1 (i2 - j));
  Seq.slice_slice (reveal arr) (j - i1) (i2 - i1) 0 1;
  assert (reveal arr21 == slice (reveal arr) (j - i1) (j - i1 + 1));
  let v_write' = Seq.create 1 v_write in
  write_seq r j (j+1) v_write';
  merge r j i2 (j+1);
  merge r i1 i2 j;
  return ()
#pop-options

#set-options "--print_implicits"

noeq type array (a: Type0) : Type u#0
  =
  {
    max_length: nat;
    content: array_ref a #max_length;
    idx: nat;
    length: l:nat{idx + l <= max_length};
  }

unfold let get_max_length (#a: Type0) (arr: array a)
  = arr.max_length
unfold let get_content (#a: Type0) (arr: array a)
  = arr.content
unfold let get_i1 (#a: Type0) (arr: array a)
  = arr.idx
unfold let get_i2 (#a: Type0) (arr: array a)
  = arr.idx + arr.length
unfold let get_length (#a: Type0) (arr: array a)
  = arr.length

[@@ __steel_reduce__]
unfold let mk_array (#a: Type0)
  (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : arr:array a{
    get_max_length arr = n /\
    get_content arr == r /\
    get_i1 arr = i1 /\
    get_i2 arr = i2 /\
    get_length arr = i2 - i1
  }
  = {
    max_length = n;
    content = r;
    idx = i1;
    length = i2 - i1;
  }


//[@@ __steel_reduce__; __reduce__]
unfold let varrayp (#a: Type0)
  (arr: array a)
  (p: lseq (option perm) (get_max_length arr){perm_ok p})
  : vprop
  =
  varrp
    (get_content arr)
    (get_i1 arr)
    (get_i2 arr)
    p

//[@@ __steel_reduce__; __reduce__]
unfold let varray (#a: Type0) (arr: array a) : vprop
  =
  varr
    (get_content arr)
    (get_i1 arr)
    (get_i2 arr)

[@@ __steel_reduce__]
let aselp2 (#a: Type0) (#vp: vprop)
  (arr: array a)
  (p: lseq (option perm) (get_max_length arr){perm_ok p})
  (h: rmem vp{FStar.Tactics.with_tactic selector_tactic
    (can_be_split vp (varrayp arr p) /\ True)})
  : GTot (lseq a (get_length arr))
  = h (varrayp arr p)

[@@ __steel_reduce__]
let asel2 (#a: Type0) (#vp: vprop)
  (arr: array a)
  (h: rmem vp{FStar.Tactics.with_tactic selector_tactic
    (can_be_split vp (varray arr) /\ True)})
  : GTot (lseq a (get_length arr))
  = h (varray arr)

let varray_to_varr (#a: Type0) (#opened:_) (arr: array a)
  : SteelGhost unit opened
  (varray arr)
  (fun _ -> varr (get_content arr) (get_i1 arr) (get_i2 arr))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel (get_content arr) (get_i1 arr) (get_i2 arr) h1
    ==
    asel2 arr h0)
  =
  change_slprop_rel
    (varray arr)
    (varr (get_content arr) (get_i1 arr) (get_i2 arr))
    (fun x y -> x == y)
    (fun _ -> ())

let varr_to_varray (#a: Type0) (#opened:_)
  (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : SteelGhost unit opened
  (varr r i1 i2)
  (fun _ -> varray (mk_array n r i1 i2))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel2 (mk_array n r i1 i2) h1
    ==
    asel r i1 i2 h0)
  =
  change_slprop_rel
    (varr r i1 i2)
    (varray (mk_array n r i1 i2))
    (fun x y -> x == y)
    (fun _ -> ())

let malloc2 (#a: Type0) (v: a) (n: U32.t)
  //(v: lseq a n)
  : Steel (array a)
  emp
  (fun arr -> varray arr)
  (requires fun _ -> True)
  (ensures fun _ arr h1 ->
    get_i1 arr = 0 /\
    get_i2 arr = (U32.v n) /\
    get_max_length arr == (U32.v n) /\
    asel2 arr h1 == Seq.create (U32.v n) v /\
    not (is_null (get_content arr)))
  =
  let v = Seq.create (U32.v n) v in
  let r = malloc (U32.v n) v in
  varr_to_varray r 0 (U32.v n);
  let arr = mk_array (U32.v n) r 0 (U32.v n) in
  return arr

let free2 (#a: Type0) (arr: array a)
  : Steel unit
  (varray arr)
  (fun _ -> emp)
  (requires fun _ ->
    get_i1 arr = 0 /\
    get_i2 arr = get_max_length arr)
  (ensures fun _ _ _ -> True)
  =
  varray_to_varr arr;
  change_slprop_rel
    (varr (get_content arr) (get_i1 arr) (get_i2 arr))
    (varr (get_content arr) 0 (get_max_length arr))
    (fun x y -> x == y)
    (fun _ -> ());
  free (get_content arr)

let read2 (#a: Type0)
  (arr: array a)
  (i: U32.t)
  : Steel a
  (varray arr)
  (fun _ -> varray arr)
  (requires fun _ ->
    get_i1 arr <= U32.v i /\
    U32.v i < get_i2 arr)
  (ensures fun h0 v h1 ->
    get_i1 arr <= U32.v i /\
    U32.v i < get_i2 arr /\
    asel2 arr h1 == asel2 arr h0 /\
    Seq.index (asel2 arr h1) ((U32.v i) - get_i1 arr) == v)
  =
  varray_to_varr arr;
  let v = read (get_content arr) (get_i1 arr) (get_i2 arr) (U32.v i) in
  varr_to_varray (get_content arr) (get_i1 arr) (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      (get_i2 arr)))
    (varray arr)
    (fun x y -> x == y)
    (fun _ -> ());
  return v

let write2 (#a: Type0)
  (arr: array a)
  (i: U32.t)
  (v_write: a)
  : Steel unit
  (varray arr)
  (fun _ -> varray arr)
  (requires fun _ ->
    get_i1 arr <= U32.v  i /\
    U32.v i < get_i2 arr)
  (ensures fun h0 v h1 ->
    get_i1 arr <= U32.v i /\
    U32.v i < get_i2 arr /\
    Seq.index (asel2 arr h1) (U32.v i - get_i1 arr) == v_write)
  =
  varray_to_varr arr;
  write (get_content arr) (get_i1 arr) (get_i2 arr) (U32.v i) v_write;
  varr_to_varray (get_content arr) (get_i1 arr) (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      (get_i2 arr)))
    (varray arr)
    (fun x y -> x == y)
    (fun _ -> ());
  return ()

let split_l (#a: Type)
  (arr: array a)
  (i: nat)
  : Pure (array a)
  (requires
    get_i1 arr <= i /\
    i < get_i2 arr)
  (ensures fun arr' ->
    get_i1 arr' = get_i1 arr /\
    get_i2 arr' = i /\
    get_length arr' = i - get_i1 arr)
  =
  {arr with length = i - get_i1 arr}

let split_r (#a: Type)
  (arr: array a)
  (i: nat)
  : Pure (array a)
  (requires
    get_i1 arr <= i /\
    i < get_i2 arr)
  (ensures fun arr' ->
    get_i1 arr' = i /\
    get_i2 arr' = get_i2 arr /\
    get_length arr' = get_i2 arr - i)
  =
  let arr = {arr with length = get_i2 arr - i} in
  {arr with idx = i}

let split2 (#a: Type)
  (arr: array a)
  (i: nat{get_i1 arr <= i /\ i < get_i2 arr})
  : Steel unit
  (varray arr)
  (fun _ -> varray (split_l arr i) `star` varray (split_r arr i))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel2 arr h0
    == Seq.append
      (asel2 (split_l arr i) h1)
      (asel2 (split_r arr i) h1))
  =
  varray_to_varr arr;
  split (get_content arr) (get_i1 arr) (get_i2 arr) i;
  varr_to_varray (get_content arr) (get_i1 arr) i;
  varr_to_varray (get_content arr) i (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      i))
    (varray (split_l arr i))
    (fun x y -> x == y)
    (fun _ -> ());
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      i
      (get_i2 arr)
    ))
    (varray (split_r arr i))
    (fun x y -> x == y)
    (fun _ -> ());
  return ()

let merge2 (#a: Type)
  (arr: array a)
  (i: nat{get_i1 arr <= i /\ i < get_i2 arr})
  : Steel unit
  (varray (split_l arr i) `star` varray (split_r arr i))
  (fun _ -> varray arr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel2 arr h1
    == Seq.append
      (asel2 (split_l arr i) h0)
      (asel2 (split_r arr i) h0))
  =
  varray_to_varr (split_l arr i);
  varray_to_varr (split_r arr i);
  change_slprop_rel
    (varr
      (get_content (split_l arr i))
      (get_i1 (split_l arr i))
      (get_i2 (split_l arr i)))
    (varr (get_content arr) (get_i1 arr) i)
    (fun x y -> x == y)
    (fun _ -> ());
  change_slprop_rel
    (varr
      (get_content (split_r arr i))
      (get_i1 (split_r arr i))
      (get_i2 (split_r arr i)))
    (varr (get_content arr) i (get_i2 arr))
    (fun x y -> x == y)
    (fun _ -> ());
  merge (get_content arr) (get_i1 arr) (get_i2 arr) i;
  varr_to_varray (get_content arr) (get_i1 arr) (get_i2 arr);
  change_slprop_rel
    (varray (mk_array
      (get_max_length arr)
      (get_content arr)
      (get_i1 arr)
      (get_i2 arr)))
    (varray arr)
    (fun x y -> x == y)
    (fun _ -> ());
  return ()
