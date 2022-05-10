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

//let mk_perm n p : lseq (option perm) n = Seq.create n p
let slu_downgrade (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (j1: nat)
  (j2: nat{j1 <= j2 /\ j2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (subv: lseq a (i2 - i1))
  (f: lseq a (i2 - i1) -> lseq a (j2 - j1))
  : SteelGhostT unit opened
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

let slu_raise (#a: Type0) (#opened:_) (#n: nat)
  (r: array_ref a #n)
  (j1: nat)
  (j2: nat{j1 <= j2 /\ j2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (subv: erased (lseq a (i2 - i1)))
  (f: lseq a (i2 - i1) -> lseq a (j2 - j1))
  : SteelGhostT unit opened
  (pts_to r j1 j2 p (f (reveal subv)))
  (fun _ -> H.pts_to r j1 j2 p (raise_val_seq (f (reveal subv))))
  =
  rewrite_slprop
    (H.pts_to r j1 j2 p (raise_val_seq (f (reveal subv))))
    (pts_to r j1 j2 p (f (reveal subv)))
    (fun m -> assert_norm (
      hp_of (H.pts_to r j1 j2 p (raise_val_seq (f (reveal subv))))
   == hp_of (pts_to r j1 j2 p (f (reveal subv)))
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
  (#subv: erased (lseq a (i2 - i1)))
  : Steel (lseq a (i2 - i1))
  (pts_to #a #n r i1 i2 p subv)
  (fun _ -> pts_to #a #n r i1 i2 p subv)
  (requires fun _ -> True)
  (ensures fun _ subv' _ -> subv' == reveal subv)
  =
  slu_raise r i1 i2 p i1 i2 subv (fun v -> v);
  let subv' = H.read2 n r i1 i2 p #_ in
  let subv' = downgrade_val_seq subv' in
  downgrade_raise_val_bij subv;
  slu_downgrade r i1 i2 p i1 i2 (reveal subv) (fun v -> v);
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
  slu_raise r i1 i2 p i1 i2 subv (fun v -> v);
  H.write2 n r i1 i2 p
    (raise_val_seq subv)
    (raise_val_seq subv_to_write);
  slu_downgrade r i1 i2 p i1 i2 subv_to_write (fun v -> v)

let free_pt (#a: Type) (n:nat)
  (r: array_ref a #n)
  (p: lseq (option perm) n{p == H.full_perm_seq n})
  (#subv: erased (lseq a n))
  : SteelT unit
  (pts_to #a #n r 0 n p subv)
  (fun _ -> emp)
  =
  slu_raise r 0 n p 0 n subv (fun v -> v);
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
  slu_raise r i1 i2 p i1 i2 (reveal subv) (fun v -> v);
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
    i1 i2
    subv
    (fun v -> fst (Seq.split v (j - i1)));
  slu_downgrade r j i2
    (snd (H.split_aux n p j))
    i1 i2
    subv
    (fun v -> snd (Seq.split v (j - i1)));
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
  slu_raise r i1 j p1 i1 j (reveal subv1) (fun v -> v);
  slu_raise r j i2 p2 j i2 (reveal subv2) (fun v -> v);
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
    i1 i2
    (append (reveal subv1) (reveal subv2))
    (fun v -> v);
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

[@@ __steel_reduce__; __reduce__]
let arr (#a: Type0) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  = arrp #a #n r i1 i2 (Seq.create n (Some full_perm))

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
  = arrp_sel r i1 i2 (H.full_perm_seq n)

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

unfold let mk_full_perm (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  : p:lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p}
  =
  let p' = Seq.create (i2 - i1) full_perm in
  H.complete' n i1 i2 p'

[@@ __steel_reduce__; __reduce__]
let varr (#a: Type0) (#n: nat)
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
  = h (varrp r i1 i2 p)

[@@ __steel_reduce__]
let asel (#a: Type0) (#n: nat) (#vp: vprop) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (h: rmem vp{FStar.Tactics.with_tactic selector_tactic (can_be_split vp (varr r i1 i2) /\ True)})
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

let readp (#a: Type0) (n: nat) (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p /\ H.zeroed (i1, i2) p})
  : Steel (lseq a (i2 - i1))
  (varrp r i1 i2 p)
  (fun _ -> varrp r i1 i2 p)
  (requires fun _ -> True)
  (ensures  fun _ subv h1 ->
    subv == reveal (aselp #a #n #(varrp r i1 i2 p) r i1 i2 p h1))
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
  (ensures fun _ v h1 -> asel r i1 i2 h1 == v)
  =
  let v = readp n r i1 i2 (mk_full_perm n i1 i2) in
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
let split (#a: Type0) (#opened:_) (#n: nat)
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

let merge (#a: Type0) (#opened:_) (#n: nat)
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
    (hide (append (reveal v1) (reveal v2)));
  ()


#set-options "--print_implicits"
