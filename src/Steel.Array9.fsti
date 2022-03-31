module Steel.Array9

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open FStar.Real
open FStar.PCM
open Steel.FractionalPermission
module RP = Steel.PCMReference
module Mem = Steel.Memory

#set-options "--ide_id_info_off"

open FStar.Seq
open Seq.Aux

(**
First step : seq (a & perm) pcm
Second step : slprop on top of it
Third step : vprop on top of it, introducing idx1/idx2
**)

(** First step **)

let content (a: Type u#1) (#n: nat): Type u#1 = lseq a n & lseq perm n

let array (a: Type u#1) (#n: nat): Type u#1 = option (content a #n)

let comp_prop (#a: Type) (v1 v2: a) (p1 p2: perm)
  = v1 == v2 /\ (sum_perm p1 p2).v <=. one

let composable' (#a: Type) (#n: nat): symrel (content a #n)
  = fun (arr1 arr2: content a #n) ->
  (forall (i:nat{i < n}).
    comp_prop
      (index (fst arr1) i) (index (fst arr2) i)
      (index (snd arr1) i) (index (snd arr2) i)
  )

let composable (#a: Type) (#n: nat): symrel (array a)
  = fun (arr1 arr2: array a)
  -> match arr1, arr2 with
  | None, _
  | _,  None -> True
  | Some c1, Some c2 -> composable' #a #n c1 c2

let f1 (#a: Type) : a -> a -> a
  = fun x y -> x
let f2 : perm -> perm -> perm
  = fun x y -> sum_perm x y

let f (#a: Type) : a & perm -> a & perm -> a & perm =
  fun x y -> f1 (fst x) (fst y), f2 (snd x) (snd y)

let op' (#a: Type) (#n: nat)
  (s1: content a #n) (s2: content a #n)
  : content a #n
  =
  map_seq2_len f1 (fst s1) (fst s2);
  map_seq2_len f2 (snd s1) (snd s2);
  let x1 = map_seq2 f1 (fst s1) (fst s2) in
  let x2 = map_seq2 f2 (snd s1) (snd s2) in
  x1, x2

let op (#a: Type) (#n: nat)
  (arr1 arr2: array a #n)
  : array a #n
  = match arr1, arr2 with
  | None, f
  | f, None -> f
  | Some s1, Some s2 -> Some (op' s1 s2)

let pcm_array' (#a: Type) (#n: nat): pcm' (array a #n) = {
  composable = composable;
  op = op;
  one = None;
}

let lem_commutative (#a: Type) (#n: nat)
  (arr1: array a #n)
  (arr2: array a #n{composable arr1 arr2})
  : Lemma (op arr1 arr2 == op arr2 arr1)
  = match arr1, arr2 with
  | None, _
  | _, None -> ()
  | Some s1, Some s2 ->
      map_seq2_comm f1 (fst s1) (fst s2);
      map_seq2_comm f2 (snd s1) (snd s2)

let lem_assoc_l_eq (#a: Type) (#n: nat)
  (arr1 arr2 arr3: array a #n)
  : Lemma
  (requires
    Some? arr1 /\
    Some? arr2 /\
    Some? arr3 /\
    composable arr1 arr2 /\
    composable arr2 arr3 /\
    composable (op arr1 arr2) arr3 /\
    composable arr1 (op arr2 arr3))
  (ensures
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3)
  =
  let s1 = Some?.v arr1 in
  let s2 = Some?.v arr2 in
  let s3 = Some?.v arr3 in
  map_seq2_assoc f1 (fst s1) (fst s2) (fst s3);
  map_seq2_assoc f2 (snd s1) (snd s2) (snd s3)

let lem_assoc_l_aux1 (#a: Type) (#n: nat)
  (s1 s2 s3 s23: content a #n)
  (i: nat)
  : Lemma
  (requires
    i < n /\
    composable' s2 s3 /\
    s23 == op' s2 s3 /\
    comp_prop
      (index (fst s2) i) (index (fst s3) i)
      (index (snd s2) i) (index (snd s3) i) /\
    comp_prop
      (index (fst s1) i) (index (fst s23) i)
      (index (snd s1) i) (index (snd s23) i)
  )
  (ensures
    // TODO: duplicata
    i < n /\
    comp_prop
      (index (fst s1) i) (index (fst s2) i)
      (index (snd s1) i) (index (snd s2) i))
  =
  assert (fst s23 == map_seq2 f1 (fst s2) (fst s3));
  assert (snd s23 == map_seq2 f2 (snd s2) (snd s3));
  Classical.forall_intro (map_seq2_index f1 (fst s2) (fst s3));
  Classical.forall_intro (map_seq2_index f2 (snd s2) (snd s3));
  ()

let lem_assoc_l_aux2 (#a: Type) (#n: nat)
  (s1 s2 s3 s23 s12: content a #n)
  (i: nat)
  : Lemma
  (requires
    i < n /\
    composable' s2 s3 /\
    s23 == op' s2 s3 /\
    composable' s1 s2 /\
    s12 == op' s1 s2 /\
    comp_prop
      (index (fst s2) i) (index (fst s3) i)
      (index (snd s2) i) (index (snd s3) i) /\
    comp_prop
      (index (fst s1) i) (index (fst s23) i)
      (index (snd s1) i) (index (snd s23) i)
  )
  (ensures
    //TODO: duplicata
    i < n /\
    comp_prop
      (index (fst s12) i) (index (fst s3) i)
      (index (snd s12) i) (index (snd s3) i)
  )
  =
  assert (fst s12 == map_seq2 f1 (fst s1) (fst s2));
  assert (snd s12 == map_seq2 f2 (snd s1) (snd s2));
  assert (fst s23 == map_seq2 f1 (fst s2) (fst s3));
  assert (snd s23 == map_seq2 f2 (snd s2) (snd s3));
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  Classical.forall_intro (map_seq2_index f2 (snd s1) (snd s2));
  Classical.forall_intro (map_seq2_index f1 (fst s2) (fst s3));
  Classical.forall_intro (map_seq2_index f2 (snd s2) (snd s3))

let lem_assoc_l_aux3 (#a: Type) (#n: nat)
  (arr1 arr2 arr3: array a #n)
  : Lemma
  (requires
    Some? arr1 /\ Some? arr2 /\ Some? arr3 /\
    composable arr2 arr3 /\
    composable arr1 (op arr2 arr3)
  )
  (ensures
    composable arr1 arr2 /\
    composable (op arr1 arr2) arr3
  )
  =
  let s1 = Some?.v arr1 in
  let s2 = Some?.v arr2 in
  let s3 = Some?.v arr3 in
  let arr23 = op arr2 arr3 in
  assert (Some? arr23);
  let s23 = Some?.v arr23 in
  map_seq2_len f1 (fst s2) (fst s3);
  map_seq2_len f2 (snd s2) (snd s3);
  Classical.forall_intro (
    Classical.move_requires (
      lem_assoc_l_aux1 #a #n s1 s2 s3 s23
    )
  );
  let arr12 = op arr1 arr2 in
  assert (Some? arr12);
  let s12 = Some?.v arr12 in
  map_seq2_len f1 (fst s1) (fst s2);
  map_seq2_len f2 (snd s1) (snd s2);
  Classical.forall_intro (
    Classical.move_requires (
      lem_assoc_l_aux2 s1 s2 s3 s23 s12
    )
  )

let lem_assoc (#a: Type) (#n: nat)
  (arr1 arr2 arr3: array a #n)
  : Lemma
  (requires
    composable arr2 arr3 /\
    composable arr1 (op arr2 arr3)
  )
  (ensures
    composable arr1 arr2 /\
    composable (op arr1 arr2) arr3 /\
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3
  )
  =
  if None? arr1 then () else
  if None? arr2 then () else
  if None? arr3 then () else begin
  lem_assoc_l_aux3 arr1 arr2 arr3;
  lem_assoc_l_eq arr1 arr2 arr3;
  ()
  end

let lem_assoc_l (#a: Type) (#n: nat)
  (arr1 arr2: array a #n) (arr3: array a #n{
    composable arr2 arr3 /\ composable arr1 (op arr2 arr3)
  })
  : Lemma (
    composable arr1 arr2 /\
    composable (op arr1 arr2) arr3 /\
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3
  )
  =
  lem_assoc arr1 arr2 arr3

let lem_assoc_r (#a: Type) (#n: nat)
  (arr1 arr2: array a #n) (arr3: array a #n{
    composable arr1 arr2 /\ composable (op arr1 arr2) arr3
  })
  : Lemma (
    composable arr2 arr3 /\
    composable arr1 (op arr2 arr3) /\
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3
  )
  =
  lem_commutative arr1 arr2;
  lem_assoc arr3 arr2 arr1;
  lem_commutative arr2 arr3;
  lem_commutative arr1 (op arr2 arr3);
  lem_commutative arr3 (op arr1 arr2)

let pcm_array (#a: Type) (#n: nat): pcm (array a #n) = {
  p = pcm_array';
  comm = lem_commutative;
  assoc = lem_assoc_l;
  assoc_r = lem_assoc_r;
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

let array_ref (a: Type u#1) (#n: nat) : Type u#0
  = Mem.ref (array a #n) pcm_array

let null #a #n = Mem.null #(array a #n) #pcm_array
let is_null #a #n r = Mem.is_null #(array a #n) #pcm_array r

let perm_ok_elem p : prop = (p.v <=. one == true) /\ True

let perm_ok #n (s: lseq perm n) : prop
  =
  forall i. ((index s i).v <=. one == true)

// deprecated
let apply (#a: Type u#1) (s: seq (a & perm)) (p: perm)
  : (r:seq (a & perm){length r == length s})
  =
  let s', _ = unzip s in
  unzip_len s;
  map_seq_len (fun x -> x, p) s';
  map_seq (fun x -> x, p) s'

// seq (a & perm) or seq a & seq perm?
// tentative
//let pts_to_raw_sl_extperm (#a: Type u#1)
//  (r: array_ref a) (v: content a)
//  : Mem.slprop u#1
//  =
//  let array_with_perm = apply (get_data v) p in
//  //let new_content = mk_content (get_size v) 0 0 array_with_perm in
//  let new_content = { v with data = array_with_perm } in
//  Mem.pts_to r (Some new_content)

// perm is bundled
let pts_to_raw_sl (#a: Type) (#n: nat)
  (r: array_ref a #n)
  (p: lseq perm n)
  (v: lseq a n)
  : Mem.slprop
  = Mem.pts_to r (Some (v, p))

let pts_to_raw (#a: Type) (#n: nat)
  (r: array_ref a #n)
  (p: lseq perm n)
  (v: lseq a n)
  : vprop
  //= to_vprop (Mem.pts_to r (Some v))
  = to_vprop (pts_to_raw_sl r p v)

[@@ __reduce__]
let pts_to' (#a: Type u#1) (#n: nat)
  (r: array_ref a)
  (p: lseq perm n)
  (v: lseq a n)
  : vprop
  =
  pts_to_raw r p v `star` pure (perm_ok p)

let pts_to_sl #a #n r p v
  = hp_of (pts_to' #a #n r p v)

let abcd_acbd (a b c d:Mem.slprop)
  : Lemma (Mem.(((a `star` b) `star` (c `star` d)) `equiv`
           ((a `star` c) `star` (b `star` d))))
  = let open Steel.Memory in
    calc (equiv) {
    ((a `star` b) `star` (c `star` d));
      (equiv) { star_associative a b (c `star` d) }
    ((a `star` (b `star` (c `star` d))));
      (equiv) { star_associative b c d;
                star_congruence a (b `star` (c `star` d))
                                a ((b `star` c) `star` d) }
    (a `star` ((b `star` c) `star` d));
      (equiv) { star_commutative  b c;
                star_congruence (b `star` c) d (c `star` b) d;
                star_congruence a ((b `star` c) `star` d)
                                a ((c `star` b) `star` d) }
    (a `star` ((c `star` b) `star` d));
      (equiv) { star_associative c b d;
                star_congruence a ((c `star` b) `star` d)
                                a (c `star` (b `star` d)) }
    (a `star` (c `star` (b `star` d)));
      (equiv) { star_associative a c (b `star` d) }
    ((a `star` c) `star` (b `star` d));
   }

let composable_to_fst_eq (#a: Type u#1) (#n: nat)
  (s1 s2: content a #n)
  : Lemma
  (requires composable' s1 s2)
  (ensures fst s1 == fst s2)
  =
  assert (forall (i:nat{i < n}).
    index (fst s1) i == index (fst s2) i
  );
  Seq.lemma_eq_intro (fst s1) (fst s2)

let op_to_fst_eq (#a: Type u#1) (#n: nat)
  (s1 s2 s3: content a #n)
  : Lemma
  (requires
    composable' s1 s2 /\
    s3 == op' s1 s2)
  (ensures fst s1 == fst s3)
  =
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  Seq.lemma_eq_elim (fst s1) (fst s3)

let pts_to_ref_injective (#a: Type u#1) (#n: nat)
  (r: array_ref a #n)
  (p0 p1: lseq perm n)
  (v0 v1: lseq a n)
  (m:Mem.mem)
  : Lemma
    (requires Mem.interp (
      pts_to_sl r p0 v0 `Mem.star` pts_to_sl r p1 v1) m)
    (ensures v0 == v1)
  = let open Steel.Memory in
    abcd_acbd (hp_of (pts_to_raw r p0 v0))
              (pure (perm_ok p0))
              (hp_of (pts_to_raw r p1 v1))
              (pure (perm_ok p1));
    Mem.affine_star
      (hp_of (pts_to_raw r p0 v0) `star` hp_of (pts_to_raw r p1 v1))
      (pure (perm_ok p0) `star` pure (perm_ok p1)) m;
    Mem.pts_to_compatible r (Some (v0, p0))
                            (Some (v1, p1))
                            m;
    assert (composable' (v0, p0) (v1, p1));
    composable_to_fst_eq (v0, p0) (v1, p1)

let pts_to_not_null (#a:Type u#1) (#n: nat)
                    (r: array_ref a #n)
                    (p: lseq perm n)
                    (v: lseq a n)
                    (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl r p v) m)
          (ensures r =!= null)
  = Mem.affine_star
      (hp_of (pts_to_raw r p v))
      (Mem.pure (perm_ok p)) m;
    Mem.pts_to_not_null r (Some (v, p)) m

let aux' (#a: Type u#1) (#n: nat)
  (x y f1 f2 z: array a #n)
  : Lemma
  (requires
    Some? x /\
    Some? y /\
    composable x f1 /\
    op f1 x == z /\
    composable y f2 /\
    op f2 y == z
  )
  (ensures fst (Some?.v x) == fst (Some?.v y))
  =
  assert (Some? z);
  match (Some? f1, Some? f2) with
  | false, false -> ()
  | true, false ->
    assert (op f2 y == y);
    assert (y == z);
    composable_to_fst_eq (Some?.v x) (Some?.v f1);
    op_to_fst_eq (Some?.v f1) (Some?.v x) (Some?.v z)
  | false, true ->
    assert (op f1 x == x);
    assert (x == z);
    composable_to_fst_eq (Some?.v y) (Some?.v f2);
    op_to_fst_eq (Some?.v f2) (Some?.v y) (Some?.v z)
  | true, true ->
    composable_to_fst_eq (Some?.v x) (Some?.v f1);
    composable_to_fst_eq (Some?.v y) (Some?.v f2);
    op_to_fst_eq (Some?.v f1) (Some?.v x) (Some?.v z);
    op_to_fst_eq (Some?.v f2) (Some?.v y) (Some?.v z)

let aux (#a: Type u#1) (#n: nat)
  (r: array_ref a)
  (p: lseq perm n)
  (x y: erased (lseq a n))
  (m:Mem.mem)
  : Lemma
  (requires
    Mem.interp (pts_to_sl r p x) m /\
    Mem.interp (pts_to_sl r p y) m
  )
  (ensures x == y)
  =
  let c1 = Some (reveal x, p) in
  let c2 = Some (reveal y, p) in
  Mem.pts_to_join r c1 c2 m;
  assert (joinable pcm_array c1 c2);
  assert (exists z.
    compatible pcm_array c1 z /\
    compatible pcm_array c2 z
  );
  assert (
    exists z.
    (exists (frame: array a).
      composable c1 frame /\
      op frame c1 == z) /\
    (exists (frame: array a).
      composable c2 frame /\
      op frame c2 == z)
  );
  assert (
    exists (z f1 f2: array a).
      composable c1 f1 /\
      op f1 c1 == z /\
      composable c2 f2 /\
      op f2 c2 == z /\
      Some? z
  );
  Classical.forall_intro_3 (
    Classical.move_requires_3 (
        aux' c1 c2
    )
  )

// 1) better definition
// 2) a pts_to wrapper? an unwrapped PCM based on the wrapped one?
// [selected option] 3) unwrapped PCM from scratch
let pts_to_witinv_aux (#a:Type) (#n: nat)
  (r:array_ref a #n) (p: lseq perm n)
  : Lemma (Mem.is_witness_invariant (pts_to_sl r p))
  =
  Classical.forall_intro_3 (
    fun (x y: lseq a n) ->
      Classical.move_requires (aux r p x y)
  )
