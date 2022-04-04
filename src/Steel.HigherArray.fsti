module Steel.HigherArray

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission

open FStar.Real
open FStar.PCM

module PR = Steel.PCMReference
module Mem = Steel.Memory

#set-options "--ide_id_info_off"

open FStar.Seq
open Seq.Aux

(**
[ok] First step : lseq a n & lseq perm n PCM
  [ok] - unwrapped PCM
  [ok] - perm -> option perm
[ok] Second step : slprop on top of it
-- separation between HigherArray and Array,
  due to selectors universes restriction
[wip] Third step : vprop on top of it, introducing idx1/idx2
**)

(** First step **)

// seems a reasonable way to reason about null permissions
let perm = option perm

let sum_perm_opt (p1 p2: perm) : perm
  = match p1, p2 with
  | None, p
  | p, None -> p
  | Some p1, Some p2 -> Some (sum_perm p1 p2)

let perm_ok_elem (p: perm)
  = match p with
  | None -> true
  | Some p -> p.v <=. one

let content (a: Type u#1) (#n: nat): Type u#1
  = x:(lseq (option a) n & lseq perm n){
    forall (i:nat{i < n}).
      Some? (index (fst x) i) = Some? (index (snd x) i)
  }

let array (a: Type u#1) (#n: nat): Type u#1 = option (content a #n)

let comp_prop (#a: Type) (v1 v2: option a) (p1 p2: perm)
  =
  ((Some? p1 /\ Some? p2) ==> v1 == v2) /\
  perm_ok_elem (sum_perm_opt p1 p2)

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

let f1 (#a: Type) : option a -> option a -> option a
  = fun v1 v2 -> match (v1, v2) with
  | v, None
  | None, v -> v
  | Some _, Some _ -> v1

let f2 : perm -> perm -> perm
  = fun x y -> sum_perm_opt x y

//let f (#a: Type) : a & perm -> a & perm -> a & perm =
//  fun x y -> f1 (fst x) (fst y), f2 (snd x) (snd y)

//let l2 (p1 p2: perm)
//  : Lemma
//  (Some? (f2 p1 p2) = (Some? p1 || Some? p2))
//  = ()
//
//let l1 (#a: Type) (v1 v2: option a)
//  : Lemma
//  (Some? (f1 v1 v2) = (Some? v1 || Some? v2))
//  = ()
//
//let l (#a: Type) (v1 v2: option a) (p1 p2: perm)
//  : Lemma
//  (requires (Some? v1 = Some? p1) /\ (Some? v2 = Some? p2))
//  (ensures Some? (f1 v1 v2) = Some? (f2 p1 p2))
//  = ()

let op' (#a: Type) (#n: nat)
  (s1 s2: content a #n)
  : content a #n
  =
  map_seq2_len f1 (fst s1) (fst s2);
  map_seq2_len f2 (snd s1) (snd s2);
  let x1 = map_seq2 f1 (fst s1) (fst s2) in
  let x2 = map_seq2 f2 (snd s1) (snd s2) in
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  Classical.forall_intro (map_seq2_index f2 (snd s1) (snd s2));
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
  //assert (fst s23 == map_seq2 f1 (fst s2) (fst s3));
  Classical.forall_intro (map_seq2_index f1 (fst s2) (fst s3));
  //assert (x23 == f1 x2 x3);
  //assert (snd s23 == map_seq2 f2 (snd s2) (snd s3));
  Classical.forall_intro (map_seq2_index f2 (snd s2) (snd s3));
  //assert (y23 == f2 y2 y3);
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
  //assert (fst s23 == map_seq2 f1 (fst s2) (fst s3));
  Classical.forall_intro (map_seq2_index f1 (fst s2) (fst s3));
  //assert (x23 == f1 x2 x3);
  //assert (snd s23 == map_seq2 f2 (snd s2) (snd s3));
  Classical.forall_intro (map_seq2_index f2 (snd s2) (snd s3));
  //assert (y23 == f2 y2 y3);
  //assert (fst s12 == map_seq2 f1 (fst s1) (fst s2));
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  //assert (x12 == f1 x1 x2);
  //assert (snd s12 == map_seq2 f2 (snd s1) (snd s2));
  Classical.forall_intro (map_seq2_index f2 (snd s1) (snd s2));
  //assert (y12 == f2 y1 y2);
  ()

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
      lem_assoc_l_aux1 s1 s2 s3 s23
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
  lem_assoc_l_eq arr1 arr2 arr3
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
let is_null #a #n r
  : b:bool{b <==> r == null}
  = Mem.is_null #(array a #n) #pcm_array r

let perm_ok #n (s: lseq perm n) : prop
  =
  forall i. perm_ok_elem (index s i)

(** Second step = void? **)

(** Third step **)

type set = s:(nat & nat){fst s <= snd s}

let is_in (pos: nat) (s: set) : bool
  = fst s <= pos && pos < snd s

let zeroed (#a: Type) (bounds: set) (s: seq (option a))
  : prop
  = forall (i:nat{i < length s}).
      Some? (index s i) = is_in i (bounds)

[@@ __steel_reduce__]
unfold
let pts_to_sl' (#a: Type)
  (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  (v: lseq (option a) n
  {forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq (option a) (i2 - i1))
  : Mem.slprop u#1
  =
  Mem.pts_to r (Some (v, p)) `Mem.star`
  Mem.pure (perm_ok p) `Mem.star`
  Mem.pure (zeroed (i1, i2) p) `Mem.star`
  //Mem.pure (zeroed (i1, i2) v) `Mem.star`
  Mem.pure (Seq.slice v i1 i2 == subv)

let pts_to_ref_injective' (#a: Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p1 p2: lseq perm n)
  (v1: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p1 i) = Some? (index v1 i)})
  (v2: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p2 i) = Some? (index v2 i)})
  (subv1 subv2: lseq (option a) (i2 - i1))
  (m:Mem.mem)
  : Lemma
    (requires Mem.interp (
      pts_to_sl' n r i1 i2 p1 v1 subv1 `Mem.star`
      pts_to_sl' n r i1 i2 p2 v2 subv2) m)
    (ensures subv1 == subv2)
  =
  let pa1 = Mem.pts_to r (Some (v1, p1)) in
  let pb1 = Mem.pure (perm_ok p1) in
  let pc1 = Mem.pure (zeroed (i1, i2) p1) in
  let pd1 = Mem.pure (Seq.slice v1 i1 i2 == subv1) in
  let pa2 = Mem.pts_to r (Some (v2, p2)) in
  let pb2 = Mem.pure (perm_ok p2) in
  let pc2 = Mem.pure (zeroed (i1, i2) p2) in
  let pd2 = Mem.pure (Seq.slice v2 i1 i2 == subv2) in
  let pab1 = pa1 `Mem.star` pb1 in
  let pabc1 = pa1 `Mem.star` pb1 `Mem.star` pc1 in
  let pab2 = pa2 `Mem.star` pb2 in
  let pabc2 = pa2 `Mem.star` pb2 `Mem.star` pc2 in
  let pabcd1 = pa1 `Mem.star` pb1 `Mem.star` pc1 `Mem.star` pd1 in
  let pabcd2 = pa2 `Mem.star` pb2 `Mem.star` pc2 `Mem.star` pd2 in
  assert (Mem.interp (pabcd1 `Mem.star` pabcd2) m);
  let m1, m2 = Mem.id_elim_star pabcd1 pabcd2 m in
  assert (Mem.disjoint m1 m2);
  assert (Mem.interp (
    ((pa1 `Mem.star` pb1) `Mem.star` pc1) `Mem.star` pd1
  ) m1);
  let mabc1, md1 = Mem.id_elim_star pabc1 pd1 m1 in
  let mab1, mc1 = Mem.id_elim_star pab1 pc1 mabc1 in
  let ma1, mb1 = Mem.id_elim_star pa1 pb1 mab1 in
  let mabc2, md2 = Mem.id_elim_star pabc2 pd2 m2 in
  let mab2, mc2 = Mem.id_elim_star pab2 pc2 mabc2 in
  let ma2, mb2 = Mem.id_elim_star pa2 pb2 mab2 in

  Mem.disjoint_join m2 mabc1 md1;
  Mem.disjoint_join m2 mab1 mc1;
  Mem.disjoint_join m2 ma1 mb1;
  assert (Mem.disjoint ma1 m2);
  Mem.disjoint_join ma1 mabc2 md2;
  Mem.disjoint_join ma1 mab2 mc2;
  Mem.disjoint_join ma1 ma2 mb2;
  assert (Mem.disjoint ma1 ma2);

  Mem.intro_star pa1 pa2 ma1 ma2;
  let ma = Mem.join ma1 ma2 in
  assert (Mem.interp (pa1 `Mem.star` pa2) ma);
  Mem.pts_to_compatible r
    (Some (v1, p1))
    (Some (v2, p2))
    ma;
  assert (composable' (v1, p1) (v2, p2));
  Mem.pure_interp (zeroed (i1, i2) p1) m;
  Mem.pure_interp (zeroed (i1, i2) p2) m;
  assert (forall (i:nat{i < n}).
      Some? (index p1 i) = is_in i (i1, i2));
  assert (forall (i:nat{i < n}).
      Some? (index p2 i) = is_in i (i1, i2));
  assert (forall (i:nat{i < n /\ i1 <= i /\ i < i2}).
      Some? (index p1 i) = true);
  assert (forall (i:nat{i < n /\ i1 <= i /\ i < i2}).
      Some? (index p2 i) = true);
  assert (forall (i:nat{i < n /\ i1 <= i /\ i < i2}).
      index v1 i == index v2 i);
  Mem.pure_interp (Seq.slice v1 i1 i2 == subv1) m;
  Mem.pure_interp (Seq.slice v2 i1 i2 == subv2) m;
  Seq.lemma_eq_intro subv1 subv2;
  assert (subv1 == subv2);
  ()

let pts_to_not_null' (#a:Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq (option a) (i2 - i1))
  (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl' n r i1 i2 p v subv) m)
          (ensures r =!= null)
  = Mem.pts_to_not_null r (Some (v, p)) m

let composable_to_fst_eq (#a: Type u#1) (#n: nat)
  (s1 s2: content a #n)
  (i1 i2: nat)
  : Lemma
  (requires
    composable' s1 s2 /\
    snd s1 == snd s2 /\
    i1 <= i2 /\ i2 <= n /\
    zeroed (i1, i2) (snd s1))
  (ensures
    Seq.slice (fst s1) i1 i2 == Seq.slice (fst s2) i1 i2)
  =
  assert (forall (i:nat{i < n}).
    index (fst s1) i == index (fst s2) i
  );
  Seq.lemma_eq_intro (fst s1) (fst s2)

let op_to_fst_eq (#a: Type u#1) (#n: nat)
  (s1 s2 s3: content a #n)
  (i1 i2: nat)
  : Lemma
  (requires
    composable' s1 s2 /\
    s3 == op' s1 s2 /\
    i1 <= i2 /\ i2 <= n /\
    zeroed (i1, i2) (snd s1))
  (ensures
    Seq.slice (fst s1) i1 i2 == Seq.slice (fst s3) i1 i2)
  =
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  Seq.lemma_eq_elim
    (Seq.slice (fst s1) i1 i2)
    (Seq.slice (fst s3) i1 i2)

let aux' (#a: Type u#1) (#n: nat)
  (i1 i2: nat)
  (x y u1 u2 z: array a #n)
  : Lemma
  (requires
    Some? x /\
    Some? y /\
    snd (Some?.v x) == snd (Some?.v y) /\
    composable x u1 /\
    op u1 x == z /\
    composable y u2 /\
    op u2 y == z /\
    i1 <= i2 /\ i2 <= n /\
    zeroed (i1, i2) (snd (Some?.v x))
  )
  (ensures (
    Seq.slice (fst (Some?.v x)) i1 i2
 == Seq.slice (fst (Some?.v y)) i1 i2))
  =
  assert (Some? z);
  let x' = Some?.v x in
  let y' = Some?.v y in
  let z' = Some?.v z in
  match (Some? u1, Some? u2) with
  | false, false -> ()
  | false, true ->
    assert (op u1 x == x);
    assert (x == z);
    lem_commutative y u2;
    op_to_fst_eq (Some?.v y) (Some?.v u2) (Some?.v z) i1 i2
  | true, false ->
    assert (op u2 y == y);
    assert (y == z);
    lem_commutative x u1;
    op_to_fst_eq (Some?.v x) (Some?.v u1) (Some?.v z) i1 i2
  | true, true ->
    lem_commutative y u2;
    op_to_fst_eq (Some?.v y) (Some?.v u2) (Some?.v z) i1 i2;
    lem_commutative x u1;
    op_to_fst_eq (Some?.v x) (Some?.v u1) (Some?.v z) i1 i2

//#push-options "--z3rlimit 30"
let aux_sl' (#a: Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  (v1: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v1 i)})
  (v2: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v2 i)})
  (subv1 subv2: lseq (option a) (i2 - i1))
  (m:Mem.mem)
  : Lemma
  (requires
    Mem.interp (pts_to_sl' n r i1 i2 p v1 subv1) m /\
    Mem.interp (pts_to_sl' n r i1 i2 p v2 subv2) m
  )
  (ensures subv1 == subv2)
  =
  let c1 = Some (v1, p) in
  let c2 = Some (v2, p) in
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
  Mem.pure_interp (zeroed (i1, i2) p) m;
  assert (zeroed (i1, i2) (snd (Some?.v c1)));
  assert (
    exists (z f1 f2: array a).
      Some? c1 /\
      Some? c2 /\
      snd (Some?.v c1) == snd (Some?.v c2) /\
      composable c1 f1 /\
      op f1 c1 == z /\
      composable c2 f2 /\
      op f2 c2 == z /\
      i1 <= i2 /\ i2 <= n /\
      zeroed (i1, i2) (snd (Some?.v c1))
  );
  Mem.pure_interp (Seq.slice v1 i1 i2 == subv1) m;
  assert (Seq.slice v1 i1 i2 == subv1);
  Mem.pure_interp (Seq.slice v2 i1 i2 == subv2) m;
  assert (Seq.slice v2 i1 i2 == subv2);
  Classical.forall_intro_3 (
    Classical.move_requires_3 (
      aux' i1 i2 c1 c2
    )
  );
  assert (Seq.slice v1 i1 i2 == Seq.slice v2 i1 i2);
  Seq.lemma_eq_intro subv1 subv2

unfold
let pts_to_sl (#a: Type)
  (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  =
  fun (x: lseq a (i2 - i1)) ->
  Mem.h_exists (
    fun (y: lseq (option a) n{forall (i:nat{i < n}).
      Some? (index p i) = Some? (index y i)}) ->
    map_seq_len (fun e -> Some e) x;
    pts_to_sl' n r i1 i2 p y (map_seq (fun e -> Some e) x)
  )

let pts_to_ref_injective (#a: Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p1 p2: lseq perm n)
  (subv1 subv2: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma
    (requires Mem.interp (
      pts_to_sl n r i1 i2 p1 subv1 `Mem.star`
      pts_to_sl n r i1 i2 p2 subv2) m)
    (ensures subv1 == subv2)
  =
  let psl1 = pts_to_sl n r i1 i2 p1 subv1 in
  let psl2 = pts_to_sl n r i1 i2 p2 subv2 in
  let m1, m2 = Mem.id_elim_star psl1 psl2 m in
  map_seq_len (fun e -> Some e) subv1;
  map_seq_len (fun e -> Some e) subv2;
  let subv1' = map_seq (fun e -> Some e) subv1 in
  let subv2' = map_seq (fun e -> Some e) subv2 in
  let v1 : (y: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p1 i) = Some? (index y i)})
    = Mem.id_elim_exists
    (fun x -> pts_to_sl' n r i1 i2 p1 x subv1') m1 in
  let v2 : (y: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p2 i) = Some? (index y i)})
    = Mem.id_elim_exists
    (fun x -> pts_to_sl' n r i1 i2 p2 x subv2') m2 in
  let psl1' = pts_to_sl' n r i1 i2 p1 v1 subv1' in
  let psl2' = pts_to_sl' n r i1 i2 p2 v2 subv2' in
  assert (Mem.interp psl1' m1);
  assert (Mem.interp psl2' m2);
  assert (Mem.disjoint m1 m2);
  Mem.intro_star psl1' psl2' m1 m2;
  pts_to_ref_injective' r i1 i2 p1 p2 v1 v2 subv1' subv2' m;
  assert (subv1' == subv2');
  Classical.forall_intro (map_seq_index (fun e -> Some e) subv1);
  Classical.forall_intro (map_seq_index (fun e -> Some e) subv2);
  Seq.lemma_eq_intro subv1 subv2;
  assert (subv1 == subv2)

let pts_to_not_null (#a:Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  (subv: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl n r i1 i2 p subv) m)
          (ensures r =!= null)
  =
  map_seq_len (fun e -> Some e) subv;
  let subv' = map_seq (fun e -> Some e) subv in
  let v : (y: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index y i)})
    = Mem.id_elim_exists
    (fun x -> pts_to_sl' n r i1 i2 p x subv') m in
  pts_to_not_null' r i1 i2 p v subv' m

let aux_sl (#a: Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  (subv1 subv2: lseq a (i2 - i1))
  (m:Mem.mem)
  : Lemma
  (requires
    Mem.interp (pts_to_sl n r i1 i2 p subv1) m /\
    Mem.interp (pts_to_sl n r i1 i2 p subv2) m
  )
  (ensures subv1 == subv2)
  =
  map_seq_len (fun e -> Some e) subv1;
  map_seq_len (fun e -> Some e) subv2;
  let subv1' = map_seq (fun e -> Some e) subv1 in
  let subv2' = map_seq (fun e -> Some e) subv2 in
  let v1 : (y: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index y i)})
    = Mem.id_elim_exists
    (fun x -> pts_to_sl' n r i1 i2 p x subv1') m in
  let v2 : (y: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index y i)})
    = Mem.id_elim_exists
    (fun x -> pts_to_sl' n r i1 i2 p x subv2') m in
  aux_sl' r i1 i2 p v1 v2 subv1' subv2' m;
  Classical.forall_intro (map_seq_index (fun e -> Some e) subv1);
  Classical.forall_intro (map_seq_index (fun e -> Some e) subv2);
  Seq.lemma_eq_intro subv1 subv2

// 1) better definition
// 2) a pts_to wrapper? an unwrapped PCM based on the wrapped one?
// [selected option] 3) unwrapped PCM from scratch

//let t1 (#a: Type) (#n: nat)
//  (i1: nat) (i2: nat{i1 <= i2 /\ i2 <= n})
//  (p: lseq perm n)
//  : Type
//  = v:(lseq (option a) n){forall (i:nat{i < n}).
//      Some? (index p i) = Some? (index v i)}
//
//let t2 (#a: Type) (#n: nat)
//  (i1: nat) (i2: nat{i1 <= i2 /\ i2 < n})
//  : Type
//  = lseq (option a) (i2 - i1))
//
//let t (#a: Type) (#n: nat)
//  (i1: nat) (i2: nat{i1 <= i2 /\ i2 < n})
//  (p: lseq perm n)
//  : Type
//  = t1 #a #n i1 i2 p & t2 #a #n i1 i2

let pts_to_witinv (#a:Type) (#n: nat)
  (r:array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  : Lemma (Mem.is_witness_invariant (
      pts_to_sl n r i1 i2 p
    ))
  =
  Classical.forall_intro_3 (
    Classical.move_requires_3 (
      aux_sl r i1 i2 p
    )
  )

let pts_to_frame_mon (#a:Type) (#n: nat)
  (r:array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  : Lemma (Mem.is_frame_monotonic (
      pts_to_sl n r i1 i2 p
    ))
  = pts_to_witinv r i1 i2 p

[@@ expect_failure]
let array_sel' (#a:Type) (#n: nat)
  (r:array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 < n})
  (p: lseq perm n)
  : selector' (lseq a (i2 - i1)) (pts_to_sl n r i1 i2 p)
  =
  fun h -> Mem.id_elim_exists (pts_to_sl n r i1 i2 p)

let full_perm_seq (n: nat)
  : s:lseq perm n{forall (i:nat{i < n}). Some? (index s i)}
  = Seq.create n (Some full_perm)

let to_some (#a: Type) (#n: nat) (v: lseq a n)
  : s:lseq (option a) n{forall (i:nat{i < n}). Some? (index s i)}
  =
  map_seq_len (fun e -> Some e) v;
  Classical.forall_intro (map_seq_index (fun e -> Some e) v);
  map_seq (fun e -> Some e) v

let mk_content (#a: Type) (v: seq a) : content a #(Seq.length v)
  =
  let v = to_some v in
  let p = full_perm_seq (Seq.length v) in
  v, p

unfold
let pts_to (#a:Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq perm n)
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq a (i2 - i1))
  =
  to_vprop (pts_to_sl' n r i1 i2 p v (to_some subv))

open FStar.Tactics
let lema_alloc (#a:Type u#1)
  (#n: nat)
  (r: array_ref a #n)
  (v: lseq a n)
  (m: Mem.mem)
  : Lemma
  (requires (
    let v' = to_some v in
    let p = full_perm_seq n in
    let c : array a #n = Some (v', p) in
    Mem.interp (hp_of (PR.pts_to #(array a #n) #pcm_array r c)) m
  ))
  (ensures (
    //let p : lseq perm n = full_perm_seq n in
    Mem.interp (
      pts_to_sl' n r 0 n (full_perm_seq n) (to_some v) (to_some v)
      //Mem.pts_to r (Some (to_some v, p)) `Mem.star`
      //Mem.pure (perm_ok p) `Mem.star`
      //Mem.pure (zeroed (0, n) p) `Mem.star`
      //Mem.pure (Seq.slice (to_some v) 0 n == to_some v)
    ) m
  ))
  =
  //let p = full_perm_seq n in
  //let p1 = Mem.pts_to r (Some (to_some v, p)) in
  let p1 = Mem.pts_to r (Some (to_some v, full_perm_seq n)) in
  let p2 = Mem.pure (perm_ok (full_perm_seq n)) in
  let p3 = Mem.pure (zeroed (0, n) (full_perm_seq n)) in
  let p4 = Mem.pure (slice (to_some v) 0 n == to_some v) in
  assert (Mem.interp p1 m);

  Mem.emp_unit p1;
  assert (perm_ok (full_perm_seq n));
  Mem.pure_star_interp p1
    (perm_ok (full_perm_seq n)) m;
  assert (Mem.interp (p1 `Mem.star` p2) m);

  Mem.emp_unit (p1 `Mem.star` p2);
  assert (zeroed (0, n) (full_perm_seq n));
  Mem.pure_star_interp (p1 `Mem.star` p2)
    (zeroed (0, n) (full_perm_seq n)) m;
  assert (Mem.interp (p1 `Mem.star` p2 `Mem.star` p3) m);

  Mem.emp_unit (p1 `Mem.star` p2 `Mem.star` p3);
  assert (slice (to_some v) 0 n == to_some v);
  Mem.pure_star_interp (p1 `Mem.star` p2 `Mem.star` p3)
    (slice (to_some v) 0 n == to_some v) m;
  assert (Mem.interp
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4) m);
  assert (forall (i:nat{i < n}).
    Some? (index (full_perm_seq n) i) = Some? (index (to_some v) i));
  assert (
  pts_to_sl' n r 0 n (full_perm_seq n) (to_some v) (to_some v)
  ==
  pts_to_sl' n r 0 n (full_perm_seq n) (to_some v) (to_some v));
  // to be removed
  assume (
  pts_to_sl' #a n r 0 n (full_perm_seq n) (to_some v) (to_some v)
  ==
  ((Mem.pts_to r (Some (to_some v, (full_perm_seq n))) `Mem.star`
  Mem.pure (perm_ok (full_perm_seq n)) `Mem.star`
  Mem.pure (zeroed (0, n) (full_perm_seq n)) `Mem.star`
  Mem.pure (Seq.slice (to_some v) 0 n == to_some v)) <: Mem.slprop u#1));
  assert (
  pts_to_sl' #a n r 0 n (full_perm_seq n) (to_some v) (to_some v)
  ==
  ((Mem.pts_to r (Some (to_some v, (full_perm_seq n))) `Mem.star`
  Mem.pure (perm_ok (full_perm_seq n)) `Mem.star`
  Mem.pure (zeroed (0, n) (full_perm_seq n)) `Mem.star`
  Mem.pure (Seq.slice (to_some v) 0 n == to_some v)) <: Mem.slprop u#1)
  );
  //by (norm [delta_only [`%pts_to_sl']]; trefl (); dump "zut");
  assert (
    pts_to_sl' n r 0 n (full_perm_seq n) (to_some v) (to_some v)
    ==
    p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4);
  ()

//#push-options "--z3rlimit 30"
let alloc (#a: Type) (n:nat{n > 0}) (v: lseq a n)
  : Steel (array_ref a #(Seq.length v))
  //: Steel unit
  emp
  (fun r ->
    pts_to #a #n r 0 n
      (full_perm_seq n)
      (to_some v)
      v)
  (requires fun _ -> True)
  (ensures fun _ r _ -> not (is_null r))
  =
  let v' = to_some v in
  let p = full_perm_seq n in
  let c : array a #n = Some (v', p) in
  assert (FStar.PCM.composable pcm_array c None);
  assert (compatible pcm_array c c);
  let r = PR.alloc #(array a #n) #pcm_array c in
  rewrite_slprop
    (PR.pts_to #(array a #n) #pcm_array r c)
    (pts_to #a #n r 0 n (full_perm_seq n) (to_some v) v)
    (fun m -> lema_alloc #a #n r v m);
  extract_info_raw
    (pts_to #a #n r 0 n (full_perm_seq n) (to_some v) v)
    (~ (is_null #a #n r))
    (fun m -> pts_to_not_null' #a #n r 0 n
      (full_perm_seq n) (to_some v) (to_some v) m);
  return r
