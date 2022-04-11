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
//let perm = option perm

let sum_perm_opt (p1 p2: option perm) : option perm
  = match p1, p2 with
  | None, p
  | p, None -> p
  | Some p1, Some p2 -> Some (sum_perm p1 p2)

let perm_ok_elem (p: option perm)
  = match p with
  | None -> true
  | Some p -> p.v <=. one

let content (a: Type u#1) (#n: nat): Type u#1
  = x:(lseq (option a) n & lseq (option perm) n){
    forall (i:nat{i < n}).
      Some? (index (fst x) i) = Some? (index (snd x) i) /\
      perm_ok_elem (index (snd x) i)
  }

let array (a: Type u#1) (#n: nat): Type u#1 = content a #n

let comp_prop (#a: Type) (v1 v2: option a) (p1 p2: option perm)
  =
  ((Some? p1 /\ Some? p2) ==> v1 == v2) /\
  perm_ok_elem (sum_perm_opt p1 p2)

let composable (#a: Type) (#n: nat): symrel (content a #n)
  = fun (arr1 arr2: array a #n) ->
  (forall (i:nat{i < n}).
    comp_prop
      (index (fst arr1) i) (index (fst arr2) i)
      (index (snd arr1) i) (index (snd arr2) i)
  )

let f1 (#a: Type) : option a -> option a -> option a
  = fun v1 v2 -> match (v1, v2) with
  | v, None
  | None, v -> v
  | Some _, Some _ -> v1

let f2 : option perm -> option perm -> option perm
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

let op (#a: Type) (#n: nat)
  (s1: array a #n)
  (s2: array a #n{composable s1 s2})
  : array a #n
  =
  map_seq2_len f1 (fst s1) (fst s2);
  map_seq2_len f2 (snd s1) (snd s2);
  let x1 = map_seq2 f1 (fst s1) (fst s2) in
  let x2 = map_seq2 f2 (snd s1) (snd s2) in
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  Classical.forall_intro (map_seq2_index f2 (snd s1) (snd s2));
  x1, x2

let one_element (#a: Type) (#n: nat) : array a #n
  =
  let none_seq1 : lseq (option a) n = Seq.create n None in
  let none_seq2 : lseq (option perm) n = Seq.create n None in
  (none_seq1, none_seq2)

let pcm_array' (#a: Type) (#n: nat): pcm' (array a #n) = {
  composable = composable;
  op = op;
  one = one_element;
}

let lem_commutative (#a: Type) (#n: nat)
  (arr1: array a #n)
  (arr2: array a #n{composable arr1 arr2})
  : Lemma (op arr1 arr2 == op arr2 arr1)
  =
  map_seq2_comm f1 (fst arr1) (fst arr2);
  map_seq2_comm f2 (snd arr1) (snd arr2)

let lem_assoc_l_eq (#a: Type) (#n: nat)
  (arr1 arr2 arr3: array a #n)
  : Lemma
  (requires
    composable arr1 arr2 /\
    composable arr2 arr3 /\
    composable (op arr1 arr2) arr3 /\
    composable arr1 (op arr2 arr3))
  (ensures
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3)
  =
  map_seq2_assoc f1 (fst arr1) (fst arr2) (fst arr3);
  map_seq2_assoc f2 (snd arr1) (snd arr2) (snd arr3)

let lem_assoc_l_aux1 (#a: Type) (#n: nat)
  (arr1 arr2 arr3 arr23: array a #n)
  (i: nat)
  : Lemma
  (requires
    i < n /\
    composable arr2 arr3 /\
    arr23 == op arr2 arr3 /\
    comp_prop
      (index (fst arr2) i) (index (fst arr3) i)
      (index (snd arr2) i) (index (snd arr3) i) /\
    comp_prop
      (index (fst arr1) i) (index (fst arr23) i)
      (index (snd arr1) i) (index (snd arr23) i)
  )
  (ensures
    // TODO: duplicata
    i < n /\
    comp_prop
      (index (fst arr1) i) (index (fst arr2) i)
      (index (snd arr1) i) (index (snd arr2) i))
  =
  map_seq2_index f1 (fst arr2) (fst arr3) i;
  map_seq2_index f2 (snd arr2) (snd arr3) i


let lem_assoc_l_aux2 (#a: Type) (#n: nat)
  (arr1 arr2 arr3 arr23 arr12: content a #n)
  (i: nat)
  : Lemma
  (requires
    i < n /\
    composable arr2 arr3 /\
    arr23 == op arr2 arr3 /\
    composable arr1 arr2 /\
    arr12 == op arr1 arr2 /\
    comp_prop
      (index (fst arr2) i) (index (fst arr3) i)
      (index (snd arr2) i) (index (snd arr3) i) /\
    comp_prop
      (index (fst arr1) i) (index (fst arr23) i)
      (index (snd arr1) i) (index (snd arr23) i)
  )
  (ensures
    //TODO: duplicata
    i < n /\
    comp_prop
      (index (fst arr12) i) (index (fst arr3) i)
      (index (snd arr12) i) (index (snd arr3) i)
  )
  =
  map_seq2_index f1 (fst arr2) (fst arr3) i;
  map_seq2_index f2 (snd arr2) (snd arr3) i;
  map_seq2_index f1 (fst arr1) (fst arr2) i;
  map_seq2_index f2 (snd arr1) (snd arr2) i

let lem_assoc_l_aux3 (#a: Type) (#n: nat)
  (arr1 arr2 arr3: array a #n)
  : Lemma
  (requires
    composable arr2 arr3 /\
    composable arr1 (op arr2 arr3)
  )
  (ensures
    composable arr1 arr2 /\
    composable (op arr1 arr2) arr3
  )
  =
  let arr23 = op arr2 arr3 in
  map_seq2_len f1 (fst arr2) (fst arr3);
  map_seq2_len f2 (snd arr2) (snd arr3);
  Classical.forall_intro (
    Classical.move_requires (
      lem_assoc_l_aux1 arr1 arr2 arr3 arr23
    )
  );
  let arr12 = op arr1 arr2 in
  map_seq2_len f1 (fst arr1) (fst arr2);
  map_seq2_len f2 (snd arr1) (snd arr2);
  Classical.forall_intro (
    Classical.move_requires (
      lem_assoc_l_aux2 arr1 arr2 arr3 arr23 arr12
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
  lem_assoc_l_aux3 arr1 arr2 arr3;
  lem_assoc_l_eq arr1 arr2 arr3

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

let lem_is_unit (#a: Type) (#n: nat) (arr: array a #n)
  : Lemma
  (composable arr (one_element #a #n) /\
  op arr (one_element #a #n) == arr)
  =
  let one_element = one_element #a #n in
  assert (forall i. index (fst one_element) i == None);
  assert (forall i. index (snd one_element) i == None);
  assert (composable arr one_element);
  map_seq2_len f1 (fst arr) (fst one_element);
  map_seq2_len f2 (snd arr) (snd one_element);
  Classical.forall_intro (
    map_seq2_index f1 (fst arr) (fst one_element));
  Classical.forall_intro (
    map_seq2_index f2 (snd arr) (snd one_element));
  let r = op arr one_element in
  Seq.lemma_eq_intro (fst r) (fst arr);
  Seq.lemma_eq_intro (snd r) (snd arr)

let pcm_array (#a: Type) (#n: nat): pcm (array a #n) = {
  p = pcm_array';
  comm = lem_commutative;
  assoc = lem_assoc_l;
  assoc_r = lem_assoc_r;
  is_unit = lem_is_unit;
  refine = (fun (arr: array a #n) ->
    (forall (i:nat{i < n}). Some? (index (snd arr) i))
    \/
    arr == one_element);
}

let array_ref (a: Type u#1) (#n: nat) : Type u#0
  = Mem.ref (array a #n) pcm_array

let null #a #n = Mem.null #(array a #n) #pcm_array
let is_null #a #n r
  : b:bool{b <==> r == null}
  = Mem.is_null #(array a #n) #pcm_array r

let perm_ok #n (s: lseq (option perm) n) : prop
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
  (p: lseq (option perm) n{perm_ok p})
  (v: lseq (option a) n
  {forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq (option a) (i2 - i1))
  : Mem.slprop u#1
  =
  Mem.pts_to r (v, p) `Mem.star`
  Mem.pure (perm_ok p) `Mem.star`
  Mem.pure (zeroed (i1, i2) p) `Mem.star`
  //Mem.pure (zeroed (i1, i2) v) `Mem.star`
  Mem.pure (Seq.slice v i1 i2 == subv)

let pts_to_ref_injective' (#a: Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p1 p2: (p:lseq (option perm) n{perm_ok p}))
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
  let pa1 = Mem.pts_to r (v1, p1) in
  let pb1 = Mem.pure (perm_ok p1) in
  let pc1 = Mem.pure (zeroed (i1, i2) p1) in
  let pd1 = Mem.pure (Seq.slice v1 i1 i2 == subv1) in
  let pa2 = Mem.pts_to r (v2, p2) in
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
    (v1, p1)
    (v2, p2)
    ma;
  assert (composable (v1, p1) (v2, p2));
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
  (p: lseq (option perm) n{perm_ok p})
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq (option a) (i2 - i1))
  (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl' n r i1 i2 p v subv) m)
          (ensures r =!= null)
  = Mem.pts_to_not_null r (v, p) m

let composable_to_fst_eq (#a: Type u#1) (#n: nat)
  (s1 s2: content a #n)
  (i1 i2: nat)
  : Lemma
  (requires
    composable s1 s2 /\
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
    composable s1 s2 /\
    s3 == op s1 s2 /\
    i1 <= i2 /\ i2 <= n /\
    zeroed (i1, i2) (snd s1))
  (ensures
    Seq.slice (fst s1) i1 i2 == Seq.slice (fst s3) i1 i2)
  =
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  Seq.lemma_eq_elim
    (Seq.slice (fst s1) i1 i2)
    (Seq.slice (fst s3) i1 i2)

let op_to_snd_eq (#a: Type u#1) (#n: nat)
  (s1 s2 s3: content a #n)
  (i1 i2: nat)
  : Lemma
  (requires
    composable s1 s2 /\
    s3 == op s1 s2 /\
    i1 <= i2 /\ i2 <= n /\
    zeroed (i1, i2) (snd s2))
  (ensures
    Seq.slice (fst s2) i1 i2 == Seq.slice (fst s3) i1 i2)
  =
  Classical.forall_intro (map_seq2_index f1 (fst s1) (fst s2));
  Seq.lemma_eq_elim
    (Seq.slice (fst s2) i1 i2)
    (Seq.slice (fst s3) i1 i2)

let aux' (#a: Type u#1) (#n: nat)
  (i1 i2: nat)
  (x y u1 u2 z: array a #n)
  : Lemma
  (requires
    snd x == snd y /\
    composable x u1 /\
    op u1 x == z /\
    composable y u2 /\
    op u2 y == z /\
    i1 <= i2 /\ i2 <= n /\
    zeroed (i1, i2) (snd x))
  (ensures (
    Seq.slice (fst x) i1 i2
 == Seq.slice (fst y) i1 i2))
  =
  lem_commutative y u2;
  op_to_fst_eq y u2 z i1 i2;
  lem_commutative x u1;
  op_to_fst_eq x u1 z i1 i2

//#push-options "--z3rlimit 30"
let aux_sl' (#a: Type u#1) (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
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
  let c1 = (v1, p) in
  let c2 = (v2, p) in
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
  assert (zeroed (i1, i2) (snd c1));
  assert (
    exists (z f1 f2: array a).
      snd c1 == snd c2 /\
      composable c1 f1 /\
      op f1 c1 == z /\
      composable c2 f2 /\
      op f2 c2 == z /\
      i1 <= i2 /\ i2 <= n /\
      zeroed (i1, i2) (snd c1)
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
  (p: lseq (option perm) n{perm_ok p})
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
  (p1 p2: (p:lseq (option perm) n{perm_ok p}))
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
  (p: lseq (option perm) n{perm_ok p})
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
  (p: lseq (option perm) n{perm_ok p})
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
  (p: lseq (option perm) n{perm_ok p})
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
  (p: lseq (option perm) n{perm_ok p})
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
  : s:lseq (option perm) n{forall (i:nat{i < n}). Some? (index s i)}
  = Seq.create n (Some full_perm)

let null_perm_seq (n: nat)
  : s:lseq (option perm) n{forall (i:nat{i < n}). None? (index s i)}
  = Seq.create n None

let to_some
  (#a: Type)
  (#n: nat)
  (s: Seq.lseq a n)
  : Pure (Seq.lseq (option a) n)
  (requires True)
  (ensures fun s' -> forall (i: nat{i < n}).
    Some? (Seq.index s' i) /\
    Seq.index s' i == Some (Seq.index s i)
  )
  = without_some (to_some' s)

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
  (p: lseq (option perm) n{perm_ok p})
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq a (i2 - i1))
  =
  to_vprop (pts_to_sl' n r i1 i2 p v (to_some subv))

let lemma_alloc (#a:Type)
  (#n: nat)
  (r: array_ref a #n)
  (v: lseq a n)
  (m: Mem.mem)
  : Lemma
  (requires (
    let v' = to_some v in
    let p = full_perm_seq n in
    let c : array a #n = (v', p) in
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
  let p1 = Mem.pts_to r (to_some v, full_perm_seq n) in
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
  assert (
  pts_to_sl' #a n r 0 n (full_perm_seq n) (to_some v) (to_some v)
  ==
  Mem.pts_to r (to_some v, (full_perm_seq n)) `Mem.star`
  Mem.pure (perm_ok (full_perm_seq n)) `Mem.star`
  Mem.pure (zeroed (0, n) (full_perm_seq n)) `Mem.star`
  Mem.pure (Seq.slice (to_some v) 0 n == to_some v));
  assert (
    pts_to_sl' n r 0 n (full_perm_seq n) (to_some v) (to_some v)
    ==
    p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4);
  ()

let alloc (#a: Type) (n:nat{n > 0}) (v: lseq a n)
  : Steel (array_ref a #(Seq.length v))
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
  let c : array a #n = (v', p) in
  pcm_array.is_unit c;
  assert (FStar.PCM.composable pcm_array c pcm_array.p.one);
  pcm_array.comm c pcm_array.p.one;
  assert (FStar.PCM.op pcm_array pcm_array.p.one c == c);
  assert (compatible pcm_array c c);
  let r = PR.alloc #(array a #n) #pcm_array c in
  rewrite_slprop
    (PR.pts_to #(array a #n) #pcm_array r c)
    (pts_to #a #n r 0 n (full_perm_seq n) (to_some v) v)
    (fun m -> lemma_alloc #a #n r v m);
  extract_info_raw
    (pts_to #a #n r 0 n (full_perm_seq n) (to_some v) v)
    (~ (is_null #a #n r))
    (fun m -> pts_to_not_null' #a #n r 0 n
      (full_perm_seq n) (to_some v) (to_some v) m);
  return r

let lemma_usersl_to_pcmsl (#a: Type)
  (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq a (i2 - i1))
  (m: Mem.mem)
  : Lemma
  (requires Mem.interp (
    pts_to_sl' n r i1 i2 p v (to_some subv)
  ) m)
  (ensures (
    let c : array a #n = (v, p) in
    Mem.interp (
    hp_of (PR.pts_to #(array a #n) #pcm_array r c)
    ) m
  ))
  =
  ()

let lemma_pcmsl_to_usersl (#a: Type)
  (#n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2})
  (p: lseq (option perm) n)
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq a (i2 - i1))
  (m: Mem.mem)
  : Lemma
  (requires (
    i1 <= i2 /\ i2 <= n /\
    perm_ok p /\
    zeroed (i1, i2) p /\
    slice v i1 i2 == to_some subv /\
    (let c : array a #n = (v, p) in
    Mem.interp (
    hp_of (PR.pts_to #(array a #n) #pcm_array r c)
  ) m)))
  (ensures Mem.interp (
    pts_to_sl' n r i1 i2 p v (to_some subv)
  ) m)
  =
  let p1 = Mem.pts_to r (v, p) in
  let p2 = Mem.pure (perm_ok p) in
  let p3 = Mem.pure (zeroed (i1, i2) p) in
  let p4 = Mem.pure (slice v i1 i2 == to_some subv) in
  assert (Mem.interp p1 m);

  Mem.emp_unit p1;
  assert (perm_ok p);
  Mem.pure_star_interp p1 (perm_ok p) m;
  assert (Mem.interp (p1 `Mem.star` p2) m);

  Mem.emp_unit (p1 `Mem.star` p2);
  assert (zeroed (i1, i2) p);
  Mem.pure_star_interp (p1 `Mem.star` p2)
    (zeroed (i1, i2) p) m;
  assert (Mem.interp (p1 `Mem.star` p2 `Mem.star` p3) m);


  Mem.emp_unit (p1 `Mem.star` p2 `Mem.star` p3);
  assert (slice v i1 i2 == to_some subv);
  Mem.pure_star_interp (p1 `Mem.star` p2 `Mem.star` p3)
    (slice v i1 i2 == to_some subv) m;
  assert (Mem.interp
    (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4) m);
  ()

let lemma_exclusive (#a: Type) (n: nat)
  (c1: array a #n{snd c1 == full_perm_seq n})
  (c2: array a #n)
  : Lemma
  (requires
    composable c1 c2
  )
  (ensures
    c2 == one_element
  )
  =
  let one_element = one_element #a #n in
  assert (forall i. index (snd c2) i == None);
  assert (forall i. index (fst c2) i == None);
  Seq.lemma_eq_intro (fst c2) (fst one_element);
  Seq.lemma_eq_intro (snd c2) (snd one_element)

// extending it with ghost ref/additional writing for zeroing?
let free (#a: Type) (n:nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{p == full_perm_seq n})
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq a (i2 - i1))
  : SteelT unit
  (pts_to #a #n r i1 i2 p v subv)
  (fun _ -> emp)
  =
  let c : array a #n = (v, p) in
  pcm_array.is_unit c;
  assert (FStar.PCM.composable pcm_array c pcm_array.p.one);
  pcm_array.comm c pcm_array.p.one;
  assert (FStar.PCM.op pcm_array pcm_array.p.one c == c);
  assert (compatible pcm_array c c);
  rewrite_slprop
    (pts_to #a #n r i1 i2 p v subv)
    (PR.pts_to #(array a #n) #pcm_array r c)
    (fun m -> lemma_usersl_to_pcmsl r i1 i2 p v subv m);
  Classical.forall_intro (
    Classical.move_requires (lemma_exclusive n c));
  assert (FStar.PCM.exclusive pcm_array c);
  PR.free r c;
  drop (PR.pts_to r (Mkpcm'?.one (Mkpcm?.p pcm_array)));
  return ()

let from_some (#a: Type) (#n: nat) (s: lseq (option a) n)
  : Pure (lseq a n)
         (requires forall (i:nat{i < n}). Some? (index s i))
         (ensures fun s' ->
           forall (i:nat{i < n}). Some? (Seq.index s i))
  =
  from_some' (with_some s)

let read (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{perm_ok p})
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (#subv: lseq a (i2 - i1))
  : Steel (lseq a (i2 - i1))
  (pts_to #a #n r i1 i2 p v subv)
  (fun _ -> pts_to #a #n r i1 i2 p v subv)
  (requires fun _ -> True)
  (ensures fun _ subv' _ -> subv' == subv)
  =
  let c = (v, p) in
  extract_info_raw
    (pts_to #a #n r i1 i2 p v subv)
    (zeroed (i1, i2) p)
    (fun m -> Mem.pure_interp (zeroed (i1, i2) p) m);
  assert (zeroed (i1, i2) p);
  extract_info_raw
    (pts_to #a #n r i1 i2 p v subv)
    (Seq.slice v i1 i2 == to_some subv)
    (fun m -> Mem.pure_interp (Seq.slice v i1 i2 == to_some subv) m);
  assert (Seq.slice v i1 i2 == to_some subv);
  eq_bazar_some subv;
  assert (from_some (Seq.slice v i1 i2) == subv);
  rewrite_slprop
    (pts_to #a #n r i1 i2 p v subv)
    (PR.pts_to #(array a #n) #pcm_array r (v, p))
    (fun m -> lemma_usersl_to_pcmsl r i1 i2 p v subv m);
  let read_v = PR.read r (v, p) in
  assert (forall (i:nat{i <n}).
   Some? (index (snd read_v) i) = Some? (index (fst read_v) i));
  assert (compatible pcm_array (v, p) read_v);
  assert (exists (frame:content a #n).
    composable (v, p) frame /\ op frame (v, p) == read_v
  );
  let frame = FStar.IndefiniteDescription.indefinite_description_tot
    (content a #n)
    (fun frame -> composable (v, p) frame /\ op frame (v, p) == read_v) in
  op_to_snd_eq frame (v, p) read_v i1 i2;
  assert (Seq.slice v i1 i2 == Seq.slice (fst read_v) i1 i2);
  assert (from_some (Seq.slice (fst read_v) i1 i2) == subv);
  rewrite_slprop
    (PR.pts_to #(array a #n) #pcm_array r (v, p))
    (pts_to #a #n r i1 i2 p v subv)
    (fun m -> lemma_pcmsl_to_usersl r i1 i2 p v subv m);
  return subv

let full_p (bounds: set) (s: seq (option perm))
  : prop
  = forall (i:nat{i < length s}).
      is_in i (bounds) ==> index s i == Some full_perm

let selfcompose_split_aux (#a: Type) (#n:nat)
  (i: nat{i <= n})
  (arr: array a #n)
  : array a #i & array a #(n - i)
  =
  let v1, v2 = Seq.split (fst arr) i in
  let p1, p2 = Seq.split (snd arr) i in
  (v1, p1), (v2, p2)

let selfcompose_split3_aux (#a: Type) (#n:nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr: array a #n)
  : array a #i1 & array a #(i2 - i1) & array a #(n - i2)
  =
  let v1, v2' = Seq.split (fst arr) i1 in
  let v2, v3 = Seq.split v2' (i2 - i1) in
  let p1, p2' = Seq.split (snd arr) i1 in
  let p2, p3 = Seq.split p2' (i2 - i1) in
  (v1, p1), (v2, p2), (v3, p3)

let selfcompose_split3_zeroed (#a: Type) (#n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr: array a #n{
    zeroed (i1, i2) (snd arr) /\
    full_p (i1, i2) (snd arr)
  })
  : Lemma
  //Pure (array a #i1 & array a #(i2 - i1) & array a #(n - i2))
  (requires
    zeroed (i1, i2) (snd arr) /\
    full_p (i1, i2) (snd arr))
  (ensures
    (let arr1, arr2, arr3 = selfcompose_split3_aux i1 i2 arr in
    snd arr1 == null_perm_seq i1 /\
    snd arr2 == full_perm_seq (i2 - i1) /\
    snd arr3 == null_perm_seq (n - i2)
  ))
  =
  let arr1, arr2, arr3 = selfcompose_split3_aux i1 i2 arr in
  Seq.lemma_eq_intro (snd arr1) (null_perm_seq i1);
  Seq.lemma_eq_intro (snd arr2) (full_perm_seq (i2 - i1));
  Seq.lemma_eq_intro (snd arr3) (null_perm_seq (n - i2))

let selfcompose_split (#a: Type) (#n:nat) (i: nat{i <= n})
  (arr1: array a #n)
  (arr2: array a #n)
  : Lemma
  (requires composable arr1 arr2)
  (ensures (
    let arr11, arr12 = selfcompose_split_aux i arr1 in
    let arr21, arr22 = selfcompose_split_aux i arr2 in
    composable arr11 arr21 /\
    composable arr12 arr22
  ))
  = ()

let selfcompose_split3 (#a: Type) (#n:nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr1: array a #n)
  (arr2: array a #n)
  : Lemma
  (requires composable arr1 arr2)
  (ensures (
    let arr11, arr12, arr13 = selfcompose_split3_aux i1 i2 arr1 in
    let arr21, arr22, arr23 = selfcompose_split3_aux i1 i2 arr2 in
    composable arr11 arr21 /\
    composable arr12 arr22 /\
    composable arr13 arr23
  ))
  = ()

let op_none_id (#a: Type) (#n: nat)
  (arr1 arr2 arr3: array a #n)
  : Lemma
  (requires
    snd arr1 == null_perm_seq n /\
    arr3 == op arr1 arr2
  )
  (ensures arr3 == arr2)
  =
  assert (forall i. None? (index (fst arr1) i));
  map_seq2_len f1 (fst arr1) (fst arr2);
  map_seq2_len f2 (snd arr1) (snd arr2);
  Classical.forall_intro (map_seq2_index f1 (fst arr1) (fst arr2));
  Classical.forall_intro (map_seq2_index f2 (snd arr1) (snd arr2));
  Seq.lemma_eq_intro (fst arr2) (fst arr3);
  Seq.lemma_eq_intro (snd arr2) (snd arr3)

let selfcompose_merge_aux (#a: Type) (#i1 #i2: nat)
  (arr1: array a #i1)
  (arr2: array a #i2)
  : array a #(i1 + i2)
  =
  let arr_v = append (fst arr1) (fst arr2) in
  let arr_p = append (snd arr1) (snd arr2) in
  arr_v, arr_p

let selfcompose_merge3_aux (#a: Type) (#i1 #i2 #i3: nat)
  (arr1: array a #i1)
  (arr2: array a #i2)
  (arr3: array a #i3)
  : array a #(i1 + i2 + i3)
  =
  let arr_v23 = append (fst arr2) (fst arr3) in
  let arr_p23 = append (snd arr2) (snd arr3) in
  let arr_v = append (fst arr1) arr_v23 in
  let arr_p = append (snd arr1) arr_p23 in
  arr_v, arr_p

let selfcompose_merge_split_bij (#a: Type) (#n:nat)
  (i1: nat{i1 <= n})
  (arr: array a #n)
  : Lemma
  (let arr1, arr2 = selfcompose_split_aux i1 arr in
  selfcompose_merge_aux arr1 arr2 == arr)
  =
  lemma_split (fst arr) i1;
  lemma_split (snd arr) i1

let selfcompose_split_merge_bij (#a: Type) (#n:nat)
  (j: nat{j <= n})
  (arr1: array a #j)
  (arr2: array a #(n - j))
  : Lemma
  (let arr1', arr2' = selfcompose_split_aux j
    (selfcompose_merge_aux arr1 arr2)
  in
  arr1 == arr1' /\
  arr2 == arr2'
  )
  =
  let arr1', arr2' = selfcompose_split_aux j
    (selfcompose_merge_aux arr1 arr2) in
  Seq.lemma_eq_intro (fst arr1') (fst arr1);
  Seq.lemma_eq_intro (snd arr1') (snd arr1);
  Seq.lemma_eq_intro (fst arr2') (fst arr2);
  Seq.lemma_eq_intro (snd arr2') (snd arr2)

let selfcompose_merge3_split3_bij (#a: Type) (#n:nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr: array a #n)
  : Lemma
  (let arr1, arr2, arr3 = selfcompose_split3_aux i1 i2 arr in
  selfcompose_merge3_aux arr1 arr2 arr3 == arr)
  =
  lemma_split (fst arr) i1;
  lemma_split (snd arr) i1;
  let _, arr23_v = split (fst arr) i1 in
  let _, arr23_p = split (snd arr) i1 in
  lemma_split arr23_v (i2 - i1);
  lemma_split arr23_p (i2 - i1)

let selfcompose_split3_merge3_bij (#a: Type) (#n:nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr1: array a #i1)
  (arr2: array a #(i2 - i1))
  (arr3: array a #(n - i2))
  : Lemma
  (let arr1', arr2', arr3' = selfcompose_split3_aux i1 i2
    (selfcompose_merge3_aux arr1 arr2 arr3)
  in
  arr1 == arr1' /\
  arr2 == arr2' /\
  arr3 == arr3'
  )
  =
  let arr = selfcompose_merge3_aux arr1 arr2 arr3 in
  let arr1', arr2', arr3' = selfcompose_split3_aux i1 i2 arr in
  let _, arr23_v = split (fst arr) i1 in
  let _, arr23_p = split (snd arr) i1 in
  Seq.lemma_eq_intro arr23_v (append (fst arr2) (fst arr3));
  Seq.lemma_eq_intro arr23_p (append (snd arr2) (snd arr3));
  Seq.lemma_eq_intro (fst arr1') (fst arr1);
  Seq.lemma_eq_intro (snd arr1') (snd arr1);
  Seq.lemma_eq_intro (fst arr2') (fst arr2);
  Seq.lemma_eq_intro (snd arr2') (snd arr2);
  Seq.lemma_eq_intro (fst arr3') (fst arr3);
  Seq.lemma_eq_intro (snd arr3') (snd arr3)

let selfcompose_merge3 (#a: Type) (#n:nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr1: array a #n)
  (arr2: array a #n)
  : Lemma
  (requires (
    let arr11, arr12, arr13 = selfcompose_split3_aux i1 i2 arr1 in
    let arr21, arr22, arr23 = selfcompose_split3_aux i1 i2 arr2 in
    composable arr11 arr21 /\
    composable arr12 arr22 /\
    composable arr13 arr23
  ))
  (ensures (
    let arr11, arr12, arr13 = selfcompose_split3_aux i1 i2 arr1 in
    let arr21, arr22, arr23 = selfcompose_split3_aux i1 i2 arr2 in
    composable arr1 arr2 /\
    op arr1 arr2 == selfcompose_merge3_aux
      (op arr11 arr21)
      (op arr12 arr22)
      (op arr13 arr23)
  ))
  =
  selfcompose_merge3_split3_bij i1 i2 arr1;
  selfcompose_merge3_split3_bij i1 i2 arr2;
  let arr11, arr12, arr13 = selfcompose_split3_aux i1 i2 arr1 in
  let arr21, arr22, arr23 = selfcompose_split3_aux i1 i2 arr2 in
  map_seq2_append f1
    (fst arr12) (fst arr22) (fst arr13) (fst arr23);
  map_seq2_append f2
    (snd arr12) (snd arr22) (snd arr13) (snd arr23);
  let arr1_23 = selfcompose_merge_aux arr12 arr13 in
  let arr2_23 = selfcompose_merge_aux arr22 arr23 in
  map_seq2_append f1
    (fst arr11) (fst arr21) (fst arr1_23) (fst arr2_23);
  map_seq2_append f2
    (snd arr11) (snd arr21) (snd arr1_23) (snd arr2_23)

#push-options "--z3rlimit 20"
let frame_preserving_sufficient_conditions1 (#a: Type) (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr1: array a #n)
  (arr2: array a #n{
    snd arr1 == snd arr2 /\
    zeroed (i1, i2) (snd arr1) /\
    full_p (i1, i2) (snd arr1)})
  (arr3: array a #n)
  : Pure (array a #n)
  (requires
    pcm_array.refine arr3 /\
    compatible pcm_array arr1 arr3)
  (ensures fun arr4 ->
    pcm_array.refine arr4 /\
    compatible pcm_array arr2 arr4)
  =
  let arr21, arr22, arr23 = selfcompose_split3_aux i1 i2 arr2 in
  let arr31, arr32, arr33 = selfcompose_split3_aux i1 i2 arr3 in
  let arr4 = selfcompose_merge3_aux arr31 arr22 arr33 in
  // 1
  // TODO: to be removed, refactor this proof+lemmas
  assume (forall (i:nat{i < n}). Some? (index (snd arr3) i));
  assert (pcm_array.refine arr4);
  // 2
  let frame22 : array a #(i2 - i1)
    = (create (i2 - i1) None, create (i2 - i1) None) in
  let frame2 : array a #n
    = selfcompose_merge3_aux arr31 frame22 arr33 in
  // 2.2
  assert (composable arr22 frame22);
  op_none_id frame22 arr22 (op frame22 arr22);
  assert (op frame22 arr22 == arr22);
  lem_commutative frame22 arr22;
  assert (op arr22 frame22 == arr22);
  // 2.1 & 2.3
  selfcompose_split3_zeroed i1 i2 arr2;
  // 2.1
  assert (snd arr21 == null_perm_seq i1);
  assert (composable arr21 arr31);
  op_none_id arr21 arr31 (op arr21 arr31);
  assert (op arr21 arr31 == arr31);
  // 2.3
  assert (snd arr23 == null_perm_seq (n - i2));
  assert (composable arr23 arr33);
  op_none_id arr23 arr33 (op arr23 arr33);
  assert (op arr23 arr33 == arr33);
  // 2
  selfcompose_merge3 i1 i2 arr2 frame2;
  // arr2:   arr21, arr22,   arr23
  // frame2: arr31, frame22, arr33
  // arr4:   arr31, arr22,   ar33
  selfcompose_split3_merge3_bij i1 i2 arr21 arr22 arr23;
  selfcompose_split3_merge3_bij i1 i2 arr31 frame22 arr33;
  assert (op arr2 frame2 == selfcompose_merge3_aux
    (op arr21 arr31)
    (op arr22 frame22)
    (op arr23 arr33)
  );
  selfcompose_split3_merge3_bij i1 i2 arr31 arr22 arr33;
  assert (op arr2 frame2 == arr4);
  lem_commutative frame2 arr2;
  assert (compatible pcm_array arr2 arr4);
  arr4

let _f_aux (#a: Type) (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr1: array a #n)
  (arr2: array a #n{
    snd arr1 == snd arr2 /\
    zeroed (i1, i2) (snd arr1) /\
    full_p (i1, i2) (snd arr1)})
  :
  (arr3: array a #n{
    pcm_array.refine arr3 /\ compatible pcm_array arr1 arr3})
  ->
  (arr4:array a #n{
    pcm_array.refine arr4 /\ compatible pcm_array arr2 arr4})
  =
  fun (arr3: array a #n{
    pcm_array.refine arr3 /\ compatible pcm_array arr1 arr3})
    -> frame_preserving_sufficient_conditions1 n i1 i2 arr1 arr2 arr3


let frame_preserving_sufficient_conditions2 (#a: Type) (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr1: array a #n)
  (arr2: array a #n{
    snd arr1 == snd arr2 /\
    zeroed (i1, i2) (snd arr1) /\
    full_p (i1, i2) (snd arr1)})
  (arr3 arr4: array a #n)
  (frame: array a #n)
  : Lemma
  (requires
    //i1 < i2 /\
    pcm_array.refine arr3 /\
    compatible pcm_array arr1 arr3 /\
    //pcm_array.refine arr4 /\
    //compatible pcm_array arr2 arr4 /\
    arr4 == _f_aux
      n i1 i2 arr1 arr2 arr3 /\

    composable arr1 frame /\
    op arr1 frame == arr3)
  (ensures
    //(forall (frame:array a #n{composable arr1 frame}).
    composable arr2 frame /\
    op arr2 frame == arr4)
  =
  let arr11, arr12, arr13 = selfcompose_split3_aux i1 i2 arr1 in
  let arr21, arr22, arr23 = selfcompose_split3_aux i1 i2 arr2 in
  let arr31, arr32, arr33 = selfcompose_split3_aux i1 i2 arr3 in
  //let arr41, arr42, arr43 = selfcompose_split3_aux i1 i2 arr4 in
  let frame1, frame2, frame3 = selfcompose_split3_aux i1 i2 frame in

  selfcompose_split3 i1 i2 arr1 frame;
  selfcompose_split3_zeroed i1 i2 arr1;
  // 2
  assert (composable arr12 frame2);
  assert (snd arr12 == full_perm_seq (i2 - i1));
  lemma_exclusive (i2 - i1) arr12 frame2;
  assert (frame2 == one_element #a #(i2 - i1));
  lem_is_unit arr22;
  assert (composable arr22 frame2);
  assert (op arr22 frame2 == arr22);
  // 1
  assert (composable arr11 frame1);
  assert (snd arr11 == null_perm_seq i1);
  assert (snd arr21 == snd arr11);
  assert (composable arr21 frame1);
  op_none_id arr21 frame1 (op arr21 frame1);
  assert (op arr21 frame1 == frame1);
  // 3
  assert (composable arr13 frame3);
  assert (snd arr13 == null_perm_seq (n - i2));
  assert (snd arr23 == snd arr13);
  assert (composable arr23 frame3);
  op_none_id arr23 frame3 (op arr23 frame3);
  assert (op arr23 frame3 == frame3);

  // reverse
  selfcompose_merge3 i1 i2 arr1 frame;
  assert (op arr1 frame == selfcompose_merge3_aux
    (op arr11 frame1)
    (op arr12 frame2)
    (op arr13 frame3)
  );
  selfcompose_split3_merge3_bij i1 i2
    (op arr11 frame1)
    (op arr12 frame2)
    (op arr13 frame3);
  // 1 (reverse)
  assert (op arr11 frame1 == arr31);
  assert (snd arr11 == null_perm_seq i1);
  op_none_id arr11 frame1 arr31;
  assert (frame1 == arr31);
  // 3 (reverse)
  assert (op arr13 frame3 == arr33);
  assert (snd arr13 == null_perm_seq (n - i2));
  op_none_id arr13 frame3 arr33;
  assert (frame3 == arr33);

  // merge
  // frame: arr31, null, arr33
  // arr4: arr31, arr22, arr33
  let arr41, arr42, arr43 = selfcompose_split3_aux i1 i2 arr4 in
  selfcompose_merge3 i1 i2 arr2 frame;
  assert (op arr2 frame == selfcompose_merge3_aux
    (op arr21 frame1)
    (op arr22 frame2)
    (op arr23 frame3)
  );
  selfcompose_split3_merge3_bij i1 i2
    (op arr21 frame1)
    (op arr22 frame2)
    (op arr23 frame3);
  ()

let _f (#a: Type) (n: nat)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (arr1: array a #n)
  (arr2: array a #n{
    snd arr1 == snd arr2 /\
    zeroed (i1, i2) (snd arr1) /\
    full_p (i1, i2) (snd arr1)})
  : frame_preserving_upd #(array a #n) (pcm_array #a #n) arr1 arr2
  =
  Classical.forall_intro_3 (
    Classical.move_requires_3 (
      frame_preserving_sufficient_conditions2 n i1 i2 arr1 arr2
    )
  );
  fun (arr3: array a #n{
    pcm_array.refine arr3 /\ compatible pcm_array arr1 arr3})
    -> frame_preserving_sufficient_conditions1 n i1 i2 arr1 arr2 arr3

let write (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (p: lseq (option perm) n{
    perm_ok p /\ zeroed (i1, i2) p /\ full_p (i1, i2) p})
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq a (i2 - i1){slice v i1 i2 == to_some subv})
  (subv_to_write: lseq a (i2 - i1))
  : SteelT unit
  (pts_to #a #n r i1 i2 p v subv)
  (fun _ ->
    let v' = append
      (slice v 0 i1)
      (append (to_some subv_to_write) (slice v i2 n)) in
    pts_to #a #n r i1 i2 p v' subv_to_write)
  =
  rewrite_slprop
    (pts_to #a #n r i1 i2 p v subv)
    (PR.pts_to #(array a #n) #pcm_array r (v, p))
    (fun m -> lemma_usersl_to_pcmsl r i1 i2 p v subv m);
  let v' =
    append
    (slice v 0 i1)
    (append (to_some subv_to_write) (slice v i2 n)) in
  let v'' = (append (to_some subv_to_write) (slice v i2 n)) in
  assert (length (to_some subv_to_write) == i2 - i1);
  lemma_eq_intro (slice v'' 0 (i2 - i1)) (to_some subv_to_write);
  assert (slice v'' 0 (i2 - i1) == to_some subv_to_write);
  lemma_eq_intro (slice v' i1 i2) (to_some subv_to_write);
  assert (slice v' i1 i2 == to_some subv_to_write);
  PR.upd_gen r (v, p) (
    append
    (slice v 0 i1)
    (append (to_some subv_to_write) (slice v i2 n)),
  p) (_f n i1 i2 (v, p) (v', p));
  rewrite_slprop
    (PR.pts_to #(array a #n) #pcm_array r (
      append
      (slice v 0 i1)
      (append (to_some subv_to_write) (slice v i2 n)),
    p))
    (pts_to #a #n r i1 i2 p
      (append
      (slice v 0 i1)
      (append (to_some subv_to_write) (slice v i2 n)))
    subv_to_write)
    (fun m ->
      lemma_pcmsl_to_usersl r i1 i2 p v' subv_to_write m);
  return ()

let split_aux (#a: Type) (n: nat)
  (s: lseq (option a) n)
  (j: nat{j <= n})
  : Pure (lseq (option a) n & lseq (option a) n)
  (requires True)
  (ensures fun r ->
    slice (fst r) 0 j == slice s 0 j /\
    slice (fst r) j n == create (n - j) None /\
    slice (snd r) j n == slice s j n /\
    slice (snd r) 0 j == create j None /\
    append (slice (fst r) 0 j) (slice (snd r) j n) == s
  )
  =
  let s1a, s2b = Seq.split s j in
  let s1b = Seq.create (n - j) None in
  let s2a = Seq.create j None in
  let s1 = append s1a s1b in
  let s2 = append s2a s2b in
  Seq.lemma_eq_intro (slice s1 0 j) (slice s 0 j);
  Seq.lemma_eq_intro (slice s1 j n) (create (n - j) None);
  Seq.lemma_eq_intro (slice s2 j n) (slice s j n);
  Seq.lemma_eq_intro (slice s2 0 j) (create j None);
  lemma_split s j;
  s1, s2

let split_aux_lemma (n: nat)
  (s: lseq (option perm) n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  : Lemma
  (requires perm_ok #n s /\ zeroed (i1, i2) s)
  (ensures (
    let s1, s2 = split_aux n s j in
    perm_ok #n s1 /\
    perm_ok #n s2 /\
    zeroed (i1, j) s1 /\
    zeroed (j, i2) s2
  ))
  =
  lemma_split s j

let split_aux_slice (#a: Type) (n: nat)
  (arr: array a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (subv: lseq a (i2 - i1){slice (fst arr) i1 i2 == to_some subv})
  (j: nat{i1 <= j /\ j <= i2})
  : Lemma
  (let v1, v2 = split_aux n (fst arr) j in
  let subv1, subv2 = split subv (j - i1) in
  slice v1 i1 j == to_some #a #(j - i1) subv1 /\
  slice v2 j i2 == to_some #a #(i2 - j) subv2)
  =
  let v1, v2 = split_aux n (fst arr) j in
  let subv1, subv2 = split subv (j - i1) in

  map_seq_len (fun e -> Some e) subv;
  let subv' = map_seq (fun e -> Some e) subv in
  Classical.forall_intro (map_seq_index (fun e -> Some e) subv);
  Seq.lemma_eq_intro (to_some subv) subv';

  assert (slice v1 0 j == slice (fst arr) 0 j);
  slice_slice v1 0 j i1 j;
  assert (slice v1 i1 j == slice (to_some subv) 0 (j - i1));
  assert (slice v1 i1 j == slice subv' 0 (j - i1));
  map_seq_len (fun e -> Some e) (slice subv 0 (j - i1));
  let subv1' = map_seq (fun e -> Some e) (slice subv 0 (j - i1)) in
  Classical.forall_intro (map_seq_index (fun e -> Some e)
    (slice subv 0 (j - i1)));
  Seq.lemma_eq_intro subv1' (slice subv' 0 (j - i1));
  assert (subv1' == slice subv' 0 (j - i1));
  Seq.lemma_eq_intro subv1' (to_some #a #(j - i1) subv1);
  assert (slice v1 i1 j == to_some #a #(j - i1) subv1);

  assert (slice v2 j n == slice (fst arr) j n);
  slice_slice v2 j n 0 (i2 - j);
  assert (slice v2 j i2 == slice (to_some subv) (j - i1) (i2 - i1));
  assert (slice v2 j i2 == slice subv' (j - i1) (i2 - i1));
  map_seq_len (fun e -> Some e) (slice subv (j - i1) (i2 - i1));
  let subv2' = map_seq (fun e -> Some e)
    (slice subv (j - i1) (i2 - i1)) in
  Classical.forall_intro (map_seq_index (fun e -> Some e)
    (slice subv (j - i1) (i2 - i1)));
  Seq.lemma_eq_intro subv2' (slice subv' (j - i1) (i2 - i1));
  assert (subv2' == slice subv' (j - i1) (i2 - i1));
  Seq.lemma_eq_intro subv2' (to_some #a #(i2 - j) subv2);
  assert (slice v2 j i2 == to_some #a #(i2 - j) subv2)

let selfcompose_merge2 (#a: Type) (#n:nat)
  (j: nat{j <= n})
  (arr1: array a #n)
  (arr2: array a #n)
  : Lemma
  (requires (
    let arr11, arr12 = selfcompose_split_aux j arr1 in
    let arr21, arr22 = selfcompose_split_aux j arr2 in
    composable arr11 arr21 /\
    composable arr12 arr22
  ))
  (ensures (
    let arr11, arr12 = selfcompose_split_aux j arr1 in
    let arr21, arr22 = selfcompose_split_aux j arr2 in
    composable arr1 arr2 /\
    op arr1 arr2 == selfcompose_merge_aux
      (op arr11 arr21)
      (op arr12 arr22)
  ))
  =
  selfcompose_merge_split_bij j arr1;
  selfcompose_merge_split_bij j arr2;
  let arr11, arr12 = selfcompose_split_aux j arr1 in
  let arr21, arr22 = selfcompose_split_aux j arr2 in
  map_seq2_append f1
    (fst arr11) (fst arr21) (fst arr12) (fst arr22);
  map_seq2_append f2
    (snd arr11) (snd arr21) (snd arr12) (snd arr22)

let split_aux_composable_op (#a: Type) (n: nat)
  (arr: array a #n)
  (j: nat{j <= n})
  : Lemma
  (let v1, v2 = split_aux n (fst arr) j in
  let p1, p2 = split_aux n (snd arr) j in
  composable (v1, p1) (v2, p2) /\
  op (v1, p1) (v2, p2) == arr)
  =
  let v1, v2 = split_aux n (fst arr) j in
  let p1, p2 = split_aux n (snd arr) j in
  assert (slice v1 0 j == slice (fst arr) 0 j);
  assert (slice v2 j n == slice (fst arr) j n);
  assert (slice p1 j n == null_perm_seq (n -j));
  assert (slice p2 0 j == null_perm_seq j);
  let arr1 = v1, p1 in
  let arr2 = v2, p2 in
  let r = op arr1 arr2 in
  let arr11, arr12 = selfcompose_split_aux j arr1 in
  let arr21, arr22 = selfcompose_split_aux j arr2 in
  let r1, r2 = selfcompose_split_aux j r in

  selfcompose_merge2 j arr1 arr2;
  assert (r == selfcompose_merge_aux
    (op arr11 arr21)
    (op arr12 arr22)
  );
  selfcompose_merge_split_bij j r;
  assert (selfcompose_merge_aux r1 r2 == r);
  selfcompose_split_merge_bij j (op arr11 arr21) (op arr12 arr22);

  assert (op arr11 arr21 == r1);
  lem_commutative #a #j arr21 arr11;
  op_none_id arr21 arr11 r1;
  assert (arr11 == r1);

  assert (op arr12 arr22 == r2);
  op_none_id arr12 arr22 r2;
  assert (arr22 == r2);

  assert (fst arr11 == slice (fst arr) 0 j);
  assert (fst arr22 == slice (fst arr) j n);
  assert (fst r == fst arr);
  assert (snd r == snd arr)

let split (#a: Type) (n: nat)
  (r: array_ref a #n)
  (i1: nat)
  (i2: nat{i1 <= i2 /\ i2 <= n})
  (j: nat{i1 <= j /\ j <= i2})
  (p: lseq (option perm) n{perm_ok p /\ zeroed (i1, i2) p})
  (v: lseq (option a) n{forall (i:nat{i < n}).
    Some? (index p i) = Some? (index v i)})
  (subv: lseq a (i2 - i1){slice v i1 i2 == to_some subv})
  : Steel (lseq a (i2 - i1))
  (pts_to #a #n r i1 i2 p v subv)
  (fun _ ->
    pts_to #a #n r i1 j
      (fst (split_aux n p j))
      (fst (split_aux n v j))
      (fst (split subv (j - i1)))
    `star`
    pts_to #a #n r j i2
      (snd (split_aux n p j))
      (snd (split_aux n v j))
      (snd (split subv (j - i1)))
  )
  (requires fun _ -> True)
  (ensures fun _ _ _ ->
    let v1, v2 = split_aux n v j in
    let p1, p2 = split_aux n p j in
    let subv1, subv2 = split subv (j - i1) in
    composable (v1, p1) (v2, p2) /\
    Seq.append subv1 subv2 == subv)
  =
  rewrite_slprop
    (pts_to #a #n r i1 i2 p v subv)
    (PR.pts_to #(array a #n) #pcm_array r (v, p))
    (fun m -> lemma_usersl_to_pcmsl r i1 i2 p v subv m);
  let v1, v2 = split_aux n v j in
  let p1, p2 = split_aux n p j in
  let c1 : array a #n = (v1, p1) in
  let c2 : array a #n = (v2, p2) in
  let c : array a #n = (v, p) in
  let subv1, subv2 = split subv (j - i1) in
  assert (composable c1 c2);
  split_aux_composable_op n c j;
  assert (op c1 c2 == c);
  PR.split r (v, p)
    (fst (split_aux n v j), fst (split_aux n p j))
    (snd (split_aux n v j), snd (split_aux n p j));
  split_aux_lemma n p i1 i2 j;
  assert (perm_ok p1);
  assert (perm_ok p2);
  assert (zeroed (i1, j) p1);
  assert (zeroed (j, i2) p2);
  lemma_split subv (j - i1);
  assert (Seq.append subv1 subv2 == subv);
  split_aux_slice n c i1 i2 subv j;
  assert (slice (fst (split_aux n v j)) i1 j
  == to_some #a #(j - i1) (fst (split subv (j - i1))));
  assert (slice (snd (split_aux n v j)) j i2
  == to_some #a #(i2 - j) (snd (split subv (j - i1))));
  rewrite_slprop
    (PR.pts_to #(array a #n) #pcm_array r
      (fst (split_aux n v j), fst (split_aux n p j)))
    (pts_to #a #n r i1 j
      (fst (split_aux #perm n p j))
      (fst (split_aux #a n v j))
      (fst (split #a subv (j - i1)))
    )
    (fun m -> lemma_pcmsl_to_usersl #a #n r i1 j
      (fst (split_aux #perm n p j))
      (fst (split_aux #a n v j))
      (fst (split #a subv (j - i1)))
    m);
  rewrite_slprop
    (PR.pts_to #(array a #n) #pcm_array r
      (snd (split_aux n v j), snd (split_aux n p j)))
    (pts_to #a #n r j i2
      (snd (split_aux n p j))
      (snd (split_aux n v j))
      (snd (split subv (j - i1)))
    )
    (fun m -> lemma_pcmsl_to_usersl r j i2
      (snd (split_aux n p j))
      (snd (split_aux n v j))
      (snd (split subv (j - i1)))
    m);
  return subv
