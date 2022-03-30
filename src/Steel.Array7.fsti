module Steel.Array7

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

let array (a: Type u#1) : Type u#1 = option (seq (a & perm))

let comp_prop (#a: Type) (x y: a & perm)
  = fst x == fst y /\ (sum_perm (snd x) (snd y)).v <=. one

let composable' (#a: Type) : symrel (seq (a & perm))
  = fun (arr1 arr2: seq (a & perm))  ->
  length arr1 == length arr2 /\
  (forall (i:nat{i < length arr1}).
    comp_prop (index arr1 i) (index arr2 i)
  )

let composable (#a: Type) : symrel (array a)
  = fun (arr1 arr2: array a)
  -> match arr1, arr2 with
  | None, _
  | _,  None -> True
  | Some c1, Some c2 -> composable' c1 c2

let f (#a: Type) : a & perm -> a & perm -> a & perm =
  fun x y -> (fst x, (sum_perm (snd x) (snd y)))

let op' (#a: Type)
  (s1: seq (a & perm)) (s2: seq (a & perm){length s1 == length s2})
  : (r:seq (a & perm){length r == length s1})
  =
  map_seq2_len f s1 s2;
  map_seq2 f s1 s2

let op (#a: Type)
  (arr1: array a) (arr2: array a {composable arr1 arr2})
  : array a
  = match arr1, arr2 with
  | None, f
  | f, None -> f
  | Some s1, Some s2 -> Some (op' s1 s2)

let pcm_array' (#a: Type) : pcm' (array a) = {
  composable = composable;
  op = op;
  one = None;
}

let lem_commutative (#a: Type)
  (arr1: array a) (arr2: array a {composable arr1 arr2})
  : Lemma (op arr1 arr2 == op arr2 arr1)
  = match arr1, arr2 with
  | None, _
  | _, None -> ()
  | Some s1, Some s2 ->
    assert (composable arr1 arr2);
    assert (length s1 == length s2);
    map_seq2_comm f s1 s2

let lem_assoc_l_eq (#a: Type)
  (arr1 arr2 arr3: array a)
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
  assert (
    forall i. (i <= 0 /\ i < length s1) ==>
    (let x = index s1 i in
    let y = index s2 i in
    let z = index s3 i in
    f x (f y z) == f (f x y) z)
  );
  map_seq2_assoc f s1 s2 s3

let lem_assoc_l_aux1 (#a: Type)
  (s1 s2 s3 s23: seq (a & perm))
  (i: nat)
  : Lemma
  (requires
    length s1 == length s2 /\
    length s2 == length s3 /\
    length s3 == length s23 /\
    0 <= i /\ i < length s1 /\
    composable' s2 s3 /\
    s23 == op' s2 s3 /\
    comp_prop (index s2 i) (index s3 i) /\
    comp_prop (index s1 i) (index s23 i)
  )
  (ensures
    // TODO: duplicata
    0 <= i /\ i < length s1 /\
    comp_prop (index s1 i) (index s2 i))
  =
  assert (s23 == map_seq2 f s2 s3);
  Classical.forall_intro (map_seq2_index f s2 s3);
  ()

let lem_assoc_l_aux2 (#a: Type)
  (s1 s2 s3 s23 s12: seq (a & perm))
  (i: nat)
  : Lemma
  (requires
    length s1 == length s2 /\
    length s2 == length s3 /\
    length s3 == length s23 /\
    length s23 == length s12 /\
    0 <= i /\ i < length s1 /\
    composable' s2 s3 /\
    s23 == op' s2 s3 /\
    composable' s1 s2 /\
    s12 == op' s1 s2 /\
    comp_prop (index s2 i) (index s3 i) /\
    comp_prop (index s1 i) (index s23 i)
  )
  (ensures
    // TODO: duplicata
    0 <= i /\ i < length s1 /\
    comp_prop (index s12 i) (index s3 i)
  )
  =
  assert (s12 == map_seq2 f s1 s2);
  assert (s23 == map_seq2 f s2 s3);
  Classical.forall_intro (map_seq2_index f s1 s2);
  Classical.forall_intro (map_seq2_index f s2 s3);
  ()

//#push-options "--z3rlimit 20"
let lem_assoc_l_aux3 (#a: Type)
  (arr1 arr2 arr3: array a)
  : Lemma
  (requires
    Some? arr1 /\ Some? arr2 /\ Some? arr3 /\
    composable arr2 arr3 /\
    composable arr1 (op arr2 arr3)
  )
  (ensures
    composable arr1 arr2
    /\ composable (op arr1 arr2) arr3
  )
  =
  let s1 = Some?.v arr1 in
  let s2 = Some?.v arr2 in
  let s3 = Some?.v arr3 in
  let arr23 = op arr2 arr3 in
  assert (Some? arr23);
  let s23 = Some?.v arr23 in

  assert (length s2 == length s3);
  assert (length s1 == length s23);
  map_seq2_len f s2 s3;
  assert (length s23 == length s2);
  assert (length s1 == length s2);
  Classical.forall_intro (
    Classical.move_requires (
      lem_assoc_l_aux1 s1 s2 s3 s23
    )
  );
  assert (composable arr1 arr2);

  let arr12 = op arr1 arr2 in
  assert (Some? arr12);
  let s12 = Some?.v arr12 in
  map_seq2_len f s1 s2;
  assert (length s1 == length s2);
  Classical.forall_intro (
    Classical.move_requires (
      lem_assoc_l_aux2 s1 s2 s3 s23 s12
    )
  );
  ()

let lem_assoc (#a: Type)
  (arr1 arr2 arr3: array a)
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

let lem_assoc_l (#a: Type)
  (arr1 arr2: array a) (arr3: array a{
    composable arr2 arr3 /\ composable arr1 (op arr2 arr3)
  })
  : Lemma (
    composable arr1 arr2 /\
    composable (op arr1 arr2) arr3 /\
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3
  )
  =
  lem_assoc arr1 arr2 arr3

let lem_assoc_r (#a: Type)
  (arr1 arr2: array a) (arr3: array a{
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

let pcm_array (#a: Type) : pcm (array a) = {
  p = pcm_array';
  comm = lem_commutative;
  assoc = lem_assoc_l;
  assoc_r = lem_assoc_r;
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

//val array_ref (a: Type u#0) : Type u#0
let array_ref (a: Type u#1) : Type u#0
  = Mem.ref (array a) pcm_array

let null #a = Mem.null #(array a) #pcm_array
let is_null #a r = Mem.is_null #(array a) #pcm_array r

let perm_ok_elem p : prop = (p.v <=. one == true) /\ True

let perm_ok #a (s: seq (a & perm)) : prop
  =
  forall i. ((snd (index s i)).v <=. one == true)

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
let pts_to_raw_sl (#a: Type)
  (r: array_ref a) (v: seq (a & perm))
  : Mem.slprop
  = Mem.pts_to r (Some v)

let pts_to_raw (#a: Type)
  (r: array_ref a) (v: seq (a & perm))
  : vprop
  //= to_vprop (Mem.pts_to r (Some v))
  = to_vprop (pts_to_raw_sl r v)

[@@ __reduce__]
let pts_to' (#a: Type u#1)
  (r: array_ref a) (v: seq (a & perm))
  : vprop
  =
  pts_to_raw r v `star` pure (perm_ok v)

let pts_to_sl #a r v
  = hp_of (pts_to' #a r v)

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

// stuck: need to separate perm from content
let pts_to_ref_injective
  (#a: Type u#1)
  (r: array_ref a)
  //(p0 p1:perm)
  (v0 v1: seq (a & perm))
  (m:Mem.mem)
  : Lemma
    (requires
      Mem.interp (pts_to_sl r v0 `Mem.star` pts_to_sl r v1) m)
    (ensures
      //fst (unzip v0) `Seq.equal` fst (unzip v1)
      fst (unzip v0) == fst (unzip v1)
    )
  = let open Steel.Memory in
    abcd_acbd (hp_of (pts_to_raw r v0))
              (pure (perm_ok v0))
              (hp_of (pts_to_raw r v1))
              (pure (perm_ok v1));
    Mem.affine_star
      (hp_of (pts_to_raw r v0) `star` hp_of (pts_to_raw r v1))
      (pure (perm_ok v0) `star` pure (perm_ok v1)) m;
    Mem.pts_to_compatible r (Some v0)
                            (Some v1)
                            m;
    assert (composable' v0 v1);
    assert  (forall (i:nat{i < length v1}).
      comp_prop (index v0 i) (index v1 i)
    );
    assert (length v0 == length v1);
    assert  (forall (i:nat{i < length v1}).
      (let x = index v0 i in
      let y = index v1 i in
      fst x == fst y /\ (sum_perm (snd x) (snd y)).v <=. one
      )
    );
    let s0 = fst (unzip v0) in
    let s1 = fst (unzip v1) in
    unzip_len v0;
    unzip_len v1;
    assert (forall (i:nat{i < length v1}).
      fst (index v0 i) == fst (index v1 i)
    );
    Classical.forall_intro (unzip_index v0);
    Classical.forall_intro (unzip_index v1);
    assert (forall (i:nat{i < length v1}).
      index s0 i == index s1 i
    );
    Seq.lemma_eq_elim s0 s1;
    ()

let pts_to_not_null (#a:Type u#1)
                    (r:array_ref a)
                    (v:seq (a & perm))
                    (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl r v) m)
          (ensures r =!= null)
  = Mem.affine_star (hp_of (pts_to_raw r v)) (Mem.pure (perm_ok v)) m;
    Mem.pts_to_not_null r (Some v) m

[@@ expect_failure]
let pts_to_witinv (#a:Type) (r:array_ref a)
  : Lemma (Mem.is_witness_invariant (pts_to_sl r)) =
  let aux (x y: erased (seq (a & perm))) (m:Mem.mem)
    : Lemma
    (requires (
      Mem.interp (pts_to_sl r x) m /\
      Mem.interp (pts_to_sl r y) m))
    (ensures (fst (unzip x) `Seq.equal` fst (unzip y)))
    =
    Mem.pts_to_join r (Some (reveal x)) (Some (reveal y)) m;
    admit ();
    //Seq.lemma_eq_elim (fst (unzip (reveal x))) (fst (unzip (reveal y)))
    ()
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))
