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
  = fun (arr1 arr2: seq (a & perm)) ->
  length arr1 == length arr2 /\
  (forall (i:nat{i < length arr1}).
    comp_prop (index arr1 i) (index arr2 i)
  )

let content (a: Type u#1) : Type u#1
  = x:(seq a & seq perm){length (fst x) == length (snd x)}
let array2 (a: Type u#1) : Type u#1 = option (content a)

let composable2' (#a: Type) : symrel (content a)
  = fun (arr1 arr2: content a) ->
  let arr1 = zip (fst arr1) (snd arr1) in
  let arr2 = zip (fst arr2) (snd arr2) in
  composable' arr1 arr2

let composable (#a: Type) : symrel (array a)
  = fun (arr1 arr2: array a)
  -> match arr1, arr2 with
  | None, _
  | _,  None -> True
  | Some c1, Some c2 -> composable' c1 c2

let composable2 (#a: Type) : symrel (array2 a)
  = fun (arr1 arr2: array2 a)
  -> match arr1, arr2 with
  | None, _
  | _, None -> True
  | Some c1, Some c2 -> composable2' c1 c2

let composable2'_to_len_eq (#a: Type) (arr1 arr2: content a)
  : Lemma
  (requires composable2' arr1 arr2)
  (ensures length (fst arr1) == length (fst arr2))
  =
  zip_len (fst arr1) (snd arr1);
  zip_len (fst arr2) (snd arr2);
  ()

let f (#a: Type) : a & perm -> a & perm -> a & perm =
  fun x y -> (fst x, (sum_perm (snd x) (snd y)))

let op' (#a: Type)
  (s1: seq (a & perm)) (s2: seq (a & perm){length s1 == length s2})
  : (r:seq (a & perm){length r == length s1})
  =
  map_seq2_len f s1 s2;
  map_seq2 f s1 s2

let op2' (#a: Type)
  (s1: content a) (s2: content a{length (fst s1) == length (fst s2)})
  : (r: content a{length (fst r) == length (fst s1)})
  =
  assert (length (fst s1) == length (snd s1));
  assert (length (fst s2) == length (snd s2));
  assert (length (fst s1) == length (fst s2));
  zip_len (fst s1) (snd s1);
  zip_len (fst s2) (snd s2);
  let s1 : seq (a & perm) = zip (fst s1) (snd s1) in
  let s2 : seq (a & perm) = zip (fst s2) (snd s2) in
  assert (length s1 == length s2);
  let r = op' s1 s2 in
  unzip_len r;
  unzip r

let op (#a: Type)
  (arr1: array a) (arr2: array a {composable arr1 arr2})
  : array a
  = match arr1, arr2 with
  | None, f
  | f, None -> f
  | Some s1, Some s2 -> Some (op' s1 s2)

let op2 (#a: Type)
  (arr1: array2 a) (arr2: array2 a {composable2 arr1 arr2})
  = match arr1, arr2 with
  | None, f
  | f, None -> f
  | Some s1, Some s2 ->
      assert (composable2' s1 s2);
      composable2'_to_len_eq s1 s2;
      Some (op2' s1 s2)

let pcm_array' (#a: Type) : pcm' (array a) = {
  composable = composable;
  op = op;
  one = None;
}

let pcm_array2' (#a: Type) : pcm' (array2 a) = {
  composable = composable2;
  op = op2;
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

let lem_commutative2 (#a: Type)
  (arr1: array2 a) (arr2: array2 a {composable2 arr1 arr2})
  : Lemma (op2 arr1 arr2 == op2 arr2 arr1)
  = match arr1, arr2 with
  | None, _
  | _, None -> ()
  | Some s1, Some s2 ->
      zip_len (fst s1) (snd s1);
      zip_len (fst s2) (snd s2);
      let s1 : seq (a & perm) = zip (fst s1) (snd s1) in
      let s2 : seq (a & perm) = zip (fst s2) (snd s2) in
      lem_commutative (Some s1) (Some s2)

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

let composable_to_composable2 (#a: Type) (arr1 arr2: array a)
  : Lemma
  (requires
    Some? arr1 /\
    Some? arr2 /\
    composable arr1 arr2)
  (ensures (
    let arr1' = unzip (Some?.v arr1) in
    let arr2' = unzip (Some?.v arr2) in
    unzip_len (Some?.v arr1);
    unzip_len (Some?.v arr2);
    composable2 (Some arr1') (Some arr2')))
  = admit ()

let composable_op_to_composable2_op (#a: Type)
  (arr1 arr2 arr3: array a)
  : Lemma
  (requires
    Some? arr1 /\
    Some? arr2 /\
    Some? arr3 /\
    composable arr2 arr3 /\
    composable arr1 (op arr2 arr3))
  (ensures (
    let arr1' = unzip (Some?.v arr1) in
    let arr2' = unzip (Some?.v arr2) in
    let arr3' = unzip (Some?.v arr3) in
    unzip_len (Some?.v arr1);
    unzip_len (Some?.v arr2);
    unzip_len (Some?.v arr3);
    composable2 (Some arr2') (Some arr3') /\
    composable2 (Some arr1') (op2 (Some arr2') (Some arr3'))))
  = admit ()

let composable2_to_composable (#a: Type) (arr1 arr2: array2 a)
  : Lemma
  (requires
    Some? arr1 /\
    Some? arr2 /\
    composable2 arr1 arr2)
  (ensures (
    let arr1' = zip (fst (Some?.v arr1)) (snd (Some?.v arr1)) in
    let arr2' = zip (fst (Some?.v arr2)) (snd (Some?.v arr2)) in
    zip_len (fst (Some?.v arr1)) (snd (Some?.v arr1));
    zip_len (fst (Some?.v arr2)) (snd (Some?.v arr2));
    composable (Some arr1') (Some arr2')))
  = ()

let composable2_op_to_composable_op (#a: Type)
  (arr1 arr2 arr3: array2 a)
  : Lemma
  (requires
    Some? arr1 /\
    Some? arr2 /\
    Some? arr3 /\
    composable2 arr2 arr3 /\
    composable2 arr1 (op2 arr2 arr3))
  (ensures (
    let arr1' = zip (fst (Some?.v arr1)) (snd (Some?.v arr1)) in
    let arr2' = zip (fst (Some?.v arr2)) (snd (Some?.v arr2)) in
    let arr3' = zip (fst (Some?.v arr3)) (snd (Some?.v arr3)) in
    zip_len (fst (Some?.v arr1)) (snd (Some?.v arr1));
    zip_len (fst (Some?.v arr2)) (snd (Some?.v arr2));
    zip_len (fst (Some?.v arr3)) (snd (Some?.v arr3));
    composable (Some arr2') (Some arr3') /\
    composable (Some arr1') (op (Some arr2') (Some arr3'))
  ))
  = admit ()

let op_eq_to_op2_eq (#a: Type)
  (arr1 arr2 arr3: array a)
  : Lemma
  (requires
    Some? arr1 /\
    Some? arr2 /\
    composable arr1 arr2 /\
    arr3 == op arr1 arr2
  )
  (ensures (
    unzip_len (Some?.v arr1);
    unzip_len (Some?.v arr2);
    unzip_len (Some?.v arr3);
    let arr1' = Some (unzip (Some?.v arr1)) in
    let arr2' = Some (unzip (Some?.v arr2)) in
    let arr3' = Some (unzip (Some?.v arr3)) in
    composable_to_composable2 arr1 arr2;
    assert (composable2 arr1' arr2');
    admit ();
    //Classical.forall_intro (zip_unzip_id #(a & perm));
    arr3' == op2 arr1' arr2'
  ))
  = admit ()

let lem_assoc2 (#a: Type)
  (arr1 arr2 arr3: array2 a)
  : Lemma
  (requires
    composable2 arr2 arr3 /\
    composable2 arr1 (op2 arr2 arr3)
  )
  (ensures
    composable2 arr1 arr2 /\
    composable2 (op2 arr1 arr2) arr3 /\
    op2 arr1 (op2 arr2 arr3) == op2 (op2 arr1 arr2) arr3
  )
  =
  if None? arr1 then () else
  if None? arr2 then () else
  if None? arr3 then () else begin
    let s1 = Some?.v arr1 in
    let s2 = Some?.v arr2 in
    let s3 = Some?.v arr3 in
    zip_len (fst s1) (snd s1);
    zip_len (fst s2) (snd s2);
    zip_len (fst s3) (snd s3);
    let s1 : seq (a & perm) = zip (fst s1) (snd s1) in
    let s2 : seq (a & perm) = zip (fst s2) (snd s2) in
    let s3 : seq (a & perm) = zip (fst s3) (snd s3) in
    composable2_to_composable arr2 arr3;
    composable2_op_to_composable_op arr1 arr2 arr3;
    lem_assoc (Some s1) (Some s2) (Some s3);
    assert (
      composable (Some s1) (Some s2) /\
      composable (op (Some s1) (Some s2)) (Some s3) /\
      op (Some s1) (op (Some s2) (Some s3))
      == op (op (Some s1) (Some s2)) (Some s3)
    );
    assert (
      composable (Some s1) (Some s2) /\
      composable (Some s3) (op (Some s1) (Some s2))
    );
    composable_op_to_composable2_op (Some s3) (Some s1) (Some s2);
    Classical.forall_intro_2 (unzip_zip_id #a #perm);
    op_eq_to_op2_eq (Some s1) (Some s2) (op (Some s1) (Some s2));
    op_eq_to_op2_eq
      (Some s1) (op (Some s2) (Some s3))
      (op (Some s1) (op (Some s2) (Some s3)));
    admit ();
    op_eq_to_op2_eq
      (op (Some s1) (Some s2)) (Some s3)
      (op (op (Some s2) (Some s3)) (Some s3));
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

let lem_assoc_l2 (#a: Type)
  (arr1 arr2: array2 a) (arr3: array2 a{
    composable2 arr2 arr3 /\ composable2 arr1 (op2 arr2 arr3)
  })
  : Lemma (
    composable2 arr1 arr2 /\
    composable2 (op2 arr1 arr2) arr3 /\
    op2 arr1 (op2 arr2 arr3) == op2 (op2 arr1 arr2) arr3
  )
  =
  lem_assoc2 arr1 arr2 arr3

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

let lem_assoc_r2 (#a: Type)
  (arr1 arr2: array2 a) (arr3: array2 a{
    composable2 arr1 arr2 /\ composable2 (op2 arr1 arr2) arr3
  })
  : Lemma (
    composable2 arr2 arr3 /\
    composable2 arr1 (op2 arr2 arr3) /\
    op2 arr1 (op2 arr2 arr3) == op2 (op2 arr1 arr2) arr3
  )
  =
  lem_commutative2 arr1 arr2;
  lem_assoc2 arr3 arr2 arr1;
  lem_commutative2 arr2 arr3;
  lem_commutative2 arr1 (op2 arr2 arr3);
  lem_commutative2 arr3 (op2 arr1 arr2)

let pcm_array (#a: Type) : pcm (array a) = {
  p = pcm_array';
  comm = lem_commutative;
  assoc = lem_assoc_l;
  assoc_r = lem_assoc_r;
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

let pcm_array2 (#a: Type) : pcm (array2 a) = {
  p = pcm_array2';
  comm = lem_commutative2;
  assoc = lem_assoc_l2;
  assoc_r = lem_assoc_r2;
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

//val array_ref (a: Type u#0) : Type u#0
let array_ref (a: Type u#1) : Type u#0
  = Mem.ref (array a) pcm_array

let array_ref2 (a: Type u#1) : Type u#0
  = Mem.ref (array2 a) pcm_array2

let null #a = Mem.null #(array a) #pcm_array
let null2 #a = Mem.null #(array2 a) #pcm_array2

let is_null #a r = Mem.is_null #(array a) #pcm_array r
let is_null2 #a r = Mem.is_null #(array2 a) #pcm_array2 r

let perm_ok_elem p : prop = (p.v <=. one == true) /\ True

let perm_ok #a (s: seq (a & perm)) : prop
  =
  forall i. ((snd (index s i)).v <=. one == true)


let perm_ok3 (#a: Type) (#n: nat) (s: lseq a n & lseq perm n) : prop
  =
  forall i. ((index (snd s) i).v <=. one == true)

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

let composable_to_fst_unzip_eq (#a: Type u#a)
  (s1 s2: seq (a & perm))
  : Lemma
  (requires composable' s1 s2)
  (ensures fst (unzip s1) == fst (unzip s2))
  =
  unzip_len s1;
  unzip_len s2;
  Classical.forall_intro (unzip_index s1);
  Classical.forall_intro (unzip_index s2);
  Seq.lemma_eq_elim (fst (unzip s1)) (fst (unzip s2))

let op_to_fst_unzip_eq (#a: Type u#a)
  (s1 s2 s3: seq (a & perm))
  : Lemma
  (requires
    composable' s1 s2 /\
    s3 == op' s1 s2)
  (ensures
    fst (unzip s1) == fst (unzip s3))
  =
  unzip_len s1;
  unzip_len s2;
  unzip_len s3;
  Classical.forall_intro (unzip_index s1);
  Classical.forall_intro (unzip_index s2);
  Classical.forall_intro (unzip_index s3);
  Classical.forall_intro (map_seq2_index f s1 s2);
  Seq.lemma_eq_elim (fst (unzip s1)) (fst (unzip s3))

let pts_to_ref_injective
  (#a: Type u#1)
  (r: array_ref a)
  (v0 v1: seq (a & perm))
  (m:Mem.mem)
  : Lemma
    (requires
      Mem.interp (pts_to_sl r v0 `Mem.star` pts_to_sl r v1) m)
    (ensures
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
    composable_to_fst_unzip_eq v0 v1

let pts_to_not_null (#a:Type u#1)
                    (r:array_ref a)
                    (v:seq (a & perm))
                    (m:Mem.mem)
  : Lemma (requires Mem.interp (pts_to_sl r v) m)
          (ensures r =!= null)
  = Mem.affine_star
      (hp_of (pts_to_raw r v))
      (Mem.pure (perm_ok v)) m;
    Mem.pts_to_not_null r (Some v) m

let aux' (#a: Type u#1)
  (x y f1 f2 z: array a)
  : Lemma
  (requires
    Some? x /\
    Some? y /\
    composable x f1 /\
    op f1 x == z /\
    composable y f2 /\
    op f2 y == z
  )
  (ensures fst (unzip (Some?.v x)) == fst (unzip (Some?.v y)))
  =
  assert (Some? z);
  match (Some? f1, Some? f2) with
  | false, false -> ()
  | true, false ->
    assert (op f2 y == y);
    assert (y == z);
    composable_to_fst_unzip_eq (Some?.v x) (Some?.v f1);
    op_to_fst_unzip_eq (Some?.v f1) (Some?.v x) (Some?.v z)
  | false, true ->
    assert (op f1 x == x);
    assert (x == z);
    composable_to_fst_unzip_eq (Some?.v y) (Some?.v f2);
    op_to_fst_unzip_eq (Some?.v f2) (Some?.v y) (Some?.v z)
  | true, true ->
    composable_to_fst_unzip_eq (Some?.v x) (Some?.v f1);
    composable_to_fst_unzip_eq (Some?.v y) (Some?.v f2);
    op_to_fst_unzip_eq (Some?.v f1) (Some?.v x) (Some?.v z);
    op_to_fst_unzip_eq (Some?.v f2) (Some?.v y) (Some?.v z)

//#push-options "--z3rlimit 300 --query_stats"
let aux (#a: Type u#1)
  (r: array_ref a)
  (x y: erased (seq (a & perm))) (m:Mem.mem)
  : Lemma
  (requires (
    Mem.interp (pts_to_sl r x) m /\
    Mem.interp (pts_to_sl r y) m /\
    snd (unzip x) == snd (unzip y)
  ))
  (ensures (fst (unzip x) == fst (unzip y)))
  =
  Mem.pts_to_join r (Some (reveal x)) (Some (reveal y)) m;
  assert (joinable pcm_array (Some (reveal x)) (Some (reveal y)));
  assert (exists z.
    compatible pcm_array (Some (reveal x)) z /\
    compatible pcm_array (Some (reveal y)) z
  );
  assert (
    let x' = Some (reveal x) in
    let y' = Some (reveal y) in
    exists z.
    (exists (frame: array a).
      composable x' frame /\
      op frame x' == z) /\
    (exists (frame: array a).
      composable y' frame /\
      op frame y' == z)
  );
  assert (
    let x' = Some (reveal x) in
    let y' = Some (reveal y) in
    exists (z f1 f2: array a).
      composable x' f1 /\
      op f1 x' == z /\
      composable y' f2 /\
      op f2 y' == z /\
      Some? z
  );
  Classical.forall_intro_3 (
    Classical.move_requires_3 (
        aux' (Some (reveal x)) (Some (reveal y))
    )
  );
  ()

// 1) better definition
// 2) a pts_to wrapper? an unwrapped PCM based on the wrapped one?
// seems relatively reasonable so far...
let pts_to_witinv_aux (#a:Type) (r:array_ref a) (s2: seq perm)
  : Lemma (
  Mem.is_witness_invariant
  (fun (s1: seq a{length s1 == length s2}) ->
  pts_to_sl r (zip s1 s2)))
  =
  Classical.forall_intro_3 (
    fun (x y: (s1:seq a{length s1 == length s2})) ->
    (
    zip_len x s2;
    zip_len y s2;
    Classical.forall_intro (zip_index x s2);
    Classical.forall_intro (zip_index y s2);
    assume (snd (unzip (zip x s2)) == snd (unzip (zip y s2)));
    Classical.move_requires (aux r (zip x s2) (zip y s2))
    )
  )
