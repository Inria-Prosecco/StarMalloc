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

noeq type content (a: Type0) = {
  //size: nat;
  //i1: nat;
  //i2: nat;
  data: seq (a & perm);
}

let mk_content (#a: Type0) (data: seq (a & perm)) : content a
  = { data }

let get_data (#a: Type0) (content: content a) = content.data

let array (a: Type0) = option (content a)

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
  | Some c1, Some c2 ->
      composable' (get_data c1) (get_data c2)

let f (#a: Type) : a & perm -> a & perm -> a & perm =
  fun x y -> (fst x, (sum_perm (snd x) (snd y)))

let op' (#a: Type)
  (s1: seq (a & perm)) (s2: seq (a & perm){length s1 == length s2})
  : seq (a & perm)
  = map_seq2 f s1 s2

let op (#a: Type)
  (arr1: array a) (arr2: array a {composable arr1 arr2})
  : array a
  = match arr1, arr2 with
  | None, f
  | f, None -> f
  | Some c1, Some c2 ->
      let new_data = op' (get_data c1) (get_data c2) in
      Some (mk_content new_data)

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
  | Some c1, Some c2 ->
    let s1 = get_data c1 in
    let s2 = get_data c2 in
    assert (
       forall i. (i <= 0 /\ i < length s1) ==>
       (let x = index s1 i in
       let y = index s2 i in
       comp_prop x y
    ));
    assert (
       forall i. (i <= 0 /\ i < length s1) ==>
       (let x = index s1 i in
       let y = index s2 i in
       f x y == f y x)
    );
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
  let s1 = get_data (Some?.v arr1) in
  let s2 = get_data (Some?.v arr2) in
  let s3 = get_data (Some?.v arr3) in
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
  let s1 = get_data (Some?.v arr1) in
  let s2 = get_data (Some?.v arr2) in
  let s3 = get_data (Some?.v arr3) in
  let arr23 = op arr2 arr3 in
  assert (Some? arr23);
  let s23 = get_data (Some?.v arr23) in

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
  let s12 = get_data (Some?.v arr12) in
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

let array_ref a = Mem.ref (array a) pcm_array
let null #a = Mem.null #(array a) #pcm_array
let is_null #a r = Mem.is_null #(array a) #pcm_array r

let perm_ok p : prop = (p.v <=. one == true) /\ True

let apply (#a: Type) (s: seq (a & perm)) (p: perm) : seq (a & perm)
  =
  let s, _ = unzip s in
  map_seq (fun x -> x, p) s

// seq (a & perm) or seq a & seq perm?
// tentative
let pts_to_raw_sl (#a: Type)
  (r: array_ref a) (p: perm) (v: content a) : Mem.slprop
  =
  let array_with_perm = apply (get_data v) p in
  Mem.pts_to r (Some (mk_content array_with_perm))
