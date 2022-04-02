module Steel.Array8

open FStar.Ghost
//open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open FStar.Real
open FStar.PCM
open Steel.FractionalPermission
module RP = Steel.PCMReference
module Mem = Steel.Memory

#set-options "--ide_id_info_off"

open FStar.Seq
open FStar.Mul
module M = FStar.Math.Lib


type set = s:(nat & nat){fst s < snd s}

let is_in (pos: nat) (s: set) : bool
  = fst s <= pos && pos < snd s

let zeroed (#a: Type) (bounds: set) (s: seq (a & option perm))
  = forall i.
    let b = is_in i (bounds) in
    (b ==> Some? (snd (index s i))) /\
    (not b ==> None? (snd (index s i)))


noeq type contents (a: Type0) = {
  size: nat;
  bounds: set;
  data: d:(seq (a & option perm)){
    zeroed bounds d /\ length d = size
  };
}

let get_bounds #a (c: contents a) = c.bounds
let get_size #a (c: contents a) = c.size
let get_data #a (c: contents a) = c.data

let mk_contents #a size bounds data : contents a = {
  size;
  bounds;
  data;
}

let array (a: Type0) = option (contents a)

let sum_perm_opt (p1 p2: option perm) : option perm
  = match p1, p2 with
  | None, p
  | p, None -> p
  | Some p1, Some p2 -> Some (sum_perm p1 p2)
let sum_perm_opt_comm (p1 p2: option perm)
  : Lemma
  (sum_perm_opt p1 p2 == sum_perm_opt p2 p1)
  = ()
let sum_perm_opt_assoc (p1 p2 p3: option perm)
  : Lemma
    (sum_perm_opt p1 (sum_perm_opt p2 p3)
  == sum_perm_opt (sum_perm_opt p1 p2) p3)
  = ()

let comp_prop (#a: Type) (x y: a & option perm)
  =
  let p = sum_perm_opt (snd x) (snd y) in
  (fst x == fst y) /\
  (None? p \/ ((Some?.v p).v <=. one))

let composable (#a: Type) : symrel (array a)
  = fun (arr1 arr2: array a)
  -> match arr1, arr2 with
  | None, _
  | _,  None -> True
  | Some c1, Some c2 ->
  let s1 = get_data c1 in
  let s2 = get_data c2 in
  let i1, i2 = get_bounds c1 in
  let j1, j2 = get_bounds c2 in
  //length s1 == length s2 /\
  get_size c1 == get_size c2 /\
  ((i1 == j1 /\ i2 == j2) \/ (j1 == i2) \/ (i1 == j2)) /\
  (forall i. (0 <= i /\ i < length s1) ==>
    (let x = index s1 i in
    let y = index s2 i in
    comp_prop x y
  ))

val map_seq2 (#a #b #c: Type) (f:a -> b -> Tot c)
  (s1:Seq.seq a) (s2:Seq.seq b{length s1 = length s2})
  : Tot (x:Seq.seq c{
    length x = length s1 /\
    (forall i. index x i == f (index s1 i) (index s2 i))
  })
val map_seq2_len (#a #b #c: Type) (f:a -> b -> Tot c)
  (s1:Seq.seq a) (s2:Seq.seq b{length s1 = length s2})
  : Lemma (length (map_seq2 #a #b #c f s1 s2) == length s1)
val map_seq2_comm (#a #c: Type)
  (f:a -> a -> Tot c) (s1 s2:Seq.seq a)
  : Lemma
  (requires
    length s1 == length s2 /\
    (forall i. (i <= 0 /\ i < length s1) ==>
      (let x = index s1 i in
      let y = index s2 i in
      f x y == f y x))
  )
  (ensures
    map_seq2 f s1 s2 == map_seq2 f s2 s1
  )
val map_seq2_assoc (#a: Type)
  (f:a -> a -> Tot a) (s1 s2 s3:Seq.seq a)
  : Lemma
  (requires
    length s1 == length s2 /\
    length s2 == length s3 /\
    (forall i. (i <= 0 /\ i < length s1) ==>
      (let x = index s1 i in
      let y = index s2 i in
      let z = index s3 i in
      f (f x y) z == f x (f y z)))
  )
  (ensures
       map_seq2 f (map_seq2 f s1 s2) s3
    == map_seq2 f s1 (map_seq2 f s2 s3)
  )

let f (#a: Type)
  : a & option perm -> a & option perm -> a & option perm =
  fun x y -> (fst x, sum_perm_opt (snd x) (snd y))

let adjacent (s1 s2: set) : bool =
  s1 = s2 ||
  (fst s2 = snd s1) ||
  (fst s1 = snd s2)

let union (s1: set) (s2: set{adjacent s1 s2}) : set
  = M.min (fst s1) (fst s2), M.max (snd s1) (snd s2)
let union_comm (s1: set) (s2: set{adjacent s1 s2})
  : Lemma (union s1 s2 == union s2 s1)
  = ()

let op (#a: Type)
  (arr1: array a) (arr2: array a {composable arr1 arr2})
  : array a
  = match arr1, arr2 with
  | None, f
  | f, None -> f
  | Some c1, Some c2 ->
      let i1, i2 = get_bounds c1 in
      let j1, j2 = get_bounds c2 in
      let new_bounds = union (i1, i2) (j1, j2) in
      let new_size = get_size c1 in
      let new_contents =
        map_seq2 f (get_data c1) (get_data c2) in
      Some (mk_contents new_size new_bounds new_contents)

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
      let i1, i2 = get_bounds c1 in
      let j1, j2 = get_bounds c2 in
      union_comm (i1, i2) (j1, j2);
      assert (get_size c1 == get_size c2);
      map_seq2_comm f (get_data c1) (get_data c2);
      ()

let lem_assoc_l_eq (#a: Type)
  (arr1 arr2 arr3: array a)
  : Lemma
  (requires
    Some? arr1 /\ Some? arr2 /\ Some? arr3 /\
    (let c1, c2, c3 = Some?.v arr1, Some?.v arr2, Some?.v arr3 in
    composable arr1 arr2 /\
    composable arr2 arr3 /\
    composable (op arr1 arr2) arr3 /\
    composable arr1 (op arr2 arr3)))
  (ensures
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3)
  =
  let c1, c2, c3 = Some?.v arr1, Some?.v arr2, Some?.v arr3 in
  let s1, s2, s3 = get_data c1, get_data c2, get_data c3 in
  map_seq2_assoc f s1 s2 s3

let lem_assoc_l_aux (#a: Type)
  (s1 s2: seq (a & option perm))
  (s3: seq (a & option perm){
    length s1 == length s2 /\
    length s2 == length s3})
  (i: nat{0 <= i /\ i < length s1})
  : Lemma
  (requires
    (let x1 = index s1 i in
    let x2 = index s2 i in
    let x3 = index s3 i in
    let x23 = f x2 x3 in
    comp_prop x2 x3 /\
    comp_prop x1 x23
  ))
  (ensures
    comp_prop (index s1 i) (index s2 i)
    ///\ comp_prop (f (index s1 i) (index s2 i)) (index s3 i)
  )
  = ()

let lem_assoc_l_composable (#a: Type)
  (arr1 arr2 arr3: array a)
  : Lemma
  (requires
    Some? arr1 /\
    Some? arr2 /\
    Some? arr3 /\
    composable arr2 arr3 /\
    composable arr1 (op arr2 arr3)
  )
  (ensures
    composable arr1 arr2 /\
    composable (op arr1 arr2) arr3
  )
  =
  let c1, c2, c3 = Some?.v arr1, Some?.v arr2, Some?.v arr3 in
  let s1, s2, s3 = get_data c1, get_data c2, get_data c3 in
  let arr23 = op arr2 arr3 in
  assert (Some? arr23);
  let s23 = get_data (Some?.v arr23) in
  assert (length s2 == length s3);
  assert (length s1 == length s23);
  assert (length s23 == length s2);

  assert (composable arr2 arr3);
  assert (forall i. (0 <= i /\ i < length s1) ==>
    (let x2 = index s2 i in
    let x3 = index s3 i in
    comp_prop x2 x3
  ));

  assert (composable arr1 (op arr2 arr3));
  assert (forall i. (0 <= i /\ i < length s1) ==>
    (let x1 = index s1 i in
    let x2 = index s2 i in
    let x3 = index s3 i in
    //let x23 = index s23 i in
    //f x2 x3 == x23 /\
    comp_prop x1 (f x2 x3)
  ));

  assert (forall i. (0 <= i /\ i < length s1) ==>
    (let x1 = index s1 i in
    let x2 = index s2 i in
    let x3 = index s3 i in
    comp_prop x2 x3 /\
    comp_prop x1 (f x2 x3)
  ));


  // TODO
  admit ();
  Classical.forall_intro (
    Classical.move_requires (
    fun i -> lem_assoc_l_aux s1 s2 s3 i
    )
  )

let lem_assoc_l (#a: Type)
  (arr1 arr2: array a) (arr3: array a{
    composable arr2 arr3 /\ composable arr1 (op arr2 arr3)}
  )
  : Lemma (
    composable arr1 arr2 /\
    composable (op arr1 arr2) arr3 /\
    op arr1 (op arr2 arr3) == op (op arr1 arr2) arr3
  )
  =
  if None? arr1 then () else
  if None? arr2 then () else
  if None? arr3 then () else
  assert (Some? arr1);
  ///\ Some? arr2 /\ Some? arr3);
  // TODO : wtf
  admit ();
  lem_assoc_l_composable arr1 arr2 arr3;
  ()


let pcm_array (#a: Type) : pcm (array a) = {
  p = pcm_array';
  comm = lem_commutative;
  assoc = lem_assoc_l; // in progress
  assoc_r = (fun _ _ _ -> admit (); ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

let array_ref a = Mem.ref (array a) pcm_array
