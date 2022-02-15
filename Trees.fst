module Trees

module M = FStar.Math.Lib


(*** Type definitions *)

(**** The tree structure *)

type tree (a: Type) =
  | Leaf : tree a
  | Node: data: a -> left: tree a -> right: tree a -> size: nat -> tree a

let cdata (#a: Type) (t: tree a{Node? t}) =
  let Node d _ _ _ = t in d
let cleft (#a: Type) (t: tree a{Node? t}) =
  let Node _ l _ _ = t in l
let cright (#a: Type) (t: tree a{Node? t}) =
  let Node _ _ r _ = t in r
let csize (#a: Type) (t: tree a{Node? t}) =
  let Node _ _ _ s = t in s

(**** Binary search trees *)

//@BST
type cmp (a: Type) = compare: (a -> a -> int){
  squash (forall x.
    compare x x == 0) /\
  squash (forall x y.
    compare x y > 0 <==> compare y x < 0) /\
  squash (forall x y z.
    compare x y >= 0 /\ compare y z >= 0 ==> compare x z >= 0)
}

//@BST
let rec forall_keys (#a: Type) (t: tree a) (cond: a -> bool) : bool =
  match t with
  | Leaf -> true
  | Node data left right _ ->
    cond data && forall_keys left cond && forall_keys right cond

//@BST
let key_left (#a: Type) (compare:cmp a) (root key: a) : bool =
  compare key root < 0
let key_right (#a: Type) (compare : cmp a) (root key: a) : bool =
  compare key root > 0

//@BST
let rec is_bst (#a: Type) (compare : cmp a) (x: tree a) : bool =
  match x with
  | Leaf -> true
  | Node data left right _ ->
    is_bst compare left && is_bst compare right &&
    forall_keys left (key_left compare data) &&
    forall_keys right (key_right compare data)

//@Trees
let rec size_of_tree (#a: Type) (x: tree a) : Tot nat (decreases x) =
  match x with
  | Leaf -> 0
  | Node _ left right _ -> size_of_tree left + size_of_tree right + 1

//@Trees
(* is with defined size *)
let rec is_wds (#a: Type) (x: tree a)
  : Tot bool (decreases x) =
  match x with
  | Leaf -> true
  | Node data left right size ->
      let s1 = size_of_tree left in
      let s2 = size_of_tree right in
      let b1 = is_wds left in
      let b2 = is_wds right in
      let s = s1 + s2 + 1 in
      b1 && b2 && size = s

//@Trees
let wds (a: Type) = x:tree a {is_wds x}

//@BST
let bst (a: Type) (cmp:cmp a) = x:wds a {is_bst cmp x}

(*** Operations *)

(**** Lookup *)

//@BST
let rec bst_search (#a: Type) (cmp:cmp a) (x: bst a cmp) (key: a) : option a =
  match x with
  | Leaf -> None
  | Node data left right _ ->
    let delta = cmp data key in
    if delta < 0 then bst_search cmp right key else
    if delta > 0 then bst_search cmp left key else
    Some data

(**** Height *)

//@Trees
let rec height (#a: Type) (x: tree a) : nat =
  match x with
  | Leaf -> 0
  | Node data left right _ ->
    let hleft = height left in
    let hright = height right in
    if hleft > hright then hleft + 1
    else hright + 1

//@Trees.Misc
let rec height_lte_size (#a: Type) (t: tree a)
  : Lemma
  (height t <= size_of_tree t)
  =
  match t with
  | Leaf -> ()
  | Node data left right _ ->
      height_lte_size left;
      height_lte_size right

(**** Append *)

(**** Insertion *)

(**** BST insertion *)

//@Trees
let sot_wds (#a: Type) (t: wds a)
  : s:nat{size_of_tree t == s} =
  match t with
  | Leaf -> 0
  | Node _ _ _ s -> s

//@Trees
let int_of_bool b : nat = match b with
  | true -> 1
  | false -> 0

//@BST
(*
- r: in case of equality with an already existing element,
  true = replace, false = do not replace
- snd (result): whether a new element has been added,
  that is whether the size has increased
  => bad idea/bad design?
*)
let rec insert_bst2_aux (#a: Type)
  (r:bool) (cmp:cmp a) (t: bst a cmp) (new_data: a)
  : tree a & bool =
  match t with
  | Leaf -> Node new_data Leaf Leaf 1, true
  | Node data left right size ->
    let delta = cmp data new_data in
    if delta = 0 then begin
      if r then Node new_data left right size, false
           else t, false
    end
    else if delta > 0 then begin
      let new_left, b = insert_bst2_aux r cmp left new_data in
      let new_size = size + (int_of_bool b) in
      Node data new_left right new_size, b
    end else begin
      let new_right, b = insert_bst2_aux r cmp right new_data in
      let new_size = size + (int_of_bool b) in
      Node data left new_right new_size, b
    end

//@BST
let rec insert_bst2_aux_size (#a: Type)
  (r:bool) (cmp:cmp a) (t: bst a cmp) (new_data: a)
  : Lemma (
    let new_t, b = insert_bst2_aux r cmp t new_data in
    size_of_tree new_t = size_of_tree t + (int_of_bool b) /\
    is_wds new_t
  )
  = match t with
  | Leaf -> ()
  | Node data left right size ->
    let delta = cmp data new_data in
    if delta = 0 then ()
    else if delta > 0 then begin
      let new_left, b = insert_bst2_aux r cmp left new_data in
      assert (b == snd (insert_bst2_aux r cmp t new_data));
      insert_bst2_aux_size r cmp left new_data;
      let new_size = sot_wds new_left + sot_wds right + 1 in
      assert (new_size = size + (int_of_bool b));
      let new_t = Node data new_left right new_size in
      assert (new_size == size_of_tree new_t);
      assert (is_wds new_t)
    end else begin
      let new_right, b = insert_bst2_aux r cmp right new_data in
      assert (b == snd (insert_bst2_aux r cmp t new_data));
      insert_bst2_aux_size r cmp right new_data;
      let new_size = sot_wds left + sot_wds new_right + 1 in
      assert (new_size = size + (int_of_bool b));
      let new_t = Node data left new_right new_size in
      assert (new_size == size_of_tree new_t);
      assert (is_wds new_t)
    end

//@BST
let insert_bst2 (#a: Type)
  (r: bool) (cmp:cmp a) (t: bst a cmp) (new_data: a)
  : t':wds a{
    let _, b = insert_bst2_aux r cmp t new_data in
  size_of_tree t' == size_of_tree t + (int_of_bool b)}
  =
  insert_bst2_aux_size r cmp t new_data;
  fst (insert_bst2_aux r cmp t new_data)

(**** AVL insertion *)

//@AVL
let rec is_balanced (#a: Type) (x: tree a) : bool =
  match x with
  | Leaf -> true
  | Node data left right _ ->
    M.abs(height right - height left) <= 1 &&
    is_balanced(right) &&
    is_balanced(left)

//@AVL
let is_avl (#a: Type) (cmp:cmp a) (x: wds a) : prop =
  is_bst cmp x /\ is_balanced x

//@AVL
let avl (a: Type) (cmp:cmp a) = x: wds a {is_avl cmp x}

//@D/AVL?
let get (#a: Type) (v: option a{Some? v}) : a =
  let Some v' = v in v'

(*
   x            z
t1   z   =>   x   t3
   t2 t3    t1 t2
*)

//@Trees/AVL
//let rotate_left (#a: Type) (r: tree a) : option (tree a) =
//  match r with
//  | Node x t1 (Node z t2 t3 _) _ -> Some (Node z (Node x t1 t2 0) t3 0)
//  | _ -> None
let rotate_left_wds (#a: Type) (r: wds a) : option (wds a) =
  match r with
  | Node x t1 (Node z t2 t3 _) s ->
      let s12 = sot_wds t1 + sot_wds t2 + 1 in
      let t12 = Node x t1 t2 s12 in
      //induction_wds x t1 t2;
      assert (is_wds t12);
      let s123 = s12 + sot_wds t3 + 1 in
      assert (s123 == s);
      Some (Node z t12 t3 s)
  | _ -> None

(*
    x          z
  z   t3 => t1   x
t1 t2          t2 t3
*)

//@Trees/AVL
//let rotate_right (#a: Type) (r: tree a) : option (tree a) =
//  match r with
//  | Node x (Node z t1 t2 _) t3 _ ->
//      Some (Node z t1 (Node x t2 t3 0) 0)
//  | _ -> None
let rotate_right_wds (#a: Type) (r: wds a) : option (wds a) =
  match r with
  | Node x (Node z t1 t2 _) t3 s ->
      let s23 = sot_wds t2 + sot_wds t3 + 1 in
      let t23 = Node x t2 t3 s23 in
      //induction_wds x t2 t3;
      assert (is_wds t23);
      let s123 = sot_wds t1 + s23 + 1 in
      assert (s123 == s);
      Some (Node z t1 t23 s)
  | _ -> None

(*
    x               y
t1     z    =>   x     z
     y   t4    t1 t2 t3 t4
   t2 t3
*)

//@Trees/AVL
//let rotate_right_left (#a: Type) (r: tree a) : option (tree a) =
//  match r with
//  | Node x t1 (Node z (Node y t2 t3 _) t4 _) _ ->
//      Some (Node y (Node x t1 t2 0) (Node z t3 t4 0) 0)
//  | _ -> None
let rotate_right_left_wds (#a: Type) (r: wds a) : option (wds a) =
  match r with
  | Node x t1 (Node z (Node y t2 t3 _) t4 _) s ->
      let s12 = sot_wds t1 + sot_wds t2 + 1 in
      let t12 = Node x t1 t2 s12 in
      //induction_wds x t1 t2;
      assert (is_wds t12);
      let s34 = sot_wds t3 + sot_wds t4 + 1 in
      let t34 = Node z t3 t4 s34 in
      //induction_wds z t3 t4;
      assert (is_wds t34);
      let s1234 = s12 + s34 + 1 in
      assert (s1234 == s);
      Some (Node y t12 t34 s)
  | _ -> None

(*
      x             y
   z     t4 =>   z     x
t1   y         t1 t2 t3 t4
   t2 t3
*)

//@Trees/AVL
//let rotate_left_right (#a: Type) (r: tree a) : option (tree a) =
//  match r with
//  | Node x (Node z t1 (Node y t2 t3 _) _) t4 _  -> Some (Node y (Node z t1 t2 0) (Node x t3 t4 0) 0)
//  | _ -> None
let rotate_left_right_wds (#a: Type) (r: wds a) : option (wds a) =
  match r with
  | Node x (Node z t1 (Node y t2 t3 _) _) t4 s ->
      let s12 = sot_wds t1 + sot_wds t2 + 1 in
      let t12 = Node z t1 t2 s12 in
      //induction_wds z t1 t2;
      assert (is_wds t12);
      let s34 = sot_wds t3 + sot_wds t4 + 1 in
      let t34 = Node x t3 t4 s34 in
      //induction_wds x t3 t4;
      assert (is_wds t34);
      let s1234 = s12 + s34 + 1 in
      assert (s1234 == s);
      Some (Node y t12 t34 s)
  | _ -> None

//@Trees/AVL
let rotate_left_size (#a: Type) (r: wds a)
  : Lemma
  (requires Some? (rotate_left_wds r))
  (ensures size_of_tree (get (rotate_left_wds r)) == size_of_tree r)
  = ()
let rotate_right_size (#a: Type) (r: wds a)
  : Lemma
  (requires Some? (rotate_right_wds r))
  (ensures size_of_tree (get (rotate_right_wds r)) == size_of_tree r)
  = ()
let rotate_right_left_size (#a: Type) (r: wds a)
  : Lemma
  (requires Some? (rotate_right_left_wds r))
  (ensures
  size_of_tree (get (rotate_right_left_wds r)) == size_of_tree r)
  = ()
let rotate_left_right_size (#a: Type) (r: wds a)
  : Lemma
  (requires Some? (rotate_left_right_wds r))
  (ensures
  size_of_tree (get (rotate_left_right_wds r)) == size_of_tree r)
  = ()

//@BST
let rec forall_keys_trans (#a: Type) (t: tree a) (cond1 cond2: a -> bool)
  : Lemma
  (requires (forall x. cond1 x ==> cond2 x) /\ forall_keys t cond1)
  (ensures forall_keys t cond2)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
    forall_keys_trans left cond1 cond2; forall_keys_trans right cond1 cond2

//@BST
let rotate_left_bst (#a:Type) (cmp:cmp a) (r:wds a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_left_wds r))
  (ensures is_bst cmp (Some?.v (rotate_left_wds r)))
  = match r with
  | Node x t1 (Node z t2 t3 s23) _ ->
      assert (is_bst cmp (Node z t2 t3 s23));
      let s12 = sot_wds t1 + sot_wds t2 + 1 in
      assert (is_bst cmp (Node x t1 t2 s12));
      forall_keys_trans t1 (key_left cmp x) (key_left cmp z)
let rotate_right_bst (#a:Type) (cmp:cmp a) (r:wds a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_right_wds r))
  (ensures is_bst cmp (Some?.v (rotate_right_wds r)))
  = match r with
  | Node x (Node z t1 t2 s12) t3 _ ->
      assert (is_bst cmp (Node z t1 t2 s12));
      let s23 = sot_wds t2 + sot_wds t3 + 1 in
      assert (is_bst cmp (Node x t2 t3 s23));
      forall_keys_trans t3 (key_right cmp x) (key_right cmp z)

//@BST
let rotate_right_left_bst (#a:Type) (cmp:cmp a) (r:wds a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_right_left_wds r))
  (ensures is_bst cmp (Some?.v (rotate_right_left_wds r)))
  = match r with
  | Node x t1 (Node z (Node y t2 t3 s23) t4 s234) _ ->
    // Node y (Node x t1 t2) (Node z t3 t4)
    assert (is_bst cmp (Node z (Node y t2 t3 s23) t4 s234));
    assert (is_bst cmp (Node y t2 t3 s23));
    let s12 = sot_wds t1 + sot_wds t2 + 1 in
    let s34 = sot_wds t3 + sot_wds t4 + 1 in
    let left = Node x t1 t2 s12 in
    let right = Node z t3 t4 s34 in

    assert (forall_keys (Node y t2 t3 s23) (key_right cmp x));
    assert (forall_keys t2 (key_right cmp x));
    assert (is_bst cmp left);

    assert (is_bst cmp right);

    forall_keys_trans t1 (key_left cmp x) (key_left cmp y);
    assert (forall_keys left (key_left cmp y));

    forall_keys_trans t4 (key_right cmp z) (key_right cmp y);
    assert (forall_keys right (key_right cmp y))

//@BST
let rotate_left_right_bst (#a:Type) (cmp:cmp a) (r:wds a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_left_right_wds r))
  (ensures is_bst cmp (Some?.v (rotate_left_right_wds r)))
  = match r with
  | Node x (Node z t1 (Node y t2 t3 s23) s123) t4 _ ->
    // Node y (Node z t1 t2) (Node x t3 t4)
    assert (is_bst cmp (Node z t1 (Node y t2 t3 s23) s123));
    assert (is_bst cmp (Node y t2 t3 s23));
    let s12 = sot_wds t1 + sot_wds t2 + 1 in
    let s34 = sot_wds t3 + sot_wds t4 + 1 in
    let left = Node z t1 t2 s12 in
    let right = Node x t3 t4 s34 in

    assert (is_bst cmp left);

    assert (forall_keys (Node y t2 t3 s23) (key_left cmp x));
    assert (forall_keys t2 (key_left cmp x));
    assert (is_bst cmp right);

    forall_keys_trans t1 (key_left cmp z) (key_left cmp y);
    assert (forall_keys left (key_left cmp y));

    forall_keys_trans t4 (key_right cmp x) (key_right cmp y);
    assert (forall_keys right (key_right cmp y))

//TODO: refactor, change for wds trees
//@BST
(** Same bounds before and after rotate **)
//let rotate_left_key_left (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_left r))
//  (ensures  forall_keys (Some?.v (rotate_left r)) (key_left cmp root))
//  = match r with
//  | Node x t1 (Node z t2 t3 s23) _ ->
//      let s12 = sot_wds t1 + sot_wds t2 + 1 in
//      assert (forall_keys (Node z t2 t3 s23) (key_left cmp root));
//      assert (forall_keys (Node x t1 t2 s12) (key_left cmp root))
//
//let rotate_left_key_right (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_left r))
//  (ensures  forall_keys (Some?.v (rotate_left r)) (key_right cmp root))
//  = match r with
//  | Node x t1 (Node z t2 t3 s23) _ ->
//      let s12 = sot_wds t1 + sot_wds t2 + 1 in
//      assert (forall_keys (Node z t2 t3 s23) (key_right cmp root));
//      assert (forall_keys (Node x t1 t2 s12) (key_right cmp root))
//
//let rotate_right_key_left (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_right r))
//  (ensures  forall_keys (Some?.v (rotate_right r)) (key_left cmp root))
//  = match r with
//  | Node x (Node z t1 t2 s12) t3 _ ->
//      let s23 = sot_wds t2 + sot_wds t3 + 1 in
//      assert (forall_keys (Node z t1 t2 s12) (key_left cmp root));
//      assert (forall_keys (Node x t2 t3 s23) (key_left cmp root))
//
//let rotate_right_key_right (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_right r))
//  (ensures  forall_keys (Some?.v (rotate_right r)) (key_right cmp root))
//  = match r with
//  | Node x (Node z t1 t2 s12) t3 _ ->
//      let s23 = sot_wds t2 + sot_wds t3 + 1 in
//      assert (forall_keys (Node z t1 t2 s12) (key_right cmp root));
//      assert (forall_keys (Node x t2 t3 s23) (key_right cmp root))
//
//let rotate_right_left_key_left (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_right_left r))
//  (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_left cmp root))
//  = match r with
//  | Node x t1 (Node z (Node y t2 t3 s23) t4 s234) _ ->
//    assert (forall_keys (Node z (Node y t2 t3 s23) t4 s234) (key_left cmp root));
//    assert (forall_keys (Node y t2 t3 s23) (key_left cmp root));
//    let s12 = sot_wds t1 + sot_wds t2 + 1 in
//    let s34 = sot_wds t3 + sot_wds t4 + 1 in
//    let left = Node x t1 t2 s12 in
//    let right = Node z t3 t4 s34 in
//    assert (forall_keys left (key_left cmp root));
//    assert (forall_keys right (key_left cmp root))
//
//let rotate_right_left_key_right (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_right_left r))
//  (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_right cmp root))
//  = match r with
//  | Node x t1 (Node z (Node y t2 t3 s23) t4 s234) _ ->
//    assert (forall_keys (Node z (Node y t2 t3 s23) t4 s234) (key_right cmp root));
//    assert (forall_keys (Node y t2 t3 s23) (key_right cmp root));
//    let s12 = sot_wds t1 + sot_wds t2 + 1 in
//    let s34 = sot_wds t3 + sot_wds t4 + 1 in
//    let left = Node x t1 t2 s12 in
//    let right = Node z t3 t4 s34 in
//    assert (forall_keys left (key_right cmp root));
//    assert (forall_keys right (key_right cmp root))
//
//let rotate_left_right_key_left (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_left_right r))
//  (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_left cmp root))
//  = match r with
//  | Node x (Node z t1 (Node y t2 t3 s23) s123) t4 _ ->
//    assert (forall_keys (Node z t1 (Node y t2 t3 s23) s123) (key_left cmp root));
//    assert (forall_keys (Node y t2 t3 s23) (key_left cmp root));
//    let s12 = sot_wds t1 + sot_wds t2 + 1 in
//    let s34 = sot_wds t3 + sot_wds t4 + 1 in
//    let left = Node x t1 t2 s12 in
//    let right = Node z t3 t4 s34 in
//    assert (forall_keys left (key_left cmp root));
//    assert (forall_keys right (key_left cmp root))
//
//let rotate_left_right_key_right (#a:Type) (cmp:cmp a) (r:wds a) (root:a)
//  : Lemma
//  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_left_right r))
//  (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_right cmp root))
//  = match r with
//  | Node x (Node z t1 (Node y t2 t3 s23) s123) t4 _ ->
//    assert (forall_keys (Node z t1 (Node y t2 t3 s23) s123) (key_right cmp root));
//    assert (forall_keys (Node y t2 t3 s23) (key_right cmp root));
//    let s12 = sot_wds t1 + sot_wds t2 + 1 in
//    let s34 = sot_wds t3 + sot_wds t4 + 1 in
//    let left = Node x t1 t2 s12 in
//    let right = Node z t3 t4 s34 in
//    assert (forall_keys left (key_right cmp root));
//    assert (forall_keys right (key_right cmp root))


(** Balancing operation for AVLs *)

//@D
//let rebalance_avl (#a: Type) (x: tree a) : tree a =
//    match x with
//    | Leaf -> x
//    | Node data left right _ ->
//      if is_balanced x then x
//      else (
//        if height left - height right > 1 then (
//          let Node ldata lleft lright _ = left in
//          if height lright > height lleft then (
//            match rotate_left_right x with
//            | Some y -> y
//            | _ -> x
//          ) else (
//            match rotate_right x with
//            | Some y -> y
//            | _ -> x
//          )
//
//        ) else if height left - height right < -1 then (
//          let Node rdata rleft rright _ = right in
//            if height rleft > height rright then (
//              match rotate_right_left x with
//              | Some y -> y
//              | _ -> x
//            ) else (
//              match rotate_left x with
//              | Some y -> y
//              | _ -> x
//            )
//        ) else (
//          x
//        )
//      )


(*
some changes with respect to previous version, as
this function is intended to be only used after
adding an element to a previously balanced tree:
no need to go through this entire tree
TODO : height as metadata to be retrieved in O(1)
TODO : specify rotate_* as inline functions in C (benchmark the difference !)
TODO : optimize rotate_*, remove matching and add precondition
TODO : option.get
*)

let rebalance_avl_wds (#a: Type) (t: wds a) : wds a =
  if Leaf? t then t else
  let Node data left right size = t in
  if height left - height right > 1 then (
    let Node ldata lleft lright lsize = left in
    if height lleft >= height lright then (
      let r = rotate_right_wds t in
      assert (Some? r);
      get r
    ) else (
      let r = rotate_left_right_wds t in
      assert (Some? r);
      get r
    )
  ) else if height right - height left > 1 then (
    let Node rdata rleft rright rsize = right in
    if height rleft > height rright then (
      let r = rotate_right_left_wds t in
      assert (Some? r);
      get r
    ) else (
      let r = rotate_left_wds t in
      assert (Some? r);
      get r
    )
  ) else (
    t
  )

let rebalance_avl_wds_size (#a: Type) (t: wds a)
  : Lemma (size_of_tree (rebalance_avl_wds t) == size_of_tree t)
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let rebalance_avl_wds_proof (#a: Type) (cmp: cmp a) (t: wds a)
  (root: a)
  : Lemma
  (requires is_bst cmp t /\ (
    match t with
    | Leaf -> True
    | Node data left right _ ->
        is_balanced left /\
        is_balanced right /\
        height left - height right <= 2 /\
        height right - height left <= 2
  ))
  (ensures
    is_avl cmp (rebalance_avl_wds t)
    /\
    (forall_keys t (key_left cmp root)
      ==> forall_keys (rebalance_avl_wds t) (key_left cmp root)) /\
    (forall_keys t (key_right cmp root)
      ==> forall_keys (rebalance_avl_wds t) (key_right cmp root))
  )
  =
  admit ();
  if Leaf? t then () else
  let Node _ left right _ = t in
  if height left - height right > 1 then (
    assert (height left - height right == 2);
    let Node _ lleft lright _ = left in
    if height lleft >= height lright then (
      let r = rotate_right_wds t in
      assert (Some? r);
      let t' = get r in
      rotate_right_bst cmp t;
      //Classical.move_requires (rotate_right_key_left cmp t) root;
      //Classical.move_requires (rotate_right_key_right cmp t) root;
      assert (is_avl cmp t')
    ) else (
      let r = rotate_left_right_wds t in
      assert (Some? r);
      let t' = get r in
      rotate_left_right_bst cmp t;
      //Classical.move_requires (rotate_left_right_key_left cmp t) root;
      //Classical.move_requires (rotate_left_right_key_right cmp t) root;
      assert (is_avl cmp t')
    )
  ) else if height right - height left > 1 then (
    assert (height right - height left == 2);
    let Node _ rleft rright _ = right in
    assert (is_balanced right);
    if height rright >= height rleft then (
      let r = rotate_left_wds t in
      assert (Some? r);
      let t' = get r in
      rotate_left_bst cmp t;
      //Classical.move_requires (rotate_left_key_left cmp t) root;
      //Classical.move_requires (rotate_left_key_right cmp t) root;
      assert (is_avl cmp t')
    ) else (
      let r = rotate_right_left_wds t in
      assert (Some? r);
      let t' = get r in
      rotate_right_left_bst cmp t;
      //Classical.move_requires (rotate_right_left_key_left cmp t) root;
      //Classical.move_requires (rotate_right_left_key_right cmp t) root;
      assert (is_avl cmp t')
    )
)
#pop-options

(** Insertion **)

//@D
//let rec insert_avl (#a: Type) (cmp:cmp a) (x: avl a cmp) (key: a)
//  : t:wds a{size_of_tree t == size_of_tree x + 1}
//  =
//  match x with
//  | Leaf -> Node key Leaf Leaf 1
//  | Node data left right size ->
//    let delta = cmp data key in
//    if delta >= 0 then (
//      let new_left = insert_avl cmp left key in
//      let tmp = Node data new_left right (size + 1) in
//      //aux_size_left_subtree left new_left;
//      assert (is_wds x);
//      //induction_wds data new_left right;
//      let t = rebalance_avl_wds tmp in
//      rebalance_avl_wds_size tmp;
//      t
//    ) else (
//      let new_right = insert_avl cmp right key in
//      let tmp = Node data left new_right (size + 1) in
//      //aux_size_right_subtree right new_right;
//      assert (is_wds x);
//      //induction_wds data left new_right;
//      let t = rebalance_avl_wds tmp in
//      rebalance_avl_wds_size tmp;
//      t
//    )

//@BST
let rec mem (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a) : bool =
  match t with
  | Leaf -> false
  | Node data left right _ ->
      let delta = cmp x data in
      (delta = 0) || (mem cmp left x) || (mem cmp right x)

//@BST
type cond (a: Type) (cmp:cmp a) = c: (a -> bool){
  squash (forall x y. cmp x y = 0 ==> (c x = c y))
}

//@D, change key_{left, right} types
//let key_left2 (#a: Type) (cmp:cmp a) (root: a) : cond a cmp
//  = key_left cmp root
//let key_right2 (#a: Type) (cmp:cmp a) (root: a) : cond a cmp
//  = key_right cmp root

//TODO: minify
let rec equiv_aux (#a: Type)
  (cmp:cmp a) (t: bst a cmp) (cond:cond a cmp) (x: a)
  : Lemma
  (requires forall_keys t cond /\ mem cmp t x)
  (ensures cond x)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
      let delta = cmp x data in
      assert (mem cmp t x);
      if delta = 0 then ()
      else begin
        if mem cmp left x then begin
          equiv_aux cmp left cond x
        end else begin
          equiv_aux cmp right cond x
        end
      end

let equiv_aux2 (#a: Type)
  (cmp:cmp a) (cond:cond a cmp) (t: bst a cmp{forall_keys t cond})
  (x: a)
  : Lemma (mem cmp t x ==> cond x)
  = if mem cmp t x then equiv_aux cmp t cond x

let equiv_aux3 (#a: Type)
  (cmp: cmp a) (cond:cond a cmp) (t: bst a cmp{forall_keys t cond})
  : squash (forall x. mem cmp t x ==> cond x)
  = introduce forall x. mem cmp t x ==> cond x
    // TODO: shoud be doable with equiv_aux
    with equiv_aux2 cmp cond t x

let equiv_aux4 (#a: Type)
  (cmp:cmp a) (t: bst a cmp)
  (cond: cond a cmp)
  : Lemma (
  forall_keys t cond
  ==>
  (forall x. mem cmp t x ==> cond x))
  =
  if forall_keys t cond then equiv_aux3 cmp cond t

let rec equiv_aux5 (#a: Type)
  (cmp:cmp a) (t: bst a cmp)
  (cond: cond a cmp)
  : Lemma
  (requires (forall x. mem cmp t x ==> cond x))
  (ensures forall_keys t cond)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
      assert (mem cmp t data);
      assert (cond data);
      equiv_aux5 cmp left cond;
      equiv_aux5 cmp right cond

let equiv_aux6 (#a: Type)
  (cmp:cmp a) (t: bst a cmp)
  (cond: cond a cmp)
  : Lemma
  ((forall x. mem cmp t x ==> cond x)
  ==>
  forall_keys t cond)
  =
  introduce (forall x. mem cmp t x ==> cond x) ==> forall_keys t cond
  with _. equiv_aux5 cmp t cond


let equiv (#a: Type)
  (cmp:cmp a) (t: bst a cmp)
  (cond: cond a cmp)
  : Lemma (
  forall_keys t cond
  <==>
  (forall x. mem cmp t x ==> cond x))
  =
  equiv_aux4 cmp t cond;
  equiv_aux6 cmp t cond

let rec memopt (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a) : bool =
  match t with
  | Leaf -> false
  | Node data left right _ ->
      let delta = cmp x data in
      if delta = 0 then begin
        true
      end else if delta < 0 then begin
        memopt cmp left x
      end else begin
        memopt cmp right x
      end

let unicity_left (#a: Type) (cmp: cmp a) (t: bst a cmp{Node? t})
  (x: a{mem cmp t x})
  : Lemma (
    let delta = cmp x (cdata t) in
    delta < 0 <==> mem cmp (cleft t) x
  )
  = match t with
  | Node data left right _ ->
      let delta = cmp x data in
      if delta < 0 then begin
        if mem cmp right x then begin
          assert (forall_keys right (key_right cmp data));
          equiv cmp right (key_right cmp data);
          assert (key_right cmp data x);
          assert (not (mem cmp right x))
        end;
        assert (mem cmp left x)
      end;
      assert (delta < 0 ==> mem cmp (cleft t) x);

      if mem cmp left x then begin
        assert (forall_keys left (key_left cmp data));
        equiv cmp left (key_left cmp data);
        assert (key_left cmp data x);
        assert (delta < 0)
      end;
      assert (mem cmp (cleft t) x ==> delta < 0)

let unicity_right (#a: Type) (cmp: cmp a) (t: bst a cmp{Node? t})
  (x: a{mem cmp t x})
  : Lemma (
    let delta = cmp x (cdata t) in
    delta > 0 <==> mem cmp (cright t) x
  )
  = match t with
  | Node data left right _ ->
      let delta = cmp x data in

      if delta > 0 then begin
        if mem cmp left x then begin
          assert (forall_keys left (key_left cmp data));
          equiv cmp left (key_left cmp data);
          assert (key_left cmp data x);
          assert (not (mem cmp left x))
        end;
        assert (mem cmp right x)
      end;
      assert (delta > 0 ==> mem cmp (cright t) x);

      if mem cmp right x then begin
        assert (forall_keys right (key_right cmp data));
        equiv cmp right (key_right cmp data);
        assert (key_right cmp data x);
        assert (delta > 0)
      end;
      assert (mem cmp (cright t) x ==> delta > 0)

let rec equivmem1 (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a)
  : Lemma
  (memopt cmp t x ==> mem cmp t x)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
      equivmem1 cmp left x;
      equivmem1 cmp right x

let rec equivmem2 (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a)
  : Lemma
  (requires mem cmp t x)
  (ensures memopt cmp t x)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
      let delta = cmp x data in
      if mem cmp left x then begin
        unicity_left cmp t x;
        assert (delta < 0);
        equivmem2 cmp left x
      end;
      if mem cmp right x then begin
        unicity_right cmp t x;
        assert (delta > 0);
        equivmem2 cmp right x
      end

let equivmem (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a)
  : Lemma
  (mem cmp t x <==> memopt cmp t x)
  =
  if mem cmp t x then equivmem2 cmp t x;
  equivmem1 cmp t x

// x \in t1 => x \in t2 <=> t1 \subset t2
let subset (#a: Type) (cmp:cmp a) (t1 t2: bst a cmp)
  = forall x. mem cmp t1 x ==> mem cmp t2 x

// x \in t2 => x \in t1 or x = v
let add (#a: Type) (cmp:cmp a) (t1 t2: bst a cmp) (v: a)
  //= forall x. (mem cmp t1 x \/ cmp v x = 0) ==> mem cmp t2 x
  = forall x. (mem cmp t1 x \/ cmp v x = 0) <==> mem cmp t2 x

let add_is_subset (#a: Type) (cmp:cmp a) (t1 t2: bst a cmp) (v: a)
  : Lemma (
    add cmp t1 t2 v ==> subset cmp t1 t2
  )
  = ()

let equal (#a: Type) (cmp:cmp a) (t1 t2: bst a cmp)
  = forall x. mem cmp t1 x = mem cmp t2 x

let double_inclusion (#a: Type) (cmp:cmp a) (t1 t2: bst a cmp)
  : Lemma (equal cmp t1 t2
  <==> subset cmp t1 t2 /\ subset cmp t2 t1)
  = ()

let subset_preserves_cond (#a: Type0)
  (cmp:cmp a)
  (t1 t2: bst a cmp) (cond: cond a cmp)
  : Lemma
  (requires
    subset cmp t1 t2 /\
    forall_keys t2 cond
  )
  (ensures
    forall_keys t1 cond
  )
  =
  equiv cmp t2 cond;
  assert (forall x. mem cmp t2 x ==> cond x);
  assert (forall x. mem cmp t1 x ==> cond x);
  equiv cmp t1 cond

let add_preserves_cond (#a: Type0)
  (cmp:cmp a)
  (t1 t2: bst a cmp) (v: a) (cond: cond a cmp)
  : Lemma
  (requires
    add cmp t1 t2 v /\
    forall_keys t1 cond /\
    cond v
  )
  (ensures
    forall_keys t2 cond
  )
  = equiv cmp t1 cond;
    equiv cmp t2 cond

let equal_preserves_cond (#a: Type)
  (cmp:cmp a)
  (t1 t2: bst a cmp) (cond: cond a cmp)
  : Lemma
  (requires forall_keys t1 cond /\ equal cmp t1 t2)
  (ensures forall_keys t2 cond)
  = equiv cmp t1 cond;
    equiv cmp t2 cond

let smaller_not_mem (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a)
  : Lemma
  (requires forall_keys t (key_right cmp x))
  (ensures mem cmp t x = false)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
    // ad absurdum
    if mem cmp t x then begin
      assert (forall_keys t (key_right cmp x));
      equiv cmp t (key_right cmp x);
      assert (mem cmp t x);
      assert (key_right cmp x x);
      assert (cmp x x < 0)
    end;
    assert (mem cmp t x = false)

let greater_not_mem (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a)
  : Lemma
  (requires forall_keys t (key_left cmp x))
  (ensures mem cmp t x = false)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
    // ad absurdum
    if mem cmp t x then begin
      assert (forall_keys t (key_left cmp x));
      equiv cmp t (key_left cmp x);
      assert (mem cmp t x);
      assert (key_left cmp x x);
      assert (cmp x x < 0)
    end;
    assert (mem cmp t x = false)

//previous lemmas: @BST

//@AVL
let rebalance_equal (#a: Type) (cmp: cmp a) (t1: bst a cmp)
  : Lemma
  (requires is_avl cmp (rebalance_avl_wds t1))
  (ensures equal cmp t1 (rebalance_avl_wds t1))
  = admit ()




(*
- r: in case of equality with an already existing element,
  true = replace, false = do not replace
- snd (result): whether a new element has been added,
  that is whether the size has increased
  => bad idea/bad design?
*)

#push-options "--z3rlimit 100"
let rec insert_avl2_aux (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : result:(avl a cmp & bool){
    let t',b = result in
    size_of_tree t' = size_of_tree t + (int_of_bool b) /\
    height t <= height t' /\
    height t' <= height t + 1 /\
    (b ==> add cmp t t' new_data) /\
    (not b ==> equal cmp t t') /\
    (subset cmp t t')
  }
  =
  match t with
  | Leaf -> Node new_data Leaf Leaf 1, true
  | Node data left right size ->
    let delta = cmp new_data data in
    if delta = 0 then begin
      if r
      then
        let new_t = Node new_data left right size in
        forall_keys_trans left
          (key_left cmp data)
          (key_left cmp new_data);
        forall_keys_trans right
          (key_right cmp data)
          (key_right cmp new_data);
        new_t, false
      else
        t, false
    end
    else if delta < 0 then begin
      //assert (subset cmp (fst (insert_avl2_aux r cmp left new_data))
      //left);
      let new_left, b = insert_avl2_aux r cmp left new_data in
      let new_size = size + (int_of_bool b) in
      let new_t = Node data new_left right new_size in
      // is_bst new_t
      if b then begin
        assert (add cmp left new_left new_data);
        add_preserves_cond cmp left new_left new_data
          (key_left cmp data)
      end else begin
        assert (equal cmp new_left left);
        equal_preserves_cond cmp left new_left
          (key_left cmp data)
      end;
      assert (forall_keys new_left (key_left cmp data));
      assert (is_bst cmp new_t);


      assert (is_avl cmp new_left);
      assert (is_avl cmp right);
      assert (height t <= height new_t);
      assert (height new_t <= height t + 1);
      rebalance_avl_wds_proof cmp new_t data;
      assert (is_avl cmp (rebalance_avl_wds new_t));
      rebalance_avl_wds_size new_t;
      let new_t2 = rebalance_avl_wds new_t in
      rebalance_equal cmp new_t;
      //assert (subset cmp t new_t2);
      //assert (b ==> add cmp t new_t2 new_data);
      //assert (not b ==> equal cmp t new_t2);
      //assert (height t <= height new_t2);
      //assert (height new_t2 <= height t + 1);
      new_t2, b
    end else begin
      let new_right, b = insert_avl2_aux r cmp right new_data in
      let new_size = size + (int_of_bool b) in
      let new_t = Node data left new_right new_size in
       // is_bst new_t
      if b then begin
        assert (add cmp right new_right new_data);
        add_preserves_cond cmp right new_right new_data
          (key_right cmp data)
      end else begin
        assert (equal cmp new_right right);
        equal_preserves_cond cmp right new_right
          (key_right cmp data)
      end;
      assert (forall_keys new_right (key_right cmp data));
      assert (is_bst cmp new_t);

      assert (is_avl cmp new_right);
      assert (is_avl cmp left);
      assert (height t <= height new_t);
      assert (height new_t <= height t + 1);
      rebalance_avl_wds_proof cmp new_t data;
      assert (is_avl cmp (rebalance_avl_wds new_t));
      rebalance_avl_wds_size new_t;
      let new_t2 = rebalance_avl_wds new_t in
      rebalance_equal cmp new_t;
      //assert (subset cmp t new_t2);
      //assert (b ==> add cmp t new_t2 new_data);
      //assert (not b ==> equal cmp t new_t2);
      //assert (height t <= height new_t2);
      //assert (height new_t2 <= height t + 1);
      new_t2, b
    end
#pop-options

#push-options "--z3rlimit 50"
let rec remove_leftmost (#a: Type0)
  (cmp:cmp a)
  (t: avl a cmp{Node? t})
  : r:(avl a cmp & a){
    //1 returned element was part of the tree
    mem cmp t (snd r) = true /\
    //2 returned element smaller than all elements of the new tree
    forall_keys (fst r) (key_right cmp (snd r)) /\
    //3 returned element has been removed
    mem cmp (fst r) (snd r) = false /\
    //4 rest of the tree preserved
    //(forall x. cmp x (snd r) <> 0
    //  ==> mem cmp t x = mem cmp (fst r) x) /\
    //5 subset
    //subset cmp (fst r) t /\
    add cmp (fst r) t (snd r) /\
    //6 size decreased by 1
    size_of_tree (fst r) = size_of_tree t - 1 /\
    //7
    height t - 1 <= height (fst r) /\
    height (fst r) <= height t
    //Node? (fst r) ==> is_balanced (cleft (fst r)) /\
    //Node? (fst r) ==> is_balanced (cright (fst r)) /\
 }
  =
  match t with
  | Node data Leaf right size ->
      // (1 : trivial)
      // (2)
      assert (forall_keys right (key_right cmp data));
      // (3)
      equiv cmp right (key_right cmp data);
      assert (mem cmp right data = false);
      //assert (is_balanced t);
      //assert (height right - height #a Leaf <= 1);
      //assert (height right <= 1);
      // (4 5 6 : trivial)
      right, data
  | Node data left right size ->
      let new_left, leftmost = remove_leftmost cmp left in
      // (1 : IH)
      assert (mem cmp left leftmost = true);
      assert (mem cmp t leftmost = true);
      // (2 : IH)
      let new_t = Node data new_left right (size - 1) in
      // new_left <= data
      add_is_subset cmp new_left left leftmost;
      assert (subset cmp new_left left);
      subset_preserves_cond cmp new_left left (key_left cmp data);
      assert (forall_keys new_left (key_left cmp data));
      // data <= right
      assert (forall_keys right (key_right cmp data));
      assert (is_bst cmp new_t);
      // new_left < right
      forall_keys_trans right
        (key_right cmp data)
        (key_right cmp leftmost);
      // (3 : use 2)
      //smaller_not_mem cmp new_t leftmost;
      let new_t2 = rebalance_avl_wds new_t in
      assert (is_balanced new_left);
      assert (is_balanced right);
      assert (height left - 1 <= height new_left);
      assert (height new_left <= height left);
      assert (height right - height new_left <= 2);
      assert (height new_left - height right <= 1);
      rebalance_avl_wds_proof cmp new_t data;

      // 1
      assert (mem cmp t leftmost = true);
      // 2
      rebalance_equal cmp new_t;
      assert (subset cmp new_t2 new_t);
      subset_preserves_cond cmp
        new_t2 new_t (key_right cmp leftmost);
      // 3
      smaller_not_mem cmp new_t2 leftmost;
      assert (mem cmp new_t2 leftmost = false);
      // 5
      assert (add cmp new_t2 t leftmost);
      // 6
      rebalance_avl_wds_size new_t;
      assert (size_of_tree new_t2 = size_of_tree t - 1);
      // 7
      assert (height new_t2 <= height t);
      assert (height t - 1 <= height new_t2);
      assert (is_avl cmp new_t2);
      new_t2, leftmost
#pop-options

// https://en.wikipedia.org/wiki/Binary_search_tree#Deletion
#push-options "--z3rlimit 80"
let delete_bst_aux0 (#a: Type0)
  (cmp:cmp a) (data_to_rm: a)
  (t: avl a cmp{Node? t /\ cmp (cdata t) data_to_rm = 0})
  //(t: avl a cmp{Node? t /\ cmp (cdata t) data_to_rm = 0})
  : r:avl a cmp{
    // 1 a b removal of one element
    mem cmp t data_to_rm = true /\
    //?data_to_rm = true /\
    mem cmp r data_to_rm = false /\
    // 2 remaining tree unchanged
    //(forall x. cmp x data_to_rm <> 0
    //  ==> mem cmp t x = mem cmp r x) /\
    add cmp r t data_to_rm /\
    // 3 size decreased by one
    size_of_tree r = size_of_tree t - 1 /\
    // 4
    height t - 1 <= height r /\
    height r <= height t
  }
  =
  match t with
  | Node data Leaf Leaf 1 -> Leaf
  | Node data left Leaf size ->
      assert (forall_keys left (key_left cmp data));
      equiv cmp left (key_left cmp data);
      //greater_not_mem cmp left data;
      assert (mem cmp left data = false);
      left
  | Node data Leaf right size ->
      assert (forall_keys right (key_right cmp data));
      equiv cmp right (key_right cmp data);
      //smaller_not_mem cmp right data;
      assert (mem cmp right data = false);
      right
  // successor of z = y
  | Node z l (Node y Leaf x sy) sz ->
      let r = Node y Leaf x sy in
      // y <= x
      assert (forall_keys x (key_right cmp y));
      // l <= z <= y
      forall_keys_trans l
        (key_left cmp z)
        (key_left cmp y);
      assert (forall_keys l (key_left cmp y));
      let new_t = Node y l x (sz - 1) in
      // 3 is included
      assert (is_bst cmp new_t);
      //assert (size_of_tree new_t = size_of_tree t - 1);
      // 1a
      assert (mem cmp t data_to_rm = true);
      // 1b : removal l
      assert (cmp z data_to_rm = 0);
      forall_keys_trans l
        (key_left cmp z)
        (key_left cmp data_to_rm);
      assert (forall_keys l (key_left cmp data_to_rm));
      greater_not_mem cmp l data_to_rm;
      assert (mem cmp l data_to_rm = false);
      // 1b : removal x
      assert (cmp z data_to_rm = 0);
      forall_keys_trans r
        (key_right cmp z)
        (key_right cmp data_to_rm);
      assert (forall_keys r (key_right cmp data_to_rm));
      assert (subset cmp x r);
      subset_preserves_cond cmp x r (key_right cmp data_to_rm);
      smaller_not_mem cmp x data_to_rm;
      assert (mem cmp x data_to_rm = false);
      // 1b
      assert (mem cmp new_t data_to_rm = false);
      // 2
      assert (add cmp (cright new_t) (cright t) y);
      assert (add cmp new_t t data_to_rm);

      // ###
      assert (is_balanced l);
      assert (is_balanced r);
      assert (height l - height r <= 2);
      assert (height r - height l <= 2);
      let new_t2 = rebalance_avl_wds new_t in
      rebalance_avl_wds_proof cmp new_t y;
      assert (is_avl cmp new_t2);
      // 1
      assert (mem cmp t data_to_rm = true);
      rebalance_equal cmp new_t;
      assert (mem cmp new_t2 data_to_rm = false);
      // 2
      assert (add cmp new_t2 t data_to_rm);
      // 3
      rebalance_avl_wds_size new_t;
      assert (size_of_tree new_t2 = size_of_tree t - 1);
      new_t2

  // successor of z = to be retrieved
  | Node z l r sz ->
      assert (Node? r);
      // 1a
      assert (mem cmp t data_to_rm = true);
      // call to aux function, building new tree
      let new_right, succ_z = remove_leftmost cmp r in
      let new_t = Node succ_z l new_right (sz - 1) in
      // left: l <= z <= succ_z
      // z <= succ_z
      assert (forall_keys r (key_right cmp z));
      equiv cmp r (key_right cmp z);
      assert (key_right cmp z succ_z);
      // l <= succ_z
      forall_keys_trans l
        (key_left cmp z)
        (key_left cmp succ_z);
      // right: succ_z <= new_right
      assert (forall_keys new_right (key_right cmp succ_z));
      // 3 included
      assert (is_bst cmp new_t);
      // 1b: left
      assert (cmp z data_to_rm = 0);
      forall_keys_trans l
        (key_left cmp z)
        (key_left cmp data_to_rm);
      greater_not_mem cmp l data_to_rm;
      assert (mem cmp l data_to_rm = false);
      // 1b: right
      assert (cmp z data_to_rm = 0);
      assert (forall_keys new_right (key_right cmp succ_z));
      forall_keys_trans new_right
        (key_right cmp succ_z)
        (key_right cmp data_to_rm);
      smaller_not_mem cmp new_right data_to_rm;
      assert (mem cmp new_right data_to_rm = false);
      // 1b
      assert (key_right cmp z succ_z);
      assert (cmp data_to_rm succ_z <> 0);
      assert (mem cmp new_t data_to_rm
      = (cmp succ_z data_to_rm = 0)
      || (mem cmp l data_to_rm)
      || (mem cmp new_right data_to_rm));
      assert (mem cmp new_t data_to_rm = false);
      // 2
      assert (add cmp new_t t data_to_rm);

      // ###
      assert (is_balanced l);
      assert (is_balanced new_right);
      assert (height l - height new_right <= 2);
      assert (height new_right - height l <= 2);
      let new_t2 = rebalance_avl_wds new_t in
      rebalance_avl_wds_proof cmp new_t succ_z;
      assert (is_avl cmp new_t2);
      // 1
      assert (mem cmp t data_to_rm = true);
      rebalance_equal cmp new_t;
      assert (mem cmp new_t2 data_to_rm = false);
      // 2
      assert (add cmp new_t2 t data_to_rm);
      // 3
      rebalance_avl_wds_size new_t;
      assert (size_of_tree new_t2 = size_of_tree t - 1);

      new_t2
#pop-options

#push-options "--z3rlimit 50"
let rec delete_avl_aux (#a: Type0)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : result:(avl a cmp & bool){
    let t',b = result in
    size_of_tree t' = size_of_tree t - (int_of_bool b) /\
    subset cmp t' t /\
    height t - 1 <= height t' /\
    height t' <= height t /\
    (b ==> add cmp t' t data_to_rm) /\
    ((not b) ==> equal cmp t' t) /\
    mem cmp t' data_to_rm = false
  }
  =
  match t with
  | Leaf -> Leaf, false
  | Node data left right size ->
      let delta = cmp data_to_rm data in
      if delta < 0 then begin
        let new_left, b = delete_avl_aux cmp left data_to_rm in
        assert (is_avl cmp new_left);
        assert (forall_keys left (key_left cmp data));
        assert (subset cmp new_left left);
        subset_preserves_cond cmp new_left left (key_left cmp data);
        assert (forall_keys new_left (key_left cmp data));
        let new_size = size - (int_of_bool b) in
        let new_t = Node data new_left right new_size in

        rebalance_avl_wds_size new_t;
        rebalance_avl_wds_proof cmp new_t data;
        let new_t2 = rebalance_avl_wds new_t in
        rebalance_equal cmp new_t;

        assert (mem cmp new_left data_to_rm = false);
        forall_keys_trans right
          (key_right cmp data)
          (key_right cmp data_to_rm);
        smaller_not_mem cmp right data_to_rm;
        assert (mem cmp new_t data_to_rm = false);
        assert (mem cmp new_t2 data_to_rm = false);

        new_t2, b
      end
      else if delta > 0 then begin
        let new_right, b = delete_avl_aux cmp right data_to_rm in
        assert (is_avl cmp new_right);
        assert (forall_keys right (key_right cmp data));
        assert (subset cmp new_right right);
        subset_preserves_cond cmp new_right right (key_right cmp data);
        assert (forall_keys new_right (key_right cmp data));
        let new_size = size - (int_of_bool b) in
        let new_t = Node data left new_right new_size in
        rebalance_avl_wds_size new_t;
        rebalance_avl_wds_proof cmp new_t data;
        let new_t2 = rebalance_avl_wds new_t in
        rebalance_equal cmp new_t;

        assert (mem cmp new_right data_to_rm = false);
        forall_keys_trans left
          (key_left cmp data)
          (key_left cmp data_to_rm);
        greater_not_mem cmp left data_to_rm;
        assert (mem cmp new_t data_to_rm = false);
        assert (mem cmp new_t2 data_to_rm = false);

        new_t2, b
      end
      else
        let new_t = delete_bst_aux0 cmp data_to_rm t in
        new_t, true
#pop-options

let insert_avl2 (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : t':wds a{
    let _,b = insert_avl2_aux r cmp t new_data in
    size_of_tree t' = size_of_tree t + (int_of_bool b) /\
    is_wds t'
  }
  = fst (insert_avl2_aux r cmp t new_data)


let proj (x: int) : r:int{-1 <= r /\ r <= 1}
  = if x < 0 then -1
    else if x = 0 then 0
    else 1

let rec test_aux0 (#a: Type)
  (cmp:cmp a) (t: bst a cmp) (x y: a)
  : Lemma
  (requires mem cmp t x /\ cmp x y = 0)
  (ensures mem cmp t y)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
let delta = cmp x data in
begin match (proj delta) with
| 0 -> ()
| 1 -> unicity_right cmp t x; test_aux0 cmp right x y
| _ -> unicity_left cmp t x; test_aux0 cmp left x y
end

let test_aux (#a: Type)
  (cmp: cmp a) (t1 t2 t3: bst a cmp) (v x: a)
  : Lemma
  (requires
    (mem cmp t1 v = false) /\
    (mem cmp t3 v = false) /\
    (mem cmp t1 x \/ cmp v x = 0 <==> mem cmp t2 x) /\
    (mem cmp t3 x \/ cmp v x = 0 <==> mem cmp t2 x)
  )
  (ensures mem cmp t1 x = mem cmp t3 x)
  =
  if cmp x v <> 0 then ()
  else begin
    assert (cmp x v = 0);
    if mem cmp t1 x then test_aux0 cmp t1 x v;
    assert (mem cmp t1 x = false);
    if mem cmp t3 x then test_aux0 cmp t3 x v;
    assert (mem cmp t3 x = false);
    ()
  end

let test2_aux (#a: Type)
  (cmp: cmp a) (t1 t2 t3: bst a cmp) (v x: a)
  : Lemma
  (requires
    (mem cmp t1 v = true) /\
    (mem cmp t3 v = true) /\
    (mem cmp t1 x \/ cmp v x = 0 <==> mem cmp t2 x) /\
    (mem cmp t3 x \/ cmp v x = 0 <==> mem cmp t2 x)
  )
  (ensures mem cmp t1 x = mem cmp t3 x)
  =
  if cmp x v <> 0 then ()
  else begin
    assert (mem cmp t1 x ==> mem cmp t2 x);
    test_aux0 cmp t1 v x;
    assert (mem cmp t2 x ==> mem cmp t1 x);
    assert (mem cmp t3 x ==> mem cmp t2 x);
    test_aux0 cmp t3 v x;
    assert (mem cmp t2 x ==> mem cmp t3 x)
  end

let test3_aux (#a: Type)
  (cmp: cmp a) (t1 t2 t3: bst a cmp) (v x: a)
  : Lemma
  (requires
    (mem cmp t1 v = mem cmp t3 v = true) /\
    (mem cmp t1 x \/ cmp v x = 0 <==> mem cmp t2 x) /\
    (mem cmp t3 x \/ cmp v x = 0 <==> mem cmp t2 x)
  )
  (ensures mem cmp t1 x = mem cmp t3 x)
  =
  if mem cmp t1 v
  then test2_aux cmp t1 t2 t3 v x
  else test_aux cmp t1 t2 t3 v x

let test (#a: Type)
  (cmp: cmp a) (t1 t2 t3: bst a cmp) (v: a)
  : Lemma
  (requires
  mem cmp t1 v = mem cmp t3 v /\
  // t2 = add t1 v
  add cmp t1 t2 v /\
  // t2 = add t3 v
  add cmp t3 t2 v
  )
  (ensures equal cmp t1 t3)
  =
  introduce forall x. (mem cmp t1 x = mem cmp t3 x)
  with test3_aux cmp t1 t2 t3 v x

let rec lemma_insert (#a: Type)
  (r: bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Lemma
  (requires mem cmp t new_data = false)
  (ensures snd (insert_avl2_aux r cmp t new_data) = true)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
      let delta = cmp new_data data in
      if delta = 0 then begin
        test_aux0 cmp t data new_data;
        assert (mem cmp t new_data)
      end else if delta < 0 then
        lemma_insert r cmp left new_data
      else
        lemma_insert  r cmp right new_data

let rec lemma_delete (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : Lemma
  (requires mem cmp t data_to_rm = true)
  (ensures snd (delete_avl_aux cmp t data_to_rm) = true)
  = match t with
  | Leaf -> ()
  | Node data left right _ ->
      let delta = cmp data_to_rm data in
      if delta < 0 then begin
        unicity_left cmp t data_to_rm;
        lemma_delete cmp left data_to_rm
      end else if delta > 0 then begin
        unicity_right cmp t data_to_rm;
        lemma_delete cmp right data_to_rm
      end else ()

let functional_correctness (#a: Type)
  (r: bool) (cmp: cmp a) (t: avl a cmp) (v: a)
  : Lemma
  (requires mem cmp t v = false)
  (ensures (
    let new_t, b = insert_avl2_aux r cmp t v in
    let new_t2, b = delete_avl_aux cmp new_t v in
    equal cmp t new_t2
  ))
  =
  let new_t, b1 = insert_avl2_aux r cmp t v in
  assert (mem cmp t v = false);
  lemma_insert r cmp t v;
  assert (b1 = true);
  assert (add cmp t new_t v);
  let new_t2, b2 = delete_avl_aux cmp new_t v in
  assert (mem cmp new_t v = true);
  lemma_delete cmp new_t v;
  assert (b2 = true);
  assert (mem cmp new_t2 v = false);
  assert (mem cmp t v = mem cmp new_t2 v);
  assert (add cmp new_t2 new_t v);
  test cmp t new_t new_t2 v;
  assert (equal cmp t new_t2);
  ()
