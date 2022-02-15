module Spec.Trees

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

//@Trees
let rec size_of_tree (#a: Type) (x: tree a) : Tot nat (decreases x) =
  match x with
  | Leaf -> 0
  | Node _ left right _ -> size_of_tree left + size_of_tree right + 1

//@Trees.Misc
let proj (x: int) : r:int{-1 <= r /\ r <= 1}
  = if x < 0 then -1
    else if x = 0 then 0
    else 1

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

//@Trees.Misc
let int_of_bool b : nat = match b with
  | true -> 1
  | false -> 0

//@Trees.Misc
let get (#a: Type) (v: option a{Some? v}) : a =
  let Some v' = v in v'

//@Trees
let sot_wds (#a: Type) (t: wds a)
  : s:nat{size_of_tree t == s} =
  match t with
  | Leaf -> 0
  | Node _ _ _ s -> s


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

