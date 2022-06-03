module Spec.Trees

module M = FStar.Math.Lib

(*** Type definitions *)

(**** The tree structure *)

type tree (a: Type) =
  | Leaf : tree a
  | Node:
    data: a ->
    left: tree a -> right: tree a ->
    size: nat -> height: nat -> tree a

let cdata (#a: Type) (t: tree a{Node? t}) =
  let Node d _ _ _ _ = t in d
let cleft (#a: Type) (t: tree a{Node? t}) =
  let Node _ l _ _ _ = t in l
let cright (#a: Type) (t: tree a{Node? t}) =
  let Node _ _ r _ _ = t in r
let csize (#a: Type) (t: tree a{Node? t}) =
  let Node _ _ _ s _ = t in s
let cheight (#a: Type) (t: tree a{Node? t}) =
  let Node _ _ _ _ h = t in h

//@Trees.Misc
noextract
let proj (x: int) : r:int{-1 <= r /\ r <= 1}
  = if x < 0 then -1
    else if x = 0 then 0
    else 1

(**** Binary search trees *)

//@Trees
let rec size_of_tree (#a: Type) (x: tree a) : nat
  = match x with
  | Leaf -> 0
  | Node _ left right _ _ ->
      size_of_tree left + size_of_tree right + 1

//@Trees
(* is with defined size *)
let rec is_wds (#a: Type) (x: tree a)
  : GTot bool
  = match x with
  | Leaf -> true
  | Node data left right size _ ->
      let s1 = size_of_tree left in
      let s2 = size_of_tree right in
      let b1 = is_wds left in
      let b2 = is_wds right in
      let s = s1 + s2 + 1 in
      assert (s = size_of_tree x);
      b1 && b2 && size = s

//@Trees
let wds (a: Type) = x:tree a {is_wds x}

(**** Height *)

//@Trees
let rec height_of_tree_old (#a: Type) (x: tree a) : nat =
  match x with
  | Leaf -> 0
  | Node _ left right _ _ ->
      let hleft = height_of_tree_old left in
      let hright = height_of_tree_old right in
      if hleft > hright then hleft + 1
      else hright + 1

let rec height_of_tree (#a: Type) (x:tree a) : nat =
  match x with
  | Leaf -> 0
  | Node _ left right _ _ ->
      (M.max (height_of_tree left) (height_of_tree right)) + 1

let rec height_equal (#a: Type) (x:tree a)
  : Lemma
  (height_of_tree_old x = height_of_tree x)
  = match x with
  | Leaf -> ()
  | Node _ left right _ _ ->
      let hleft = height_of_tree left in
      height_equal left;
      assert (hleft = height_of_tree_old left);
      let hright = height_of_tree right in
      height_equal right;
      assert (hright = height_of_tree_old right);
      let m = M.max (hleft + 1) (hright + 1) in
      assert (m = height_of_tree_old x)

(* is with defined height *)
let rec is_wdh (#a: Type) (x: tree a)
  : GTot bool
  = match x with
  | Leaf -> true
  | Node data left right _ height ->
      let h1 = height_of_tree left in
      let h2 = height_of_tree right in
      let b1 = is_wdh left in
      let b2 = is_wdh right in
      let h = (M.max h1 h2) + 1 in
      assert (h = height_of_tree x);
      b1 && b2 && height = h

let wdh (a: Type) = x:tree a {is_wdh x}

//@Trees.Misc
let rec height_lte_size (#a: Type) (t: tree a)
  : Lemma
  (height_of_tree t <= size_of_tree t)
  =
  match t with
  | Leaf -> ()
  | Node data left right _ _ ->
      height_lte_size left;
      height_lte_size right

//@Trees.Misc
noextract
let int_of_bool b : nat = match b with
  | true -> 1
  | false -> 0

//@Trees
let sot_wds (#a: Type) (t: wds a)
  : s:nat{size_of_tree t = s} =
  match t with
  | Leaf -> 0
  | Node _ _ _ s _ -> s

let hot_wdh (#a: Type) (t: wdh a)
  : h:nat{height_of_tree t = h} =
  match t with
  | Leaf -> 0
  | Node _ _ _ _ h -> h

(* is with defined metadata *)
let is_wdm (#a: Type) (t: tree a) : GTot bool
  = is_wds t && is_wdh t
let wdm (a: Type) = x:tree a {is_wdm x}

let merge_tree (#a: Type) (v: a) (l r: wdm a) : wdm a
  =
  let s1 = sot_wds l in
  let s2 = sot_wds r in
  let s = s1 + s2 + 1 in
  let h1 = hot_wdh l in
  let h2 = hot_wdh r in
  let h = (M.max h1 h2) + 1 in
  let t = Node v l r s h in
  t

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
let rotate_left_wdm (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x t1 (Node z t2 t3 _ _) s _ ->
      let s12 = sot_wds t1 + sot_wds t2 + 1 in
      let h1 = hot_wdh t1 in
      let h2 = hot_wdh t2 in
      let h3 = hot_wdh t3 in
      let h12 = (M.max h1 h2) + 1 in
      let t12 = Node x t1 t2 s12 h12 in
      assert (is_wdm t12);
      let s123 = s12 + sot_wds t3 + 1 in
      assert (s123 == s);
      let h123 = (M.max h12 h3) + 1 in
      Some (Node z t12 t3 s h123)
  | _ -> None

let rotate_left (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x t1 (Node z t2 t3 _ _) s _ ->
      let t12 = merge_tree x t1 t2 in
      let t123 = merge_tree z t12 t3 in
      Some t123
  | _ -> None

let equiv_rl (#a: Type) (r: wdm a) :
  Lemma (rotate_left r == rotate_left_wdm r)
  = ()

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
let rotate_right_wdm (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x (Node z t1 t2 _ _) t3 s _ ->
      let s23 = sot_wds t2 + sot_wds t3 + 1 in
      let h1 = hot_wdh t1 in
      let h2 = hot_wdh t2 in
      let h3 = hot_wdh t3 in
      let h23 = (M.max h2 h3) + 1 in
      let t23 = Node x t2 t3 s23 h23 in
      assert (is_wdm t23);
      let s123 = sot_wds t1 + s23 + 1 in
      assert (s123 == s);
      let h123 = (M.max h1 h23) + 1 in
      Some (Node z t1 t23 s h123)
  | _ -> None

let rotate_right (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x (Node z t1 t2 _ _) t3 s _ ->
      let t23 = merge_tree x t2 t3 in
      let t123 = merge_tree z t1 t23 in
      Some t123
  | _ -> None

let equiv_rr (#a: Type) (r: wdm a) :
  Lemma (rotate_right r == rotate_right_wdm r)
  = ()

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
let rotate_right_left_wdm (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x t1 (Node z (Node y t2 t3 _ _) t4 _ _) s _ ->
      assert (is_wdm r);
      assert (is_wdm (cright r));
      assert (is_wdm (cleft r));
      let s12 = sot_wds t1 + sot_wds t2 + 1 in
      let h1 = hot_wdh t1 in
      let h2 = hot_wdh t2 in
      let h12 = M.max h1 h2 + 1 in
      let t12 = Node x t1 t2 s12 h12 in
      assert (is_wdm t12);
      let s34 = sot_wds t3 + sot_wds t4 + 1 in
      let h3 = hot_wdh t3 in
      let h4 = hot_wdh t4 in
      let h34 = M.max h3 h4 + 1 in
      let t34 = Node z t3 t4 s34 h34 in
      assert (is_wdm t34);
      let s1234 = s12 + s34 + 1 in
      let h1234 = M.max h12 h34 + 1 in
      assert (s1234 == s);
      Some (Node y t12 t34 s h1234)
  | _ -> None

let rotate_right_left (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x t1 (Node z (Node y t2 t3 _ _) t4 _ _) s _ ->
      assert (is_wdm r);
      assert (is_wdm (cright r));
      assert (is_wdm (cleft r));
      let t12 = merge_tree x t1 t2 in
      let t34 = merge_tree z t3 t4 in
      let t1234 = merge_tree y t12 t34 in
      Some t1234
  | _ -> None

let equiv_rrl (#a: Type) (r: wdm a) :
  Lemma (rotate_right_left r == rotate_right_left_wdm r)
  = ()

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
let rotate_left_right_wdm (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x (Node z t1 (Node y t2 t3 _ _) _ _) t4 s _ ->
      assert (is_wdm r);
      assert (is_wdm (cright r));
      assert (is_wdm (cleft r));
      let s12 = sot_wds t1 + sot_wds t2 + 1 in
      let h1 = hot_wdh t1 in
      let h2 = hot_wdh t2 in
      let h12 = M.max h1 h2 + 1 in
      let t12 = Node z t1 t2 s12 h12 in
      assert (is_wdm t12);
      let s34 = sot_wds t3 + sot_wds t4 + 1 in
      let h3 = hot_wdh t3 in
      let h4 = hot_wdh t4 in
      let h34 = M.max h3 h4 + 1 in
      let t34 = Node x t3 t4 s34 h34 in
      assert (is_wdm t34);
      let s1234 = s12 + s34 + 1 in
      assert (s1234 == s);
      let h1234 = M.max h12 h34 + 1 in
      Some (Node y t12 t34 s h1234)
  | _ -> None

let rotate_left_right (#a: Type) (r: wdm a) : option (wdm a) =
  match r with
  | Node x (Node z t1 (Node y t2 t3 _ _) _ _) t4 s _ ->
      assert (is_wdm r);
      assert (is_wdm (cright r));
      assert (is_wdm (cleft r));
      let t12 = merge_tree z t1 t2 in
      let t34 = merge_tree x t3 t4 in
      let t1234 = merge_tree y t12 t34 in
      Some t1234
  | _ -> None

let equiv_rlr (#a: Type) (r: wdm a) :
  Lemma (rotate_left_right r == rotate_left_right_wdm r)
  = ()

//@Trees/AVL
let rotate_left_size (#a: Type) (r: wdm a)
  : Lemma
  (requires Some? (rotate_left r))
  (ensures size_of_tree (Some?.v (rotate_left r)) == size_of_tree r)
  = ()
let rotate_right_size (#a: Type) (r: wdm a)
  : Lemma
  (requires Some? (rotate_right r))
  (ensures size_of_tree (Some?.v (rotate_right r)) == size_of_tree r)
  = ()
let rotate_right_left_size (#a: Type) (r: wdm a)
  : Lemma
  (requires Some? (rotate_right_left r))
  (ensures
  size_of_tree (Some?.v (rotate_right_left r)) == size_of_tree r)
  = ()
let rotate_left_right_size (#a: Type) (r: wdm a)
  : Lemma
  (requires Some? (rotate_left_right r))
  (ensures
  size_of_tree (Some?.v (rotate_left_right r)) == size_of_tree r)
  = ()

let rotate_left_height (#a: Type) (t: wdm a)
  : Lemma
  (requires (
    let t' = rotate_left t in
    Some? t' /\ Node? (Some?.v t') /\
    Node? t /\ Node? (cright t) /\
    hot_wdh (cleft t) <= hot_wdh (cright (cright t))
  ))
  (ensures (
    let t' = Some?.v (rotate_left t) in
    hot_wdh t' <= hot_wdh t
  ))
  = ()

let rotate_right_height (#a: Type) (t: wdm a)
  : Lemma
  (requires (
    let t' = rotate_right t in
    Some? t' /\ Node? (Some?.v t') /\
    Node? t /\ Node? (cleft t) /\
    hot_wdh (cright t) <= hot_wdh (cleft (cleft t))
  ))
  (ensures (
    let t' = Some?.v (rotate_right t) in
    hot_wdh t' <= hot_wdh t
  ))
  = ()

#push-options "--z3rlimit 25"
let rotate_right_left_height (#a: Type) (t: wdm a)
  : Lemma
  (requires (
    let t' = rotate_right_left t in
    Some? t' /\ Node? (Some?.v t') /\
    Node? t /\ Node? (cright t) /\
    hot_wdh (cleft t) <= hot_wdh (cright (cright t))
  ))
  (ensures (
    let t' = Some?.v (rotate_right_left t) in
    hot_wdh t' <= hot_wdh t
  ))
  = ()

let rotate_left_right_height (#a: Type) (t: wdm a)
  : Lemma
  (requires (
    let t' = rotate_left_right t in
    Some? t' /\ Node? (Some?.v t') /\
    Node? t /\ Node? (cleft t) /\
    hot_wdh (cright t) <= hot_wdh (cleft (cleft t))
  ))
  (ensures (
    let t' = Some?.v (rotate_left_right t) in
    hot_wdh t' <= hot_wdh t
  ))
  = ()
#pop-options
