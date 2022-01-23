module NTreeC3

open FStar.Ghost
open Steel.FractionalPermission

module Mem = Steel.Memory
module Spec = Trees
module U = FStar.UInt64

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

#set-options "--fuel 1 --ifuel 1 --z3rlimit 15"

#push-options "--__no_positivity"

noeq type node (a: Type0) = {
  data: a;
  left: ref (node a);
  right: ref (node a);
  size: ref U.t;
}
#pop-options

let get_left #a n = n.left
let get_right #a n = n.right
let get_data #a n = n.data
let get_size #a n = n.size

let mk_node #a data left right size = {
  data;
  left;
  right;
  size
}

let null_t #a = null
let is_null_t #a ptr = is_null ptr

//let wds (a: Type0) : Type0 = x:Spec.tree a{fst (Spec.is_wds x)}

let rec tree_sl' (#a: Type0) (ptr: t a) (tree: wds (node a))
  : Tot slprop (decreases tree)
  =
  match tree with
  | Spec.Leaf -> Mem.pure (ptr == null_t)
  | Spec.Node data left right size ->
    Spec.check tree;
    pts_to_sl ptr full_perm data `Mem.star`
    tree_sl' (get_left data) left `Mem.star`
    tree_sl' (get_right data) right `Mem.star`
    pts_to_sl (get_size data) full_perm (U.uint_to_t size)

let tree_sl #a ptr = Mem.h_exists (tree_sl' ptr)

let rec tree_view_aux (#a: Type0) (tree: wds (node a))
  : Tot (Spec.tree a) (decreases tree)
  =
  match tree with
  | Spec.Leaf -> Spec.Leaf
  | Spec.Node data left right size ->
    Spec.Node (get_data data) (tree_view_aux left) (tree_view_aux right) size

let rec tree_view_aux_same_size (#a: Type0) (tree: wds (node a))
  : Lemma (Spec.size_of_tree tree = Spec.size_of_tree (tree_view_aux tree))
  =
  match tree with
  | Spec.Leaf -> ()
  | Spec.Node _ l r _ ->
      tree_view_aux_same_size l;
      tree_view_aux_same_size r;
      ()

let rec tree_view_aux_same_size2 (#a: Type0) (tree: wds (node a))
  : Lemma (fst (Spec.is_wds (tree_view_aux tree)))
  =
  match tree with
  | Spec.Leaf -> ()
  | Spec.Node _ l r s ->
      tree_view_aux_same_size2 l;
      tree_view_aux_same_size2 r;
      ()

let tree_view (#a: Type0) (tree: wds (node a))
  : Tot (wds a)
  =
  tree_view_aux_same_size tree;
  tree_view_aux_same_size2 tree;
  tree_view_aux tree

let tree_sel_node' (#a: Type0) (ptr: t a) : selector' (wds (node a)) (tree_sl ptr) =
  fun h -> id_elim_exists (tree_sl' ptr) h

let tree_sl'_witinv (#a: Type0) (ptr: t a) : Lemma(is_witness_invariant (tree_sl' ptr))
  = let rec aux (ptr:t a) (x y:wds (node a)) (m:mem) : Lemma
        (requires interp (tree_sl' ptr x) m /\ interp (tree_sl' ptr y) m)
        (ensures x == y)
        (decreases x)
    = match x with
      | Spec.Leaf -> begin match y with
         | Spec.Leaf -> ()
         | Spec.Node data left right size ->
           Mem.pure_interp (ptr == null_t) m;
           Spec.check y;
           let p1 = pts_to_sl ptr full_perm data in
           let p2 = tree_sl' (get_left data) left in
           let p3 = tree_sl' (get_right data) right in
           let p4 = pts_to_sl (get_size data) full_perm (U.uint_to_t size) in
           Mem.affine_star (p1 `Mem.star` p2 `Mem.star` p3) p4 m;
           Mem.affine_star (p1 `Mem.star` p2) p3 m;
           Mem.affine_star p1 p2 m;
           pts_to_not_null ptr full_perm data m
       end
      | Spec.Node data1 left1 right1 size1 -> begin match y with
        | Spec.Leaf ->
           Mem.pure_interp (ptr == null_t) m;
           Spec.check x;
           let p1 = pts_to_sl ptr full_perm data1 in
           let p2 = tree_sl' (get_left data1) left1 in
           let p3 = tree_sl' (get_right data1) right1 in
           let p4 = pts_to_sl (get_size data1) full_perm (U.uint_to_t size1) in
           Mem.affine_star (p1 `Mem.star` p2 `Mem.star` p3) p4 m;
           Mem.affine_star (p1 `Mem.star` p2) p3 m;
           Mem.affine_star p1 p2 m;
           pts_to_not_null ptr full_perm data1 m
        | Spec.Node data2 left2 right2 size2 ->
           pts_to_witinv ptr full_perm;
           Spec.check x;
           Spec.check y;
           aux (get_left data1) left1 left2 m;
           aux (get_right data1) right1 right2 m;
           assert (left1 == left2);
           assert (right1 == right2);
           Spec.equiv_sot_wds x;
           Spec.equiv_sot_wds y;
           assert (size1 == Spec.size_of_tree x);
           assert (size2 == Spec.size_of_tree y);
           assert (size1 == size2);
           assert (x == y);
           ()
      end

    in
    Classical.forall_intro_3 (Classical.move_requires_3 (aux ptr))

let tree_sel_depends_only_on (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (Mem.join m0 m1))
  =
  let m':Mem.hmem (tree_sl ptr) = Mem.join m0 m1 in
  let t1 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m0) in
  let t2 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m') in
  tree_sl'_witinv ptr;
  Mem.elim_wi (tree_sl' ptr) t1 t2 m'

let tree_sel_depends_only_on_core (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr))
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (core_mem m0))
  =
  let t1 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m0) in
  let t2 = Ghost.reveal (id_elim_exists (tree_sl' ptr) (core_mem m0)) in
  tree_sl'_witinv ptr;
  Mem.elim_wi (tree_sl' ptr) t1 t2 (core_mem m0)

let tree_sel_node (#a: Type0) (ptr: t a) : selector (wds (node a)) (tree_sl ptr) =
  Classical.forall_intro_2 (tree_sel_depends_only_on ptr);
  Classical.forall_intro (tree_sel_depends_only_on_core ptr);
  tree_sel_node' ptr

let tree_sel #a r =
  fun h -> tree_view (tree_sel_node r h)

let tree_sel_interp (#a: Type0) (ptr: t a) (t: wds (node a)) (m: mem) : Lemma
  (requires interp (tree_sl' ptr t) m)
  (ensures interp (tree_sl ptr) m /\ tree_sel_node' ptr m == t)
  = intro_h_exists t (tree_sl' ptr) m;
    tree_sl'_witinv ptr

let intro_leaf_lemma (a:Type0) (m:mem) : Lemma
    (requires interp (hp_of emp) m)
    (ensures interp (tree_sl (null_t #a)) m /\ tree_sel (null_t #a) m == Spec.Leaf)
    = let ptr:t a = null_t in
      pure_interp (ptr == null_t) m;
      let open FStar.Tactics in
      assert (tree_sl' ptr Spec.Leaf == Mem.pure (ptr == null_t)) by (norm [delta; zeta; iota]);
      tree_sel_interp ptr Spec.Leaf m

let intro_linked_tree_leaf #opened #a _ =
    change_slprop_2 emp (linked_tree (null_t #a)) (Spec.Leaf <: wds a) (intro_leaf_lemma a)

let elim_leaf_lemma (#a:Type0) (ptr:t a) (m:mem) : Lemma
    (requires interp (tree_sl ptr) m /\ ptr == null_t)
    (ensures interp (tree_sl ptr) m /\ tree_sel ptr m == Spec.Leaf)
    = let l' = id_elim_exists (tree_sl' ptr) m in
      pure_interp (ptr == null_t) m;
      tree_sel_interp ptr Spec.Leaf m

let elim_linked_tree_leaf #opened #a ptr =
  change_slprop_rel (linked_tree ptr) (linked_tree ptr)
    (fun x y -> x == y /\ y == Spec.Leaf)
    (fun m -> elim_leaf_lemma ptr m)

let lemma_node_is_not_null (#a:Type) (ptr:t a) (t:wds a) (m:mem) : Lemma
    (requires interp (tree_sl ptr) m /\ tree_sel ptr m == t /\ Spec.Node? t)
    (ensures ptr =!= null_t)
    =
      let t':wds (node a) = id_elim_exists (tree_sl' ptr) m in
      assert (interp (tree_sl' ptr t') m);
      tree_sel_interp ptr t' m;
       //match reveal (t' <: Spec.tree (node a)) with
       match reveal t' with
      | Spec.Node data left right size ->
           Spec.check (reveal t');
//           let p1 = pts_to_sl ptr full_perm data in
//           let p2 = tree_sl' (get_left data) left in
//           let p3 = tree_sl' (get_right data) right in
//           let p4 = pts_to_sl (get_size data) full_perm (U.uint_to_t size) in
//           Mem.affine_star (p1 `Mem.star` p2 `Mem.star` p3) p4 m;
//           Mem.affine_star (p1 `Mem.star` p2) p3 m;
//           Mem.affine_star p1 p2 m;
           pts_to_not_null ptr full_perm data m

let lemma_not_null_is_node (#a:Type) (ptr:t a) (t:wds a) (m:mem) : Lemma
  (requires interp (tree_sl ptr) m /\ tree_sel ptr m == t /\ ptr =!= null_t)
  (ensures Spec.Node? t)
  =
  let t': wds (node a) = id_elim_exists (tree_sl' ptr) m in
  assert (interp (tree_sl' ptr t') m);
  tree_sel_interp ptr t' m;
  match reveal t' with
  | Spec.Leaf -> Mem.pure_interp (ptr == null_t) m
  | Spec.Node _ _ _ _ -> ()

let node_is_not_null #opened #a ptr =
  let h = get () in
  let t = hide (v_linked_tree ptr h) in
  extract_info (linked_tree ptr) t (ptr =!= null_t) (lemma_node_is_not_null ptr t)

let not_null_is_node #opened #a ptr =
  let h = get () in
  let t = hide (v_linked_tree ptr h) in
  extract_info (linked_tree ptr) t (Spec.Node? t == true) (lemma_not_null_is_node ptr t)

let pack_tree_lemma_aux (#a:Type0) (pt:t a)
  (x: node a) (l r: wds (node a)) (s:nat) (m:mem) : Lemma
  (requires
    s < c /\
    interp (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' (get_left x) l `Mem.star`
      tree_sl' (get_right x) r `Mem.star`
      pts_to_sl (get_size x) full_perm (U.uint_to_t s)
      ) m
    /\ s == Spec.size_of_tree l + Spec.size_of_tree r + 1
  )
  (ensures
     (* TODO : doublon *)
     (
     //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in
     let t = Spec.Node x l r s in
     Spec.induction_wds x l r;
     // let t: Spec.wds (node a) = t in
     interp (tree_sl' pt t) m))
  =
    //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in
    let t = Spec.Node x l r s in
    assert (s = Spec.size_of_tree t);
    assert (fst (Spec.is_wds l));
    assert (fst (Spec.is_wds r));
    Spec.induction_wds x l r;
    assert (fst (Spec.is_wds t));
    let t: wds (node a) = t in
    affine_star (pts_to_sl pt full_perm x `Mem.star` tree_sl' (get_left x) l)
                (tree_sl' (get_right x) r)
                m;
    affine_star (pts_to_sl pt full_perm x) (tree_sl' (get_left x) l) m;

    pts_to_not_null pt full_perm x m;

    emp_unit (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' (get_left x) l `Mem.star`
      tree_sl' (get_right x) r);
    pure_star_interp (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' (get_left x) l `Mem.star`
      tree_sl' (get_right x) r)
      (pt =!= null_t)
      m

// Maintenant, tenter en ajoutant s (et sr) en paramètre(s)
let pack_tree_lemma (#a:Type0) (pt left right:t a) (sr: ref U.t)
  (x: node a) (l r:Spec.wds a) (s:nat) (m:mem) : Lemma
  (requires
    s < c /\
    interp (ptr pt `Mem.star`
      tree_sl left `Mem.star`
      tree_sl right `Mem.star`
      ptr sr) m /\
    get_left x == left /\
    get_right x == right /\
    get_size x == sr /\
    sel_of (vptr pt) m == x /\
    U.v (sel_of (vptr sr) m) == s /\
    sel_of (linked_tree left) m == l /\
    sel_of (linked_tree right) m == r /\
    s == Spec.size_of_tree l + Spec.size_of_tree r + 1
  )
  (ensures
    (
    //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in
    let t = Spec.Node (get_data x) l r s in
    assert (fst (Spec.is_wds l));
    assert (fst (Spec.is_wds r));
    Spec.induction_wds (get_data x) l r;
    assert (fst (Spec.is_wds t));
    //fst (Spec.is_wds t) /\
    interp (tree_sl pt) m /\
    tree_sel pt m == Spec.Node (get_data x) l r s)
  )
  =
    //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in
    let t = Spec.Node (get_data x) l r s in
    Spec.induction_wds (get_data x) l r;
    assert (fst (Spec.is_wds t));

    //let l':Spec.wds a = id_elim_exists (tree_sl' left) m in
    //let r':Spec.wds a = id_elim_exists (tree_sl' right) m in
    let l':wds (node a) = id_elim_exists (tree_sl' left) m in
    let r':wds (node a) = id_elim_exists (tree_sl' right) m in
    let p1 = ptr pt in
    let p2 = tree_sl left in
    let p3 = tree_sl right in
    let p4 = ptr sr in
    let m123, m4 = id_elim_star (p1 `Mem.star` p2 `Mem.star` p3) p4 m in
    let m12, m3 = id_elim_star (p1 `Mem.star` p2) p3 m123 in
    let m1, m2 = id_elim_star p1 p2 m12 in
    //assert (ptr_sel sr m == s);
    // #1
    ptr_sel_interp pt m1;
    // #2
    let l2:wds (node a) = id_elim_exists (tree_sl' left) m2 in
    join_commutative m1 m2;
    assert (interp (tree_sl' left l2) m);
    tree_sl'_witinv left;
    assert (l2 == l');
    assert (interp (tree_sl' left l') m2);
    // #3
    let r2:wds (node a) = id_elim_exists (tree_sl' right) m3 in
    join_commutative m12 m3;
    assert (interp (tree_sl' right r2) m);
    tree_sl'_witinv right;
    assert (r2 == r');
    assert (interp (tree_sl' right r') m3);
    // #4
    ptr_sel_interp sr m4;
    //ptr_sel_interp sr m;
    join_commutative m123 m4;
    assert (U.v (ptr_sel sr m) == s);

    intro_star (pts_to_sl pt full_perm x) (tree_sl' left l') m1 m2;
    intro_star
      (pts_to_sl pt full_perm x `Mem.star` tree_sl' left l')
      (tree_sl' right r')
      m12 m3;
    intro_star
      (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' left l' `Mem.star`
      tree_sl' right r')
      (pts_to_sl sr full_perm (U.uint_to_t s))
      m123 m4;
    ();

    let s = Spec.size_of_tree l' + Spec.size_of_tree r' + 1 in
    let t = Spec.Node x l' r' s in
    Spec.induction_wds x l' r';
    pack_tree_lemma_aux pt x l' r' s m;
    intro_h_exists t (tree_sl' pt) m;
    tree_sel_interp pt t m

let pack_tree #opened #a ptr left right sr =
  let h = get () in
  let x = hide (sel ptr h) in
  let l:Spec.wds a = hide (v_linked_tree left h) in
  let r:Spec.wds a = hide (v_linked_tree right h) in
  let s:U.t = hide (sel sr h) in
  //let s1 = Spec.size_of_tree (reveal l) in
  //let s2 = Spec.size_of_tree (reveal r) in
  //let s = s1 + s2 + 1 in
// TODO : reveal_star_4 / arbitrary arity
// TODO : pourquoi inutile finalement ?
  //reveal_star_3 (vptr ptr) (linked_tree left) (linked_tree right);
  Spec.induction_wds (get_data x) l r;
  //let t:Spec.wds a = Spec.Node (get_data x) l r s in
  let t = Spec.Node (get_data x) l r (U.v s) in

  change_slprop
    (vptr ptr `star` linked_tree left `star` linked_tree right `star` vptr sr)
    (linked_tree ptr)
    (((reveal x, reveal l), reveal r), reveal s) t
    (fun m -> pack_tree_lemma ptr left right sr x l r (U.v s) m)

[@@__steel_reduce__]
let tree_node' #a r : vprop' =
  {hp = tree_sl r;
   t = wds (node a);
   sel = tree_sel_node r}
unfold
let tree_node (#a:Type0) (r:t a) = VUnit (tree_node' r)

[@@ __steel_reduce__]
let v_node
  (#a:Type0)
  (#p:vprop)
  (r:t a)
  (h:rmem p{
    FStar.Tactics.with_tactic selector_tactic (can_be_split p (tree_node r) /\ True)
  })
    : GTot (wds (node a))
  = h (tree_node r)

val reveal_non_empty_tree (#opened:inames) (#a:Type0) (ptr:t a)
  : SteelGhost unit opened (tree_node ptr) (fun _ -> tree_node ptr)
             (requires fun _ -> ptr =!= null_t)
             (ensures fun h0 _ h1 -> v_node ptr h0 == v_node ptr h1 /\
               Spec.Node? (v_node ptr h0))

let reveal_non_empty_lemma (#a:Type) (ptr:t a) (t:wds (node a)) (m:mem) : Lemma
    (requires interp (tree_sl ptr) m /\ tree_sel_node ptr m == t /\ ptr =!= null_t)
    (ensures Spec.Node? t)
= let l' = id_elim_exists (tree_sl' ptr) m in
  tree_sel_interp ptr l' m;
  pure_interp (ptr == null_t) m

let is_node (#a:Type) (t:wds (node a)) : prop = match t with
  | Spec.Leaf -> False
  | Spec.Node _ _ _ _ -> True

let reveal_non_empty_tree #opened #a ptr =
  let h = get () in
  let t = hide (v_node ptr h) in
  extract_info (tree_node ptr) t (is_node t) (reveal_non_empty_lemma ptr t)

let head (#a:Type0) (t:erased (wds (node a)))
  : Pure (erased (node a)) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node n _ _ _ = reveal t in hide n

let gleft (#a:Type0) (t:erased (wds (node a)))
  : Pure (erased (Spec.wds (node a))) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ l _ _ = reveal t in hide l

let gright (#a:Type0) (t:erased (wds (node a)))
  : Pure (erased (Spec.wds (node a))) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ _ r _ = reveal t in hide r

let gsize (#a:Type0) (t:erased (wds (node a)))
  : Pure (erased nat) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ _ _ s = reveal t in hide s

(* PLUS BESOIN : voir tree_view, à mon sens tout doit reposer dessus *)
(*let check2 #a (t: Spec.wds (node a)) : Lemma
  (requires Spec.Node? t)
  (ensures (let Spec.Node x _ _ s = t in s = get_size x))
*)

let unpack_tree_node_lemma (#a:Type0) (pt:t a) (t:wds (node a)) (m:mem) : Lemma
  (requires
    Spec.Node? t /\
    interp (tree_sl pt) m /\
    tree_sel_node pt m == t)
  (ensures (
    let Spec.Node x l r s = t in

    interp (ptr pt `Mem.star`
      tree_sl (get_left x) `Mem.star`
      tree_sl (get_right x) `Mem.star`
      ptr (get_size x)
    ) m /\
    sel_of (vptr pt) m == x /\
    tree_sel_node (get_left x) m == l /\
    tree_sel_node (get_right x) m == r /\
    U.v (sel_of (vptr (get_size x)) m) == s /\
    fst (Spec.is_wds l) /\
    fst (Spec.is_wds r) /\
    s == Spec.size_of_tree t /\
    s < c
    )
  )
  =
    let Spec.Node x l r s = t in
    Spec.check t;
    assert (s < c);
    assert (fst (Spec.is_wds l));
    assert (fst (Spec.is_wds r));
    assert (fst (Spec.is_wds t));
    Spec.check t;
    assert (s == Spec.size_of_tree t);
    //check2 t;
    tree_sel_interp pt t m;

    let sl = pts_to_sl pt full_perm x `Mem.star`
    tree_sl' (get_left x) l `Mem.star`
    tree_sl' (get_right x) r `Mem.star`
    pts_to_sl (get_size x) full_perm (U.uint_to_t s)
    in

    pure_star_interp sl (pt =!= null_t) m;
    emp_unit sl;
    assert (interp sl m);

    let p1 = pts_to_sl pt full_perm x in
    let p2 = tree_sl' (get_left x) l in
    let p3 = tree_sl' (get_right x) r in
    let p4 = pts_to_sl (get_size x) full_perm (U.uint_to_t s) in
    //let p12 = p1 `Mem.star` p2 in
    let m123, m4 = id_elim_star
      (p1 `Mem.star` p2 `Mem.star` p3) p4 m in
    assert (join m123 m4 == m);
    let m12, m3 = id_elim_star
      (p1 `Mem.star` p2) p3 m123 in
    assert (hide (join m12 m3) == m123);
    let m1, m2 = id_elim_star
      p1 p2 m12 in
    assert (hide (join m1 m2) == m12);

    // #1
    intro_ptr_interp pt (hide x) m1;
    ptr_sel_interp pt m1;
    pts_to_witinv pt full_perm;
    // #2
    tree_sel_interp (get_left x) l m2;
    tree_sl'_witinv (get_left x);
    intro_star
      (ptr pt)
      (tree_sl (get_left x)) m1 m2;
    join_commutative m1 m2;
    assert (reveal m12 == join m1 m2);
    assert (interp (ptr pt `Mem.star` tree_sl (get_left x)) m12);
    // #3
    tree_sel_interp (get_right x) r m3;
    tree_sl'_witinv (get_right x);
    intro_star
      (ptr pt `Mem.star` tree_sl (get_left x))
      (tree_sl (get_right x)) m12 m3;
    join_commutative m12 m3;
    assert (reveal m123 == join m12 m3);
    assert (interp (ptr pt `Mem.star`
      tree_sl (get_left x) `Mem.star`
      tree_sl (get_right x)
    ) m123);
    // #4
    let sr = get_size x in
    intro_ptr_interp sr (hide (U.uint_to_t s)) m4;
    ptr_sel_interp sr m4;
    pts_to_witinv sr full_perm;
    intro_star
      (ptr pt `Mem.star`
      tree_sl (get_left x) `Mem.star`
      tree_sl (get_right x))
      (ptr sr) m123 m4;
    join_commutative m123 m4;
    assert (m == join m123 m4);
    assert (interp (ptr sr) m4);
    assert (interp (ptr pt `Mem.star`
      tree_sl (get_left x) `Mem.star`
      tree_sl (get_right x) `Mem.star`
      ptr sr
    ) m);
    ()

let unpack_tree_node_lemma_size (#a:Type0) (pt:t a) (t:Spec.wds (node a)) (m:mem) : Lemma
  (requires
    Spec.Node? t /\
    interp (tree_sl pt) m /\
    tree_sel_node pt m == t)
  (ensures (
    reveal (gsize t) == Spec.size_of_tree t
    )
  )
  = unpack_tree_node_lemma pt t m


let unpack_tree_node (#a:Type0) (ptr:t a)
  : Steel (node a)
             (tree_node ptr)
             (fun n ->
               vptr ptr `star`
               tree_node (get_left n) `star`
               tree_node (get_right n) `star`
               vptr (get_size n))
             (fun _ -> not (is_null_t ptr))
             (fun h0 n h1 ->
               Spec.Node? (v_node ptr h0) /\
               sel ptr h1 == n /\
               v_node ptr h0 == Spec.Node (sel ptr h1)
                 (v_node (get_left n) h1) (v_node (get_right n) h1) (U.v (sel (get_size n) h1)) /\
               U.v (sel (get_size n) h1) == Spec.size_of_tree (v_node (get_left n) h1)
                                    + Spec.size_of_tree (v_node (get_right n) h1) + 1 /\
               U.v (sel (get_size n) h1) < c
             )
  =
  let h0 = get () in
  let t = hide (v_node ptr h0) in
  reveal_non_empty_tree ptr;

  let gn = head t in
  extract_info (tree_node ptr) t
    (reveal (gsize (reveal t)) == Spec.size_of_tree (reveal t))
    (fun m -> unpack_tree_node_lemma_size ptr t m);
  assert (reveal (gsize (reveal t)) == Spec.size_of_tree (reveal t));
  let s = hide (Spec.size_of_tree (reveal t)) in
  assert (s < c);

  change_slprop
    (tree_node ptr)
    (vptr ptr `star` tree_node (get_left gn) `star` tree_node (get_right gn) `star` vptr (get_size gn))
    t (((reveal gn, reveal (gleft t)), reveal (gright t)), U.uint_to_t (Spec.size_of_tree (reveal t)))
    (fun m -> unpack_tree_node_lemma ptr t m);

  let n = read ptr in
  change_slprop_rel (tree_node (get_left gn)) (tree_node (get_left n)) (fun x y -> x == y) (fun _ -> ());
  change_slprop_rel (tree_node (get_right gn)) (tree_node (get_right n)) (fun x y -> x == y) (fun _ -> ());
  change_slprop_rel (vptr (get_size gn)) (vptr (get_size n)) (fun x y -> x == y) (fun _ -> ());

  return n

let unpack_tree (#a: Type0) (ptr: t a)
    : Steel (node a)
      (linked_tree ptr)
      (fun node ->
        vptr ptr `star`
        linked_tree (get_left node) `star`
        linked_tree (get_right node) `star`
        vptr (get_size node))
      (requires (fun h0 -> not (is_null_t ptr)))
      (ensures (fun h0 node h1 ->
        v_linked_tree ptr h0 == Spec.Node
          (get_data (sel ptr h1))
          (v_linked_tree (get_left node) h1)
          (v_linked_tree (get_right node) h1)
          (U.v (sel (get_size node) h1)) /\
        (sel ptr h1) == node /\
        U.v (sel (get_size node) h1) == Spec.size_of_tree (v_linked_tree (get_left node) h1)
                                + Spec.size_of_tree (v_linked_tree (get_right node) h1) + 1 /\
        U.v (sel (get_size node) h1) < c
      ))
  =
  let h0 = get() in
  change_slprop_rel
    (linked_tree ptr)
    (tree_node ptr)
    (fun x y -> x == tree_view y)
    (fun _ -> ());
  let h1 = get () in
  assert (v_linked_tree ptr h0 == tree_view (v_node ptr h1));
  let n = unpack_tree_node ptr in
  let h2 = get () in
  assert (U.v (sel (get_size n) h2) ==
    Spec.size_of_tree (v_node (get_left n) h2)
  + Spec.size_of_tree (v_node (get_right n) h2) + 1);

  change_slprop_rel
    (tree_node (get_left n))
    (linked_tree (get_left n))
    (fun x y -> tree_view x == y)
    (fun _ -> ());
  change_slprop_rel
    (tree_node (get_right n))
    (linked_tree (get_right n))
    (fun x y -> tree_view x == y)
    (fun _ -> ());
  let h3 = get () in
  assert (v_linked_tree (get_left n) h3 == tree_view (v_node (get_left n) h2));
  assert (v_linked_tree (get_right n) h3 == tree_view (v_node (get_right n) h2));
  tree_view_aux_same_size (v_node (get_left n) h2);
  tree_view_aux_same_size (v_node (get_right n) h2);
  return n

