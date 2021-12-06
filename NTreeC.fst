module NTreeC

open FStar.Ghost
open Steel.FractionalPermission

module Mem = Steel.Memory
module Spec = Trees

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

#set-options "--fuel 1 --ifuel 1 --z3rlimit 15 --ide_id_info_off"

#push-options "--__no_positivity"
noeq type node (a: Type0) = {
  data: a;
  left: ref (node a);
  right: ref (node a);
  size: nat;
}
#pop-options

let get_left #a n = n.left
let get_right #a n = n.right
let get_data #a n = n.data
let get_size #a n = n.size

let mk_node #a data left right size =
{
  data;
  left;
  right;
  size;
}


let null_t #a = null
let is_null_t #a ptr = is_null ptr

(*
let rec tree_sl2' (#a: Type0) (ptr: t a) (tree: Spec.tree (node a)) : Tot slprop (decreases tree) =
  match tree with
  | Spec.Leaf -> Mem.pure (ptr == null_t)
  | Spec.Node n left right size ->
    pts_to_sl ptr full_perm n `Mem.star`
    tree_sl2' n.left left `Mem.star`
    tree_sl2' n.right right `Mem.star`
    Mem.pure (size == get_size n)
*)

let rec size_of_tree #a (tree: Spec.tree a)
  : Tot nat (decreases tree)
  = match tree with
  | Spec.Leaf -> 0
  | Spec.Node _ left right _ ->
      size_of_tree left + size_of_tree right + 1
(* test *)

let rec tree_sl' (#a: Type0) (ptr: t a) (tree: Spec.tree (node a)) : Tot slprop (decreases tree) =
  match tree with
  | Spec.Leaf -> Mem.pure (ptr == null_t)
  | Spec.Node n left right size ->
      //let size = size_of_tree tree in
      //let n' = { n with size } in
    //Mem.pure (size == size_of_tree tree) `Mem.star`
    pts_to_sl ptr full_perm n `Mem.star`
    tree_sl' n.left left `Mem.star`
    tree_sl' n.right right `Mem.star`
    Mem.pure (size == size_of_tree tree)

let tree_sl #a ptr = Mem.h_exists (tree_sl' ptr)

let rec tree_view (#a: Type0) (tree: Spec.tree (node a)) : Tot (Spec.tree a) (decreases tree) =
  match tree with
  | Spec.Leaf -> Spec.Leaf
  | Spec.Node data left right size -> Spec.Node (get_data data) (tree_view left) (tree_view right) size

let tree_sel_node' (#a: Type0) (ptr: t a) : selector' (Spec.tree (node a)) (tree_sl ptr) =
  fun h -> id_elim_exists (tree_sl' ptr) h

(*
let witinv_aux2 (#a: Type) (x y:tree (node a))
  : Lemma
    (requires x == y)
    (ensures size_of_tree x == size_of_tree y)
  = ()

let witinv_aux3 (#a: Type) (x1 y1 x2 y2:tree (node a)) (n:node a) (s:nat)
  : Lemma
    (requires x1 == x2 /\ y1 == y2)
    (ensures size_of_tree (Spec.Node n x1 y1 s) == size_of_tree (Spec.Node n x2 y2 s))
  = ()
*)

let rec witinv_aux (#a: Type) (ptr:t a) (x y:tree (node a)) (m:mem)
  : Lemma
    (requires interp (tree_sl' ptr x) m /\ interp (tree_sl' ptr y) m)
    (ensures x == y)
    (decreases x)
(*)  = match (x, y) with
    | Spec.Leaf, Spec.Leaf -> ()
    | Spec.Leaf, Spec.Node n left right _
    | Spec.Node n left right _, Spec.Leaf ->
        Mem.pure_interp (ptr == null_t) m;
        assert (ptr == null_t);
        Mem.affine_star
          (pts_to_sl ptr full_perm (hide n) `Mem.star`
          tree_sl' (get_left n) left)
          (tree_sl' (get_right n) right) m;
        Mem.affine_star
          (pts_to_sl ptr full_perm n)
          (tree_sl' (get_left n) left) m;
        pts_to_not_null ptr full_perm n m;
        assert (ptr =!= null_t);
        assert false
    | _, _ -> admit()

*)
  = match x with
    | Spec.Leaf -> begin match y with
      | Spec.Leaf -> ()
      | Spec.Node n left right _ ->
          Mem.pure_interp (ptr == null_t) m;
          assert (ptr == null_t);
          (*Mem.affine_star
            (pts_to_sl ptr full_perm n
            `Mem.star` tree_sl' (get_left n) left)
            (tree_sl' (get_right n) right)
            m;*)
          (*Mem.affine_star
            (pts_to_sl ptr full_perm n)
            (tree_sl' (get_left n) left) m;*)
          pts_to_not_null ptr full_perm n m;
          assert (ptr =!= null_t);
          assert false
      end
    | Spec.Node n1 left1 right1 size1 -> begin match y with
      | Spec.Leaf ->
          Mem.pure_interp (ptr == null_t) m;
          assert (ptr == null_t);
          (*Mem.affine_star
            (pts_to_sl ptr full_perm n1
            `Mem.star` tree_sl' (get_left n1) left1)
            (tree_sl' (get_right n1) right1)
            m;
          Mem.affine_star
            (pts_to_sl ptr full_perm n1)
            (tree_sl' (get_left n1) left1) m;*)
          pts_to_not_null ptr full_perm n1 m;
          assert (ptr =!= null_t);
          assert false
      | Spec.Node n2 left2 right2 size2 ->
          pts_to_witinv ptr full_perm;
          witinv_aux (get_left n1) left1 left2 m;
          witinv_aux (get_right n1) right1 right2 m;
          assert (left1 == left2);
          assert (right1 == right2);
          //witinv_aux2 left1 left2;
          //witinv_aux2 right1 right2;
          assert (size_of_tree left1 == size_of_tree left2);
          assert (size_of_tree right1 == size_of_tree right2);
          //Classical.forall_intro_2 (Classical.move_requires_2 (witinv_aux3 left1 left2 right1 right2));
          //assert (size1 == size2);
          assert (size_of_tree left1 == size_of_tree left2);
          assert (size_of_tree right1 == size_of_tree right2);
          Mem.pure_interp (size1 == size_of_tree x) m;
          Mem.pure_interp (size2 == size_of_tree y) m;
          assert (size1 == size2);
          ()
      end


let tree_sl'_witinv (#a: Type0) (ptr: t a)
  : Lemma(is_witness_invariant (tree_sl' ptr))
  = Classical.forall_intro_3
     (Classical.move_requires_3 (witinv_aux ptr))

(* let rec aux (ptr:t a) (x y:tree (node a)) (m:mem) : Lemma
        (requires interp (tree_sl' ptr x) m /\ interp (tree_sl' ptr y) m)
        (ensures x == y)
        (decreases x)
    (*)= match x with
      | Spec
    match (x, y) with
      | Spec.Leaf, Spec.Leaf -> ()
      | Spec.Node data left right _, Spec.Leaf ->
      //| Spec.Leaf, Spec.Node data left right _ ->
          Mem.pure_interp (ptr == null_t) m;
          Mem.affine_star
            (pts_to_sl ptr full_perm data `Mem.star` tree_sl' (get_left data) left)
            (tree_sl' (get_right data) right) m;
          Mem.affine_star
            (pts_to_sl ptr full_perm data)
            (tree_sl' (get_left data) left) m;
          pts_to_not_null ptr full_perm data m
    *)
    = match x with
      | Spec.Leaf -> begin match y with
         | Spec.Leaf -> ()
         | Spec.Node data left right _ ->
           Mem.pure_interp (ptr == null_t) m;
           Mem.affine_star (pts_to_sl ptr full_perm data `Mem.star` tree_sl' (get_left data) left)
             (tree_sl' (get_right data) right) m;
           Mem.affine_star (pts_to_sl ptr full_perm data) (tree_sl' (get_left data) left) m;
           pts_to_not_null ptr full_perm data m
       end
      | Spec.Node data1 left1 right1 _ -> begin match y with
        | Spec.Leaf ->
           Mem.pure_interp (ptr == null_t) m;
           Mem.affine_star (pts_to_sl ptr full_perm data1 `Mem.star` tree_sl' (get_left data1) left1)
             (tree_sl' (get_right data1) right1) m;
           Mem.affine_star (pts_to_sl ptr full_perm data1) (tree_sl' (get_left data1) left1) m;
           pts_to_not_null ptr full_perm data1 m
        | Spec.Node data2 left2 right2 size2 ->
          pts_to_witinv ptr full_perm;
          aux (get_left data1) left1 left2 m;
          aux (get_right data1) right1 right2 m
       end
    in Classical.forall_intro_3 (Classical.move_requires_3 (aux ptr))
*)
let tree_sel_depends_only_on (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (Mem.join m0 m1))
  = let m':Mem.hmem (tree_sl ptr) = Mem.join m0 m1 in
    let t1 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m0) in
    let t2 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m') in

    tree_sl'_witinv ptr;
    Mem.elim_wi (tree_sl' ptr) t1 t2 m'

let tree_sel_depends_only_on_core (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr))
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (core_mem m0))
  = let t1 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m0) in
    let t2 = Ghost.reveal (id_elim_exists (tree_sl' ptr) (core_mem m0)) in
    tree_sl'_witinv ptr;
    Mem.elim_wi (tree_sl' ptr) t1 t2 (core_mem m0)

let tree_sel_node (#a: Type0) (ptr: t a) : selector (Spec.tree (node a)) (tree_sl ptr) =
  Classical.forall_intro_2 (tree_sel_depends_only_on ptr);
  Classical.forall_intro (tree_sel_depends_only_on_core ptr);
  tree_sel_node' ptr

let tree_sel #a r = fun h -> tree_view (tree_sel_node r h)


let tree_sel_interp (#a: Type0) (ptr: t a) (t: tree (node a)) (m: mem) : Lemma
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
      admit()

let intro_linked_tree_leaf #a _ =
    change_slprop_2 emp (linked_tree (null_t #a)) (Spec.Leaf <: tree a) (intro_leaf_lemma a)


let elim_leaf_lemma (#a:Type0) (ptr:t a) (m:mem) : Lemma
    (requires interp (tree_sl ptr) m /\ ptr == null_t)
    (ensures interp (tree_sl ptr) m /\ tree_sel ptr m == Spec.Leaf)
    = let l' = id_elim_exists (tree_sl' ptr) m in
      pure_interp (ptr == null_t) m;
      tree_sel_interp ptr Spec.Leaf m

let elim_linked_tree_leaf #a ptr =
  change_slprop_rel (linked_tree ptr) (linked_tree ptr)
    (fun x y -> x == y /\ y == Spec.Leaf)
    (fun m -> elim_leaf_lemma ptr m)

let lemma_node_not_null (#a:Type) (ptr:t a) (t:tree a) (m:mem)
  : Lemma
    (requires interp (tree_sl ptr) m /\
              tree_sel ptr m == t /\
              Spec.Node? t)
    (ensures ptr =!= null_t)
    = let t' = id_elim_exists (tree_sl' ptr) m in
      assert (interp (tree_sl' ptr t') m);
      tree_sel_interp ptr t' m;
       match reveal t' with
      | Spec.Node data left right _ ->
           (*let size = size_of_tree tree in
           let data = { data with size } in*)
           Mem.affine_star
             (pts_to_sl ptr full_perm (hide data) `Mem.star` tree_sl' (get_left data) left)
             (tree_sl' (get_right data) right) m;
           Mem.affine_star (pts_to_sl ptr full_perm data) (tree_sl' (get_left data) left) m;
           pts_to_not_null ptr full_perm data m

let node_is_not_null #a ptr =
  let h = get () in
  let t = hide (v_linked_tree ptr h) in
  extract_info (linked_tree ptr) t (ptr =!= null_t) (lemma_node_not_null ptr t)

(*
let pack_aux4 (#a: Type) (x y:tree (node a)) (n:node a) (s:nat)
  : Lemma
    (requires True)
    (ensures size_of_tree (Spec.Node n x y s) == size_of_tree x + size_of_tree y + 1)
  = ()
*)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
#restart-solver
let pack_tree_lemma_aux (#a:Type0) (pt:t a)
  (x: node a) (l r:tree (node a)) (s:nat) (m:mem) : Lemma
  (requires
    interp (
      pts_to_sl pt full_perm x `Mem.star`
      tree_sl' (get_left x) l `Mem.star`
      tree_sl' (get_right x) r `Mem.star`
      Mem.pure (s == size_of_tree l + size_of_tree r + 1)
   ) m)
  (ensures interp (tree_sl' pt (Spec.Node x l r s)) m)
  = let t = Spec.Node x l r s in
    (*assert (interp (
      (Mem.pure (s == size_of_tree l + size_of_tree r + 1))
    ) m);*)
    //assert (size_of_tree t == size_of_tree l + size_of_tree r + 1);
    /// on sort l'invariant sur la taille de la slprop
    pure_interp (s == size_of_tree l + size_of_tree r + 1) m;
    //assert (s == size_of_tree l + size_of_tree r + 1);
    //assert (size_of_tree t == s);
    //assert (get_left x == x.left);
    //assert (get_right x == x.right);

    (*assert (
      interp (
        pts_to_sl pt full_perm x `Mem.star`
        tree_sl' x.left l `Mem.star`
        tree_sl' x.right r) m);*)
    /// requis : pourquoi ?
    /// difficile de chercher les sous-slprop
    /// mais la bonne slprop est précisée dans pure_star_interp
    emp_unit (
        pts_to_sl pt full_perm x `Mem.star`
        tree_sl' x.left l `Mem.star`
        tree_sl' x.right r);
    (*assert (
      interp (
        pts_to_sl pt full_perm x `Mem.star`
        tree_sl' x.left l `Mem.star`
        tree_sl' x.right r `Mem.star`
        Mem.pure (s == size_of_tree l + size_of_tree r + 1)
   ) m);*)
   /// on rassemble les morceaux
   Mem.pure_star_interp
      (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' x.left l `Mem.star`
      tree_sl' x.right r)
      (s == size_of_tree t)
      m;
   (*assert (
     interp (
       pts_to_sl pt full_perm x `Mem.star`
       tree_sl' x.left l `Mem.star`
       tree_sl' x.right r `Mem.star`
       Mem.pure (s == size_of_tree t)
   ) m);
   assert (interp (tree_sl' pt t) m);*)
   ()


// exemple minimum pour essayer de voir ce qui se joue plus bas (pure_star_interp, pure_interp, assert/assume)
// let test (#a:Type0) ()


let aux_size_lemma (#a:Type0) (left:t a) (l:tree a) (m:mem)
  : Lemma
  (requires
    interp (tree_sl left) m /\
    sel_of (linked_tree left) m == l
  )
  (ensures
    size_of_tree l == size_of_tree (id_elim_exists (tree_sl' left) m)
  )
  // sel_of
  // linked_tree
  // tree_sl'
  // id_elim_exists (on oublie)
  = let l' = id_elim_exists (tree_sl' left) m in
    let l2' = id_elim_exists (tree_sl' left) m in
    assert (l' == l2');
    admit ()

let pack_tree_lemma (#a:Type0) (pt left right:t a)
  (x: node a) (l r:tree a) (s:nat) (m:mem) : Lemma
  (requires interp (
              ptr pt `Mem.star`
              tree_sl left `Mem.star`
              tree_sl right
    ) m /\
    get_left x == left /\
    get_right x == right /\
    s == size_of_tree l + size_of_tree r + 1 /\
    sel_of (vptr pt) m == x /\
    sel_of (linked_tree left) m == l /\
    sel_of (linked_tree right) m == r)
  (ensures interp (tree_sl pt) m /\ tree_sel pt m == Spec.Node (get_data x) l r s)
  = let l' = id_elim_exists (tree_sl' left) m in
    let r' = id_elim_exists (tree_sl' right) m in
    let aux (m:mem) (ml1 ml2 mr:mem) : Lemma
      (requires
        disjoint ml1 ml2 /\
        disjoint (join ml1 ml2) mr /\
        m == join (join ml1 ml2) mr /\
        interp (ptr pt) ml1 /\
        interp (tree_sl left) ml2 /\
        interp (tree_sl right) mr /\

        interp (tree_sl' left l') m /\
        interp (tree_sl' right r') m /\
        ptr_sel pt ml1 == x /\
        s == size_of_tree l' + size_of_tree r' + 1
      )
      (ensures interp
        (pts_to_sl pt full_perm x `Mem.star`
         tree_sl' left l' `Mem.star`
         tree_sl' right r' `Mem.star`
         Mem.pure (s == size_of_tree l' + size_of_tree r' + 1))
       m)
      = ptr_sel_interp pt ml1;

        let l2 = id_elim_exists (tree_sl' left) ml2 in
        join_commutative ml1 ml2;
        assert (interp (tree_sl' left l2) m);
        tree_sl'_witinv left;
        assert (l2 == l');
        assert (interp (tree_sl' left l') ml2);

        let r2 = id_elim_exists (tree_sl' right) mr in
        join_commutative (join ml1 ml2) mr;
        assert (interp (tree_sl' right r2) m);
        tree_sl'_witinv right;
        assert (r2 == r');
        assert (interp (tree_sl' right r') mr);

        intro_star (pts_to_sl pt full_perm x) (tree_sl' left l') ml1 ml2;
        intro_star
          (pts_to_sl pt full_perm x `Mem.star` tree_sl' left l')
          (tree_sl' right r')
          (join ml1 ml2) mr;
        //pure_interp (s == size_of_tree l' + size_of_tree r' + 1);
        assert (interp
        (pts_to_sl pt full_perm x `Mem.star`
         tree_sl' left l' `Mem.star`
         tree_sl' right r')
         m);
        assert (s == size_of_tree l' + size_of_tree r' + 1);
        pure_star_interp (
          pts_to_sl pt full_perm x `Mem.star`
          tree_sl' left l' `Mem.star`
          tree_sl' right r'
        )
        (s == size_of_tree l' + size_of_tree r' + 1)
        m;
        /// required, why?
        emp_unit (
          pts_to_sl pt full_perm x `Mem.star`
          tree_sl' left l' `Mem.star`
          tree_sl' right r'
        );
        assert (interp
        (pts_to_sl pt full_perm x `Mem.star`
         tree_sl' left l' `Mem.star`
         tree_sl' right r' `Mem.star`
         Mem.pure (s == size_of_tree l' + size_of_tree r' + 1)
         )
         m);

        ()
    in
    elim_star (ptr pt `Mem.star` tree_sl left) (tree_sl right) m;
    Classical.forall_intro (Classical.move_requires
      (elim_star (ptr pt) (tree_sl left)));
    Classical.forall_intro_3 (Classical.move_requires_3 (aux m));
    //assert(s == size_of_tree l + size_of_tree r + 1);
    pure_interp (s == size_of_tree l' + size_of_tree r' + 1) m;
    //assert(s == size_of_tree l' + size_of_tree r' + 1);
    /// on va avoir besoin d'un lemme dédié
    aux_size_lemma left l m;
    aux_size_lemma right r m;
    assert(size_of_tree l' == size_of_tree l);
    assert(size_of_tree r' == size_of_tree r);
    assert(s == size_of_tree l' + size_of_tree r' + 1);
    assert (interp (
      pts_to_sl pt full_perm x `Mem.star`
      tree_sl' left l' `Mem.star`
      tree_sl' right r' `Mem.star`
      Mem.pure (s == size_of_tree l' + size_of_tree r' + 1)
    ) m);
    pack_tree_lemma_aux pt x l' r' s m;
    intro_h_exists (Spec.Node x l' r' s) (tree_sl' pt) m;
    tree_sel_interp pt (Spec.Node x l' r' s) m

let unpack_tree_node_lemma (#a:Type0) (pt:t a) (t:tree (node a)) (m:mem) : Lemma
  (requires Spec.Node? t /\ interp (tree_sl pt) m /\ tree_sel_node pt m == t)
  (ensures (
    let Spec.Node x l r s = t in
    // Etrange ?
    interp (ptr pt `Mem.star` tree_sl (get_left x)
    //interp (pts_to_sl pt full_perm x `Mem.star` tree_sl (get_left x)
    `Mem.star` tree_sl (get_right x) `Mem.star` Mem.pure (s == size_of_tree t)) m /\
    sel_of (vptr pt) m == x /\
    tree_sel_node (get_left x) m == l /\
    tree_sel_node (get_right x) m == r
    /\ s == size_of_tree t)
  )
  = let Spec.Node x l r s = t in

    tree_sel_interp pt t m;

    let sl = pts_to_sl pt full_perm x `Mem.star` tree_sl' (get_left x) l `Mem.star` tree_sl' (get_right x) r in

    //pure_star_interp sl (pt =!= null_t) m;
    emp_unit sl;
    assert (interp sl m);
    let sl' = sl `Mem.star` (Mem.pure (s == size_of_tree t)) in
    let sl2 = ptr pt `Mem.star` tree_sl' (get_left x) l `Mem.star` tree_sl' (get_right x) r in
    let sl2' = sl2 `Mem.star` (Mem.pure (s == size_of_tree t)) in
    emp_unit sl';
    assert (interp sl' m);
    emp_unit sl2';
    emp_unit sl2;
    pure_interp (s == size_of_tree t) m;
    //assert (interp sl2 m);
    //assert (interp sl2' m);
    //assert (s == size_of_tree t);
    //admit();


    let aux (m:mem) (ml1 ml2 mr:mem) : Lemma
      (requires disjoint ml1 ml2 /\ disjoint (join ml1 ml2) mr /\ m == join (join ml1 ml2) mr /\
        interp (pts_to_sl pt full_perm x) ml1 /\
        interp (tree_sl' (get_left x) l) ml2 /\
        interp (tree_sl' (get_right x) r) mr)
      (ensures
        interp (ptr pt `Mem.star` tree_sl (get_left x) `Mem.star` tree_sl (get_right x)) m /\
        sel_of (vptr pt) m == x /\
        tree_sel_node (get_left x) m == l /\
        tree_sel_node (get_right x) m == r)
      = intro_ptr_interp pt (hide x) ml1;
        ptr_sel_interp pt ml1;
        pts_to_witinv pt full_perm;

        tree_sel_interp (get_left x) l ml2;
        intro_star (ptr pt) (tree_sl (get_left x)) ml1 ml2;

        tree_sel_interp (get_right x) r mr;
        tree_sl'_witinv (get_right x);
        join_commutative ml1 ml2;
        let ml = join ml1 ml2 in
        assert (interp (ptr pt `Mem.star` tree_sl (get_left x)) ml);

        intro_star (ptr pt `Mem.star` tree_sl (get_left x)) (tree_sl (get_right x)) ml mr;
        join_commutative ml mr

    in
    elim_star
      (pts_to_sl pt full_perm x `Mem.star` tree_sl' (get_left x) l)
      (tree_sl' (get_right x) r)
      m;
    Classical.forall_intro (Classical.move_requires
      (elim_star (pts_to_sl pt full_perm x) (tree_sl' (get_left x) l)));
    Classical.forall_intro_3 (Classical.move_requires_3 (aux m));
    //let sl' = sl `Mem.star` (Mem.pure (s == size_of_tree t)) in
    let sl2 = ptr pt `Mem.star` tree_sl (get_left x) `Mem.star` tree_sl (get_right x) in
    let sl2' = sl2 `Mem.star` (Mem.pure (s == size_of_tree t)) in
    emp_unit sl2;
    //emp_unit sl2';
    assert (interp sl2 m);
    pure_star_interp sl2 (s == size_of_tree t) m;
    assert (interp sl2' m);
    ()
    //admit ()


// OK jusque-là

// éventuellement, on calcule s dedans comme ça pas besoin de s'embêter
let pack_tree #a ptr left right s =
  // magie noire
  //assert (false);
  let h = get () in
  let x = hide (sel ptr h) in
  let l = hide (v_linked_tree left h) in
  let r = hide (v_linked_tree right h) in
//  let s = hide (size_of_tree (reveal l) + size_of_tree (reveal r) + 1) in
//  assert (reveal s == size_of_tree (Spec.Node (get_data x) l r s));
  //assert (get_left x == left);
  (*emp_unit (
    vptr ptr `Mem.star`
    linked_tree left `Mem.star`
    linked_tree right
  );*)
  (*assert (interp (
              ptr pt `Mem.star`
              tree_sl left `Mem.star`
              tree_sl right
  ) h0);*)
//  /\
//  get_left x == left /\
//  get_right x == right /\
//  s == size_of_tree l + size_of_tree r + 1 /\
//  sel_of (vptr pt) m == x /\
//  sel_of (linked_tree left) m == l /\
//  sel_of (linked_tree right) m == r)

  //aux_size_lemme left l;
  //assert (size_of_tree left == size_of_tree l);
  reveal_star_3 (vptr ptr) (linked_tree left) (linked_tree right);


  change_slprop
    (vptr ptr `star` linked_tree left `star` linked_tree right)
    (linked_tree ptr)
    ((reveal x, reveal l), reveal r)
    (Spec.Node (get_data x) l r s)
    (fun m -> pack_tree_lemma ptr left right x l r s m)

[@@__steel_reduce__]
let tree_node' #a r : vprop' =
  {hp = tree_sl r;
   t = tree (node a);
   sel = tree_sel_node r}
unfold
let tree_node (#a:Type0) (r:t a) = VUnit (tree_node' r)

// duplicata of v_linked_tree
[@@ __steel_reduce__]
let v_node
  (#a:Type0)
  (#p:vprop)
  (r:t a)
  (h:rmem p{
    FStar.Tactics.with_tactic selector_tactic (can_be_split p (tree_node r) /\ True)
  })
    : GTot (tree (node a))
  = h (tree_node r)



val reveal_non_empty_tree (#a:Type0) (ptr:t a)
  : Steel unit (tree_node ptr) (fun _ -> tree_node ptr)
             (requires fun _ -> ptr =!= null_t)
             (ensures fun h0 _ h1 -> v_node ptr h0 == v_node ptr h1 /\
               Spec.Node? (v_node ptr h0))

let reveal_non_empty_lemma (#a:Type) (ptr:t a) (t:tree (node a)) (m:mem) : Lemma
    (requires interp (tree_sl ptr) m /\ tree_sel_node ptr m == t /\ ptr =!= null_t)
    (ensures Spec.Node? t)
= let l' = id_elim_exists (tree_sl' ptr) m in
  tree_sel_interp ptr l' m;
  pure_interp (ptr == null_t) m

let prop_of_bool (b:bool) : prop = match b with
  | true -> True
  | false -> False
let is_node (#a:Type) (t:tree (node a)) : prop =
  prop_of_bool (Spec.Node? t)
(*
let is_node (#a:Type) (t:tree (node a)) : prop = match t with
  | Spec.Leaf -> False
  | Spec.Node _ _ _ -> True
*)

let reveal_non_empty_tree #a ptr =
  let h = get () in
  let t = hide (v_node ptr h) in
  extract_info (tree_node ptr) t (is_node t) (reveal_non_empty_lemma ptr t)

let head (#a:Type0) (t:erased (tree (node a)))
  : Pure (erased (node a)) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node n _ _ _ = reveal t in hide n

let gleft (#a:Type0) (t:erased (tree (node a)))
  : Pure (erased (tree (node a))) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ l _ _ = reveal t in hide l

let gright (#a:Type0) (t:erased (tree (node a)))
  : Pure (erased (tree (node a))) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ _ r _ = reveal t in hide r

let gsize (#a:Type0) (t:erased (tree (node a)))
  : Pure (erased (nat)) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ _ _ s = reveal t in hide s

let unpack_tree_node (#a:Type0) (ptr:t a)
  : Steel (node a)
             (tree_node ptr)
             (fun n -> tree_node (get_left n) `star` tree_node (get_right n) `star` vptr ptr)
             //`star` (Mem.pure (get_size n == size_of_tree (v_node ptr h))))
             (fun _ -> not (is_null_t ptr))
             (fun h0 n h1 ->
               Spec.Node? (v_node ptr h0) /\
               sel ptr h1 == n /\
               v_node ptr h0 == Spec.Node
                 (sel ptr h1)
                 (v_node (get_left n) h1)
                 (v_node (get_right n) h1)
                 (get_size n)

              /\ get_size n
              == size_of_tree (v_node (get_left n) h1) + size_of_tree (v_node (get_right n) h1) + 1)

  =

  //let t = id_elim_exists (tree_sl' ptr) h in
  //let n = read ptr in
  //assert (tree_sl' ptr (get_data n));
  //assert (interp () h);
  //assert (interp (tree_node ptr) h);


  let t = gget (tree_node ptr) in
  reveal_non_empty_tree ptr;
  let h = get () in
  let n = hide (v_node ptr h) in
  assert (Spec.Node? n);
  //admit();
 // let x = head n in
 // let l = gleft n in
 // let r = gright n in
  let s = gsize n in
  assume (size_of_tree (reveal n) == (reveal s));
  //let Spec.Node x l r s = n in
  //admit();
  //assert (Spec.Node? (reveal t));

  //let s = size_of_tree (reveal t) in

  let gn = head t in
  // assume (size_of_tree (v_node l h) + size_of_tree (v_node r h) + 1 == s);
  // assume (size_of_tree (v_node (get_left gn) h) + size_of_tree (v_node (get_right gn) h) + 1 == size_of_tree (v_node ptr h));
  // assume (size_of_tree (v_node (get_left gn) h) + size_of_tree (v_node (get_right gn) h) + 1 == reveal s);
  //let x = hide (get_data n) in
  //let x = hide (get_data n) in
  //let manual_vprop = {
  // hp = Mem.pure (get_size gn == size_of_tree t);
 //  t = nat;
 //  sel = fun _ -> (get_size (sel ptr h)) } in
  change_slprop
    (tree_node ptr)
    (vptr ptr `star`
      tree_node (get_left gn) `star`
      tree_node (get_right gn) `star`
      pure (get_size gn == size_of_tree t)
      //to_vprop (Mem.pure (get_size gn == size_of_tree (v_node (get_left gn) h) + size_of_tree (v_node (get_right gn) h) + 1))
      )
      //VUnit (manual_vprop))
      //(to_vprop (Mem.pure (get_size gn == size_of_tree t))))
    t (((reveal gn, reveal (gleft t)), reveal (gright t)), ())
    (fun m -> unpack_tree_node_lemma ptr t m);

 (*let n = read ptr in
 return n*)


  let n = read ptr in
  let h = get () in
  // assume (size_of_tree (sel_of (tree_sel_node (get_left n))) + size_of_tree (tree_sel_node (get_right n)) + 1 == get_size n);
  //assert (size_of_tree (v_linked_tree (get_left n) h) + size_of_tree (v_linked_tree (get_right n) h) + 1 == get_size n);
  //assume (size_of_tree (sel_of (linked_tree (get_left n))) + size_of_tree (sel_of (linked_tree (get_right n))) + 1 == get_size n);
  //pure_star_interp (tree_node (get_left (reveal gn)) `star` tree_node (get_right (reveal gn)) `star` vptr ptr)
  //  (get_size (reveal gn) == size_of_tree (reveal t)) h;
  change_slprop_rel (tree_node (get_left gn)) (tree_node (get_left n)) (fun x y -> x == y) (fun _ -> ());
  change_slprop_rel (tree_node (get_right gn)) (tree_node (get_right n)) (fun x y -> x == y) (fun _ -> ());
  elim_pure (get_size (reveal gn) == size_of_tree (reveal t));
  //change_slprop_rel (tree_node (get_size gn)) (tree_node (get_size n)) (fun x y -> x == y) (fun _ -> ());

  return n

let unpack_tree (#a: Type0) (ptr: t a)
    : Steel (node a)
      (linked_tree ptr)
      (fun node ->
        linked_tree (get_left node) `star` linked_tree (get_right node) `star` vptr ptr)
      (requires (fun h0 -> not (is_null_t ptr)))
      (ensures (fun h0 node h1 ->
        v_linked_tree ptr h0 == Spec.Node
          (get_data (sel ptr h1))
          (v_linked_tree (get_left node) h1)
          (v_linked_tree (get_right node) h1)
          (get_size node) /\
        (sel ptr h1) == node /\
        (get_size node == size_of_tree (v_linked_tree ptr h1))
      ))
  =
  admit();
  let h = get() in
  //let _ = hide (v_linked_tree ptr h) in
  //assert false;
  change_slprop_rel (linked_tree ptr) (tree_node ptr) (fun x y -> x == tree_view y) (fun _ -> ());
  let h0 = get () in
  //assert (v_linked_tree ptr h == tree_view (v_node ptr h0));
  let n = unpack_tree_node ptr in

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
  return n
