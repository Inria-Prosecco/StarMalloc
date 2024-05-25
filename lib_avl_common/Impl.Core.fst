module Impl.Core

open FStar.Ghost
open Steel.FractionalPermission
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module Mem = Steel.Memory
module U = FStar.UInt64
module Spec = Spec.Trees

#set-options "--fuel 1 --ifuel 1 --z3rlimit 15"

noeq
type node (a: Type0) = {
  data: a;
  left: ref (node a);
  right: ref (node a);
  size: U.t;
  height: U.t;
}

let get_left #a n = n.left
let get_right #a n = n.right
let get_data #a n = n.data
let get_size #a n = n.size
let get_height #a n = n.height

let mk_node #a data left right size height = {
  data;
  left;
  right;
  size;
  height;
}

let null_t #a = null
let is_null_t #a ptr = is_null ptr

let rec tree_sl' (#a: Type0) (p: hpred a) (ptr: t a) (tree: wdm (node a))
  : Tot slprop (decreases tree)
  =
  match tree with
  | Spec.Leaf -> Mem.pure (ptr == null_t)
  | Spec.Node data left right size height ->
    pts_to_sl ptr full_perm data `Mem.star`
    tree_sl' p (get_left data) left `Mem.star`
    tree_sl' p (get_right data) right `Mem.star`
    Mem.pure (get_size data == U.uint_to_t size /\ get_height data == U.uint_to_t height) `Mem.star`
    Mem.pure ((G.reveal p) ptr)

let tree_sl #a p ptr = Mem.h_exists (tree_sl' p ptr)

let rec tree_view_aux (#a: Type0) (tree: wdm (node a))
  : Tot (Spec.tree a) (decreases tree)
  =
  match tree with
  | Spec.Leaf -> Spec.Leaf
  | Spec.Node data left right size height ->
    Spec.Node (get_data data)
      (tree_view_aux left)
      (tree_view_aux right)
      size height

let rec tree_view_aux_same_size (#a: Type0) (tree: wdm (node a))
  : Lemma (Spec.size_of_tree tree = Spec.size_of_tree (tree_view_aux tree))
  =
  match tree with
  | Spec.Leaf -> ()
  | Spec.Node _ l r _ _ ->
      tree_view_aux_same_size l;
      tree_view_aux_same_size r;
      ()

let rec tree_view_aux_same_height (#a: Type0) (tree: wdm (node a))
  : Lemma (Spec.height_of_tree tree = Spec.height_of_tree (tree_view_aux tree))
  =
  match tree with
  | Spec.Leaf -> ()
  | Spec.Node _ l r _ _ ->
      tree_view_aux_same_height l;
      tree_view_aux_same_height r;
      ()


let rec tree_view_aux_same_size2 (#a: Type0) (tree: wdm (node a))
  : Lemma (Spec.is_wdm (tree_view_aux tree))
  =
  match tree with
  | Spec.Leaf -> ()
  | Spec.Node _ l r _ _ ->
      tree_view_aux_same_size2 l;
      tree_view_aux_same_size2 r;
      ()

let tree_view (#a: Type0) (tree: wdm (node a))
  : Tot (wdm a)
  =
  tree_view_aux_same_size tree;
  tree_view_aux_same_size2 tree;
  tree_view_aux tree

let tree_sel_node' (#a: Type0) (p: hpred a) (ptr: t a) : selector' (wdm (node a)) (tree_sl p ptr) =
  fun h -> id_elim_exists (tree_sl' p ptr) h

let tree_sl'_witinv (#a: Type0) (p: hpred a) (ptr: t a)
  : Lemma(is_witness_invariant (tree_sl' p ptr))
  = let rec aux (ptr:t a) (x y:wdm (node a)) (m:mem)
    : Lemma
    (requires interp (tree_sl' p ptr x) m /\ interp (tree_sl' p ptr y) m)
    (ensures x == y)
    (decreases x)
    = match x with
      | Spec.Leaf -> begin match y with
         | Spec.Leaf -> ()
         | Spec.Node data left right size height ->
           Mem.pure_interp (ptr == null_t) m;
           let p1 = pts_to_sl ptr full_perm data in
           let p2 = tree_sl' p (get_left data) left in
           let p3 = tree_sl' p (get_right data) right in
           let p4 = Mem.pure (get_size data == U.uint_to_t size) in
           let p5 = Mem.pure (get_height data == U.uint_to_t height) in
           Mem.affine_star (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4) p5 m;
           Mem.affine_star (p1 `Mem.star` p2 `Mem.star` p3) p4 m;
           Mem.affine_star (p1 `Mem.star` p2) p3 m;
           Mem.affine_star p1 p2 m;
           pts_to_not_null ptr full_perm data m
       end
      | Spec.Node data1 left1 right1 size1 height1 -> begin match y with
        | Spec.Leaf ->
           Mem.pure_interp (ptr == null_t) m;
           let p1 = pts_to_sl ptr full_perm data1 in
           let p2 = tree_sl' p (get_left data1) left1 in
           let p3 = tree_sl' p (get_right data1) right1 in
           let p4 = Mem.pure (get_size data1 == U.uint_to_t size1) in
           let p5 = Mem.pure (get_height data1 == U.uint_to_t height1) in
           Mem.affine_star (p1 `Mem.star` p2 `Mem.star` p3 `Mem.star` p4) p5 m;
           Mem.affine_star (p1 `Mem.star` p2 `Mem.star` p3) p4 m;
           Mem.affine_star (p1 `Mem.star` p2) p3 m;
           Mem.affine_star p1 p2 m;
           pts_to_not_null ptr full_perm data1 m
        | Spec.Node data2 left2 right2 size2 height2 ->
           pts_to_witinv ptr full_perm;
           aux (get_left data1) left1 left2 m;
           aux (get_right data1) right1 right2 m;
           assert (left1 == left2);
           assert (right1 == right2);
           assert (size1 = Spec.size_of_tree x);
           assert (size2 = Spec.size_of_tree y);
           assert (size1 = size2);
           assert (height1 = height2);
           assert (x == y);
           ()
      end

    in
    Classical.forall_intro_3 (Classical.move_requires_3 (aux ptr))

let tree_sel_depends_only_on (#a:Type0) (p: hpred a) (ptr:t a)
  (m0:Mem.hmem (tree_sl p ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (tree_sel_node' p ptr m0 == tree_sel_node' p ptr (Mem.join m0 m1))
  =
  let m':Mem.hmem (tree_sl p ptr) = Mem.join m0 m1 in
  let t1 = Ghost.reveal (id_elim_exists (tree_sl' p ptr) m0) in
  let t2 = Ghost.reveal (id_elim_exists (tree_sl' p ptr) m') in
  tree_sl'_witinv p ptr;
  Mem.elim_wi (tree_sl' p ptr) t1 t2 m'

let tree_sel_depends_only_on_core (#a:Type0) (p: hpred a) (ptr:t a)
  (m0:Mem.hmem (tree_sl p ptr))
  : Lemma (tree_sel_node' p ptr m0 == tree_sel_node' p ptr (core_mem m0))
  =
  let t1 = Ghost.reveal (id_elim_exists (tree_sl' p ptr) m0) in
  let t2 = Ghost.reveal (id_elim_exists (tree_sl' p ptr) (core_mem m0)) in
  tree_sl'_witinv p ptr;
  Mem.elim_wi (tree_sl' p ptr) t1 t2 (core_mem m0)

let tree_sel_node (#a: Type0) (p: hpred a) (ptr: t a)
  : selector (wdm (node a)) (tree_sl p ptr) =
  Classical.forall_intro_2 (tree_sel_depends_only_on p ptr);
  Classical.forall_intro (tree_sel_depends_only_on_core p ptr);
  tree_sel_node' p ptr

let tree_sel #a p r =
  fun h -> tree_view (tree_sel_node p r h)

let tree_sel_interp (#a: Type0) (p: hpred a) (ptr: t a) (t: wdm (node a)) (m: mem)
  : Lemma
  (requires interp (tree_sl' p ptr t) m)
  (ensures interp (tree_sl p ptr) m /\ tree_sel_node' p ptr m == t)
  = intro_h_exists t (tree_sl' p ptr) m;
    tree_sl'_witinv p ptr

let intro_leaf_lemma (a:Type0) (p: hpred a) (m:mem) : Lemma
    (requires interp (hp_of emp) m)
    (ensures interp (tree_sl p (null_t #a)) m /\ tree_sel p (null_t #a) m == Spec.Leaf)
    = let ptr:t a = null_t in
      pure_interp (ptr == null_t) m;
      let open FStar.Tactics in
      assert (tree_sl' p ptr Spec.Leaf == Mem.pure (ptr == null_t)) by (norm [delta; zeta; iota]);
      tree_sel_interp p ptr Spec.Leaf m

let intro_linked_tree_leaf #opened #a p _ =
    change_slprop_2 emp (linked_tree p (null_t #a)) (Spec.Leaf <: wdm a) (intro_leaf_lemma a p)

let elim_leaf_lemma (#a:Type0) (p: hpred a) (ptr:t a) (m:mem) : Lemma
    (requires interp (tree_sl p ptr) m /\ ptr == null_t)
    (ensures interp (hp_of emp) m /\ tree_sel p ptr m == Spec.Leaf)
    = let l' = id_elim_exists (tree_sl' p ptr) m in
      pure_interp (ptr == null_t) m;
      tree_sel_interp p ptr Spec.Leaf m;
      reveal_emp ();
      intro_emp m

let elim_linked_tree_leaf #opened #a p ptr =
  change_slprop_rel (linked_tree p ptr) emp
    (fun x y -> x == Spec.Leaf)
    (fun m -> elim_leaf_lemma p ptr m)

let lemma_node_is_not_null (#a:Type) (p: hpred a) (ptr:t a) (t:wdm a) (m:mem) : Lemma
    (requires interp (tree_sl p ptr) m /\ tree_sel p ptr m == t /\ Spec.Node? t)
    (ensures ptr =!= null_t)
    =
      let t':wdm (node a) = id_elim_exists (tree_sl' p ptr) m in
      assert (interp (tree_sl' p ptr t') m);
      tree_sel_interp p ptr t' m;
      match reveal t' with
      | Spec.Node data _ _ _ _ ->
           pts_to_not_null ptr full_perm data m

let lemma_not_null_is_node (#a:Type) (p: hpred a) (ptr:t a) (t:wdm a) (m:mem) : Lemma
  (requires interp (tree_sl p ptr) m /\ tree_sel p ptr m == t /\ ptr =!= null_t)
  (ensures Spec.Node? t)
  =
  let t': wdm (node a) = id_elim_exists (tree_sl' p ptr) m in
  assert (interp (tree_sl' p ptr t') m);
  tree_sel_interp p ptr t' m;
  match reveal t' with
  | Spec.Leaf -> Mem.pure_interp (ptr == null_t) m
  | _ -> ()

let null_is_leaf #opened #a p ptr =
  change_slprop_rel (linked_tree p ptr) (linked_tree p ptr)
    (fun x y -> x == y /\ y == Spec.Leaf)
    (fun m -> elim_leaf_lemma p ptr m)

let lemma_leaf_is_null (#a:Type) (p: hpred a) (ptr:t a) (t:wdm a) (m:mem) : Lemma
  (requires interp (tree_sl p ptr) m /\ tree_sel p ptr m == t /\
    Spec.Leaf? t)
  (ensures ptr == null_t)
  =
  let t':wdm (node a) = id_elim_exists (tree_sl' p ptr) m in
  assert (interp (tree_sl' p ptr t') m);
  tree_sel_interp p ptr t' m;
  match reveal t' with
  | Spec.Leaf -> Mem.pure_interp (ptr == null_t) m
  | _ -> ()

let leaf_is_null #opened #a p ptr =
  let h = get () in
  let t : erased (wdm a) = hide (v_linked_tree p ptr h) in
  extract_info (linked_tree p ptr) t (ptr == null_t)
    (lemma_leaf_is_null p ptr t)

let node_is_not_null #opened #a p ptr =
  let h = get () in
  let t : erased (wdm a) = hide (v_linked_tree p ptr h) in
  extract_info (linked_tree p ptr) t (ptr =!= null_t) (lemma_node_is_not_null p ptr t)

let not_null_is_node #opened #a p ptr =
  let h = get () in
  let t : erased (wdm a) = hide (v_linked_tree p ptr h) in
  extract_info (linked_tree p ptr) t (Spec.Node? t == true) (lemma_not_null_is_node p ptr t)

let lemma_extract_pred (#a:Type) (p: hpred a) (ptr:t a) (t:wdm a) (m:mem)
  : Lemma
  (requires
    interp (tree_sl p ptr) m /\
    tree_sel p ptr m == t)
  (ensures (G.reveal p) ptr)
  =
  let t':wdm (node a) = id_elim_exists (tree_sl' p ptr) m in
  assert (interp (tree_sl' p ptr t') m);
  tree_sel_interp p ptr t' m;
  match reveal t' with
  | Spec.Leaf -> lemma_leaf_is_null p ptr t m
  | Spec.Node _ _ _ _ _ -> admit ()

let extract_pred #opened #a p ptr =
  let h = get () in
  let t : erased (wdm a) = hide (v_linked_tree p ptr h) in
  extract_info
    (linked_tree p ptr) t
    ((G.reveal p) ptr)
    (lemma_extract_pred p ptr t)

let pack_tree_lemma_aux (#a:Type0) (p: hpred a) (pt:t a)
  (x: node a) (l r: wdm (node a)) (s h:nat) (m:mem) : Lemma
  (requires
    s <= c /\
    h <= c /\
    interp (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' p (get_left x) l `Mem.star`
      tree_sl' p (get_right x) r `Mem.star`
      Mem.pure (get_size x == U.uint_to_t s /\ get_height x == U.uint_to_t h) `Mem.star`
      Mem.pure ((G.reveal p) pt)
    ) m
    /\ s = Spec.size_of_tree l + Spec.size_of_tree r + 1
    /\ h = M.max (Spec.height_of_tree l) (Spec.height_of_tree r) + 1
  )
  (ensures
     (* TODO : doublon *)
     (
     //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in
     let t = Spec.Node x l r s h in
     // let t: wds (node a) = t in
     interp (tree_sl' p pt t) m))
  =
    //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in
    let t = Spec.Node x l r s h in
    assert (s = Spec.size_of_tree t);
    assert (h = Spec.height_of_tree t);
    assert (Spec.is_wdm l);
    assert (Spec.is_wdm t);
    ()

(*
    let t: wdm (node a) = t in
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
*)

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
// Maintenant, tenter en ajoutant s (et sr) en paramètre(s)
let pack_tree_lemma (#a:Type0) (p: hpred a) (pt left right:t a) (sr hr: U.t)
  (x: node a) (l r:wdm a) (s h:nat) (m:mem) : Lemma
  (requires
    s <= c /\
    h <= c /\
    interp (ptr pt `Mem.star`
      tree_sl p left `Mem.star`
      tree_sl p right) m /\
    get_left x == left /\
    get_right x == right /\
    get_size x == sr /\
    get_height x == hr /\
    sel_of (vptr pt) m == x /\
    U.v sr == s /\
    U.v hr == h /\
    sel_of (linked_tree p left) m == l /\
    sel_of (linked_tree p right) m == r /\
    s == Spec.size_of_tree l + Spec.size_of_tree r + 1 /\
    h == M.max (Spec.height_of_tree l) (Spec.height_of_tree r) + 1 /\
    ((G.reveal p) pt)
  )
  (ensures
    (
    let t = Spec.Node (get_data x) l r s h in
    assert (Spec.is_wdm l);
    assert (Spec.is_wdm r);
    assert (Spec.is_wdm t);
    interp (tree_sl p pt) m /\
    tree_sel p pt m == Spec.Node (get_data x) l r s h)
  )
  =
    let t = Spec.Node (get_data x) l r s h in
    assert (Spec.is_wdm t);

    let l':wdm (node a) = id_elim_exists (tree_sl' p left) m in
    let r':wdm (node a) = id_elim_exists (tree_sl' p right) m in
    let p1 = ptr pt in
    let p2 = tree_sl p left in
    let p3 = tree_sl p right in
    let m12, m3 = id_elim_star (p1 `Mem.star` p2) p3 m in
    let m1, m2 = id_elim_star p1 p2 m12 in
    //assert (ptr_sel sr m == s);
    // #1
    ptr_sel_interp pt m1;
    // #2
    let l2:wdm (node a) = id_elim_exists (tree_sl' p left) m2 in
    join_commutative m1 m2;
    assert (interp (tree_sl' p left l2) m);
    tree_sl'_witinv p left;
    assert (l2 == l');
    assert (interp (tree_sl' p left l') m2);
    // #3
    let r2:wdm (node a) = id_elim_exists (tree_sl' p right) m3 in
    join_commutative m12 m3;
    assert (interp (tree_sl' p right r2) m);
    tree_sl'_witinv p right;
    assert (r2 == r');
    assert (interp (tree_sl' p right r') m3);

    intro_star (pts_to_sl pt full_perm x) (tree_sl' p left l') m1 m2;
    intro_star
      (pts_to_sl pt full_perm x `Mem.star` tree_sl' p left l')
      (tree_sl' p right r')
      m12 m3;
    Mem.emp_unit (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' p left l' `Mem.star`
      tree_sl' p right r'
      );
    Mem.pure_star_interp (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' p left l' `Mem.star`
      tree_sl' p right r'
      )
      (get_size x == U.uint_to_t s /\ get_height x == U.uint_to_t h)
      m;
    Mem.emp_unit (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' p left l' `Mem.star`
      tree_sl' p right r' `Mem.star`
      Mem.pure (get_size x == U.uint_to_t s /\ get_height x == U.uint_to_t h)
      );
    Mem.pure_star_interp (pts_to_sl pt full_perm x `Mem.star`
      tree_sl' p left l' `Mem.star`
      tree_sl' p right r' `Mem.star`
      Mem.pure (get_size x == U.uint_to_t s /\ get_height x == U.uint_to_t h)
      )
      ((G.reveal p) pt)
      m;

    let s = Spec.size_of_tree l' + Spec.size_of_tree r' + 1 in
    let h = M.max (Spec.height_of_tree l') (Spec.height_of_tree r') + 1 in
    let t = Spec.Node x l' r' s h in

    assert (interp (
      pts_to_sl pt full_perm x `Mem.star`
      tree_sl' p (get_left x) l' `Mem.star`
      tree_sl' p (get_right x) r' `Mem.star`
      Mem.pure (get_size x == U.uint_to_t s /\ get_height x == U.uint_to_t h) `Mem.star`
      Mem.pure ((G.reveal p) pt)
    ) m);

    pack_tree_lemma_aux p pt x l' r' s h m;
    intro_h_exists t (tree_sl' p pt) m;
    tree_sel_interp p pt t m
#pop-options

let pack_tree #opened #a p ptr left right sr hr =
  let h0 = get () in
  let x = hide (sel ptr h0) in
  let l:wdm a = hide (v_linked_tree p left h0) in
  let r:wdm a = hide (v_linked_tree p right h0) in
  let t = Spec.Node (get_data x) l r (U.v sr) (U.v hr) in

  change_slprop
    (vptr ptr `star`
    linked_tree p left `star`
    linked_tree p right)
    (linked_tree p ptr)
    ((reveal x, reveal l), reveal r) t
    (fun m -> pack_tree_lemma p ptr left right sr hr x l r (U.v sr) (U.v hr) m)

[@@__steel_reduce__]
let tree_node' #a p r : vprop' =
  {hp = tree_sl p r;
   t = wdm (node a);
   sel = tree_sel_node p r}
unfold
let tree_node (#a:Type0) p (r:t a) = VUnit (tree_node' p r)

[@@ __steel_reduce__]
let v_node
  (#a:Type0)
  (#vp:vprop)
  (p: hpred a)
  (r:t a)
  (h:rmem vp{
    FStar.Tactics.with_tactic selector_tactic (can_be_split vp (tree_node p r) /\ True)
  })
    : GTot (wdm (node a))
  = h (tree_node p r)

val reveal_non_empty_tree (#opened:inames) (#a:Type0) (p: hpred a) (ptr:t a)
  : SteelGhost unit opened (tree_node p ptr) (fun _ -> tree_node p ptr)
             (requires fun _ -> ptr =!= null_t)
             (ensures fun h0 _ h1 -> v_node p ptr h0 == v_node p ptr h1 /\
               Spec.Node? (v_node p ptr h0))

let reveal_non_empty_lemma (#a:Type) p (ptr:t a) (t:wdm (node a)) (m:mem) : Lemma
    (requires interp (tree_sl p ptr) m /\ tree_sel_node p ptr m == t /\ ptr =!= null_t)
    (ensures Spec.Node? t)
= let l' = id_elim_exists (tree_sl' p ptr) m in
  tree_sel_interp p ptr l' m;
  pure_interp (ptr == null_t) m

let is_node (#a:Type) (t:wdm (node a)) : prop = match t with
  | Spec.Leaf -> False
  | Spec.Node _ _ _ _ _ -> True

#push-options "--compat_pre_typed_indexed_effects"
let reveal_non_empty_tree #opened #a p ptr =
  let h = get () in
  let t = hide (v_node p ptr h) in
  extract_info (tree_node p ptr) t (is_node t) (reveal_non_empty_lemma p ptr t)
#pop-options

let head (#a:Type0) (t:erased (wdm (node a)))
  : Pure (erased (node a)) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node n _ _ _ _ = reveal t in hide n

let gleft (#a:Type0) (t:erased (wdm (node a)))
  : Pure (erased (wdm (node a))) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ l _ _ _ = reveal t in hide l

let gright (#a:Type0) (t:erased (wdm (node a)))
  : Pure (erased (wdm (node a))) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ _ r _ _ = reveal t in hide r

let gsize (#a:Type0) (t:erased (wdm (node a)))
  : Pure (erased nat) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ _ _ s _ = reveal t in hide s

let gheight (#a:Type0) (t:erased (wdm (node a)))
  : Pure (erased nat) (requires Spec.Node? (reveal t)) (ensures fun _ -> True) =
  let Spec.Node _ _ _ _ h = reveal t in hide h

let unpack_tree_node_lemma (#a:Type0) (p: hpred a) (pt:t a) (t:wdm (node a)) (m:mem) : Lemma
  (requires
    Spec.Node? t /\
    interp (tree_sl p pt) m /\
    tree_sel_node p pt m == t)
  (ensures (
    let Spec.Node x l r s h = t in

    interp (ptr pt `Mem.star`
      tree_sl p (get_left x) `Mem.star`
      tree_sl p (get_right x)
    ) m /\
    sel_of (vptr pt) m == x /\
    tree_sel_node p (get_left x) m == l /\
    tree_sel_node p (get_right x) m == r /\
    U.v (get_size x) == s /\
    U.v (get_height x) == h /\
    Spec.is_wdm l /\
    Spec.is_wdm r /\
    s = Spec.size_of_tree t /\
    h = Spec.height_of_tree t /\
    s <= c /\
    h <= c /\
    (G.reveal p) pt
    )
  )
  =
    let Spec.Node x l r s h = t in
    assert (s <= c);
    assert (h <= c);
    assert (Spec.is_wds l);
    assert (Spec.is_wds r);
    assert (Spec.is_wds t);
    assert (s == Spec.size_of_tree t);
    tree_sel_interp p pt t m;

    let p1 = pts_to_sl pt full_perm x in
    let p2 = tree_sl' p (get_left x) l in
    let p3 = tree_sl' p (get_right x) r in
    let sl = p1 `Mem.star` p2 `Mem.star` p3 in
    assert (interp sl m);
    assert (interp (sl `Mem.star` Mem.pure (get_size x == U.uint_to_t s /\ (get_height x) == U.uint_to_t h))  m);

    let m12, m3 = id_elim_star
      (p1 `Mem.star` p2) p3 m in
    assert ((join m12 m3) == m);
    let m1, m2 = id_elim_star
      p1 p2 m12 in
    assert (hide (join m1 m2) == m12);

    // #1
    intro_ptr_interp pt (hide x) m1;
    ptr_sel_interp pt m1;
    pts_to_witinv pt full_perm;
    // #2
    tree_sel_interp p (get_left x) l m2;
    tree_sl'_witinv p (get_left x);
    intro_star
      (ptr pt)
      (tree_sl p (get_left x)) m1 m2;
    join_commutative m1 m2;
    assert (reveal m12 == join m1 m2);
    assert (interp (ptr pt `Mem.star` tree_sl p (get_left x)) m12);
    // #3
    tree_sel_interp p (get_right x) r m3;
    tree_sl'_witinv p (get_right x);
    intro_star
      (ptr pt `Mem.star` tree_sl p (get_left x))
      (tree_sl p (get_right x)) m12 m3;
    join_commutative m12 m3;
    assert (reveal m == join m12 m3);
    assert (interp (ptr pt `Mem.star`
      tree_sl p (get_left x) `Mem.star`
      tree_sl p (get_right x)
    ) m);

    Mem.pure_star_interp sl
      (get_size x == U.uint_to_t s /\ (get_height x) == U.uint_to_t h)
      m;
    Mem.pure_star_interp
      (sl `Mem.star` Mem.pure (get_size x == U.uint_to_t s /\ (get_height x) == U.uint_to_t h))
      ((G.reveal p) pt)
      m

let unpack_tree_node_lemma_size (#a:Type0) (p: hpred a) (pt:t a) (t:wdm (node a)) (m:mem)
  : Lemma
  (requires
    Spec.Node? t /\
    interp (tree_sl p pt) m /\
    tree_sel_node p pt m == t)
  (ensures (
    reveal (gsize t) == Spec.size_of_tree t /\
    reveal (gsize t) == U.v (get_size (head t)) /\
    reveal (gheight t) == U.v (get_height (head t)) /\
    (G.reveal p) pt
  ))
  = unpack_tree_node_lemma p pt t m

inline_for_extraction noextract
let unpack_tree_node (#a:Type0) (p: hpred a) (ptr:t a)
  : Steel (node a)
             (tree_node p ptr)
             (fun n ->
               vptr ptr `star`
               tree_node p (get_left n) `star`
               tree_node p (get_right n))
             (fun _ -> not (is_null_t ptr))
             (fun h0 n h1 ->
               Spec.Node? (v_node p ptr h0) /\
               sel ptr h1 == n /\
               v_node p ptr h0 == Spec.Node
                 (sel ptr h1)
                 (v_node p (get_left n) h1)
                 (v_node p (get_right n) h1)
                 (U.v (get_size n))
                 (U.v (get_height n)) /\
               U.v (get_size n)
               == Spec.size_of_tree (v_node p (get_left n) h1)
                + Spec.size_of_tree (v_node p (get_right n) h1) + 1 /\
               U.v (get_height n)
               == M.max (Spec.height_of_tree (v_node p (get_left n) h1))
                        (Spec.height_of_tree (v_node p (get_right n) h1)) + 1 /\
               U.v (get_size n) <= c /\
               U.v (get_height n) <= c /\
               (G.reveal p) ptr
             )
  =
  let h0 = get () in
  let t = hide (v_node p ptr h0) in
  reveal_non_empty_tree p ptr;

  let gn = head t in
  extract_info (tree_node p ptr) t
    (reveal (gsize (reveal t)) == Spec.size_of_tree (reveal t) /\
      reveal (gsize (reveal t)) == U.v (get_size (reveal gn)) /\
      reveal (gheight (reveal t)) == U.v (get_height (reveal gn)) /\
      (G.reveal p) ptr)
    (fun m -> unpack_tree_node_lemma_size p ptr t m);

  assert (reveal (gsize (reveal t)) == Spec.size_of_tree (reveal t));
  let s = hide (Spec.size_of_tree (reveal t)) in
  assert (s <= c);
  let h = hide (Spec.height_of_tree (reveal t)) in
  assert (h <= c);

  change_slprop
    (tree_node p ptr)
    (vptr ptr `star`
    tree_node p (get_left gn) `star`
    tree_node p (get_right gn))
    t
    ((reveal gn, reveal (gleft t)), reveal (gright t))
    (fun m -> unpack_tree_node_lemma p ptr t m);

  let n = read ptr in
  change_equal_slprop
    (tree_node p (get_left gn))
    (tree_node p (get_left n));
  change_equal_slprop
    (tree_node p (get_right gn))
    (tree_node p (get_right n));
  return n

#restart-solver

let unpack_tree (#a: Type0) (p: hpred a) (ptr: t a)
//    : Steel (node a)
//      (linked_tree p ptr)
//      (fun node ->
//        vptr ptr `star`
//        linked_tree p (get_left node) `star`
//        linked_tree p (get_right node))
//      (requires (fun h0 -> not (is_null_t ptr)))
//      (ensures (fun h0 node h1 ->
//        v_linked_tree p ptr h0 == Spec.Node
//          (get_data (sel ptr h1))
//          (v_linked_tree p (get_left node) h1)
//          (v_linked_tree p (get_right node) h1)
//          (U.v (get_size node))
//          (U.v (get_height node)) /\
//        (sel ptr h1) == node /\
//        U.v (get_size node)
//        == Spec.size_of_tree (v_linked_tree p (get_left node) h1)
//         + Spec.size_of_tree (v_linked_tree p (get_right node) h1) + 1 /\
//        U.v (get_size node) <= c /\
//        U.v (get_height node)
//        == M.max (Spec.height_of_tree (v_linked_tree p (get_left node) h1))
//                 (Spec.height_of_tree (v_linked_tree p (get_right node) h1)) + 1 /\
//        U.v (get_height node) <= c /\
//        (G.reveal p) ptr
//      ))
  =
  let h0 = get() in
  change_slprop_rel
    (linked_tree p ptr)
    (tree_node p ptr)
    (fun x y -> x == tree_view y)
    (fun _ -> ());
  let h1 = get () in
  assert (v_linked_tree p ptr h0 == tree_view (v_node p ptr h1));
  let n = unpack_tree_node p ptr in
  let h2 = get () in

  change_slprop_rel
    (tree_node p (get_left n))
    (linked_tree p (get_left n))
    (fun x y -> tree_view x == y)
    (fun _ -> ());
  change_slprop_rel
    (tree_node p (get_right n))
    (linked_tree p (get_right n))
    (fun x y -> tree_view x == y)
    (fun _ -> ());
  let h3 = get () in
  assert (v_linked_tree p (get_left n) h3 == tree_view (v_node p (get_left n) h2));
  assert (v_linked_tree p (get_right n) h3 == tree_view (v_node p (get_right n) h2));
  tree_view_aux_same_size (v_node p (get_left n) h2);
  tree_view_aux_same_size (v_node p (get_right n) h2);
  tree_view_aux_same_height (v_node p (get_left n) h2);
  tree_view_aux_same_height (v_node p (get_right n) h2);
  extract_pred p (get_left n);
  extract_pred p (get_right n);
  return n
