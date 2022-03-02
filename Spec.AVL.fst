module Spec.AVL

module M = FStar.Math.Lib

open FStar.Ghost
open Spec.Trees
open Spec.BST

(**** AVL insertion *)

//@AVL
//complexity: O(n), where n is the size of the tree
//not for effective use
let rec is_balanced_g (#a: Type) (x: tree a)
  : GTot bool
  = match x with
  | Leaf -> true
  | Node data left right _ _ ->
    M.abs(height_of_tree right - height_of_tree left) <= 1 &&
    is_balanced_g right &&
    is_balanced_g left

let is_balanced (#a: Type) (t: wdm a)
  : bool
  = match t with
  | Leaf -> true
  | Node _ left right _ _ ->
      let lh = hot_wdh left in
      let rh = hot_wdh right in
      (lh - rh <= 1) && (rh - lh <= 1)

let is_balanced_spec_lemma (#a: Type) (t: wdm a)
  : Lemma
  (requires
    Node? t /\
    is_balanced_g (cleft t) /\
    is_balanced_g (cright t) /\
    is_balanced t)
  (ensures
    is_balanced_g t
  )
  = ()

//@AVL
let is_avl (#a: Type) (cmp:cmp a) (x: tree a) : GTot bool =
  is_bst cmp x && is_balanced_g x

//@AVL
let avl (a: Type) (cmp:cmp a) = x: wdm a {is_avl cmp x}
(** Balancing operation for AVLs *)


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

let rebalance_avl_wdm (#a: Type) (t: wdm a) : wdm a =
  if Leaf? t then t else
  let Node data left right size height = t in
  if hot_wdh left - hot_wdh right > 1 then (
    let Node ldata lleft lright lsize lheight = left in
    if hot_wdh lleft >= hot_wdh lright then (
      let r = rotate_right t in
      assert (Some? r);
      opt_get r
    ) else (
      let r = rotate_left_right t in
      assert (Some? r);
      opt_get r
    )
  ) else if hot_wdh right - hot_wdh left > 1 then (
    let Node rdata rleft rright rsize lright = right in
    if hot_wdh rleft > hot_wdh rright then (
      let r = rotate_right_left t in
      assert (Some? r);
      opt_get r
    ) else (
      let r = rotate_left t in
      assert (Some? r);
      opt_get r
    )
  ) else (
    t
  )

let rebalance_avl_wds_size (#a: Type) (t: wdm a)
  : Lemma (size_of_tree (rebalance_avl_wdm t) == size_of_tree t)
  = ()

//#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
#push-options "--z3rlimit 100"
let rebalance_avl_wds_proof (#a: Type) (cmp: cmp a) (t: wdm a)
  (root: a)
  : Lemma
  (requires is_bst cmp t /\ (
    match t with
    | Leaf -> True
    | Node data left right _ _ ->
        is_balanced left /\
        is_balanced right /\
        hot_wdh left - hot_wdh right <= 2 /\
        hot_wdh right - hot_wdh left <= 2
  ))
  (ensures
    is_avl cmp (rebalance_avl_wdm t)
    /\
    (forall_keys t (key_left cmp root)
      ==> forall_keys (rebalance_avl_wdm t) (key_left cmp root)) /\
    (forall_keys t (key_right cmp root)
      ==> forall_keys (rebalance_avl_wdm t) (key_right cmp root))
  )
  =
  admit ();
  if Leaf? t then () else
  let Node _ left right _ _ = t in
  if hot_wdh left - hot_wdh right > 1 then (
    assert (hot_wdh left - hot_wdh right == 2);
    let Node _ lleft lright _ _ = left in
    if hot_wdh lleft >= hot_wdh lright then (
      let r = rotate_right t in
      assert (Some? r);
      let t' = opt_get r in
      rotate_right_bst cmp t;
      //Classical.move_requires (rotate_right_key_left cmp t) root;
      //Classical.move_requires (rotate_right_key_right cmp t) root;
      assert (is_avl cmp t')
    ) else (
      let r = rotate_left_right t in
      assert (Some? r);
      let t' = opt_get r in
      rotate_left_right_bst cmp t;
      //Classical.move_requires (rotate_left_right_key_left cmp t) root;
      //Classical.move_requires (rotate_left_right_key_right cmp t) root;
      assert (is_avl cmp t')
    )
  ) else if hot_wdh right - hot_wdh left > 1 then (
    assert (hot_wdh right - hot_wdh left == 2);
    let Node _ rleft rright _ _ = right in
    assert (is_balanced right);
    if hot_wdh rright >= hot_wdh rleft then (
      let r = rotate_left t in
      assert (Some? r);
      let t' = opt_get r in
      rotate_left_bst cmp t;
      //Classical.move_requires (rotate_left_key_left cmp t) root;
      //Classical.move_requires (rotate_left_key_right cmp t) root;
      assert (is_avl cmp t')
    ) else (
      let r = rotate_right_left t in
      assert (Some? r);
      let t' = opt_get r in
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

//@D, change key_{left, right} types
//let key_left2 (#a: Type) (cmp:cmp a) (root: a) : cond a cmp
//  = key_left cmp root
//let key_right2 (#a: Type) (cmp:cmp a) (root: a) : cond a cmp
//  = key_right cmp root

//previous lemmas: @BST

let rebalance_preserves_bst (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (is_bst cmp t = is_bst cmp (rebalance_avl_wdm t))
  = admit ()

//@AVL
let rebalance_equal (#a: Type) (cmp: cmp a) (t: bst a cmp)
  : Lemma
  (let new_t = rebalance_avl_wdm t in
  rebalance_preserves_bst cmp t;
  //(requires is_bst cmp (rebalance_avl_wdm t))
  equal cmp t (rebalance_avl_wdm t))
  =
  if Leaf? t then () else
  let Node data left right size height = t in
  if hot_wdh left - hot_wdh right > 1 then (
    let Node ldata lleft lright lsize lheight = left in
    if hot_wdh lleft >= hot_wdh lright then (
      let r = rotate_right t in
      assert (Some? r);
      rotate_right_equal cmp t
    ) else (
      let r = rotate_left_right t in
      assert (Some? r);
      rotate_left_right_equal cmp t
    )
  ) else if hot_wdh right - hot_wdh left > 1 then (
    let Node rdata rleft rright rsize lright = right in
    if hot_wdh rleft > hot_wdh rright then (
      let r = rotate_right_left t in
      assert (Some? r);
      rotate_right_left_equal cmp t
    ) else (
      let r = rotate_left t in
      assert (Some? r);
      rotate_left_equal cmp t
    )
  ) else (
    ()
  )

(*
- r: in case of equality with an already existing element,
  true = replace, false = do not replace
- snd (result): whether a new element has been added,
  that is whether the size has increased
  => bad idea/bad design?
*)


#push-options "--z3rlimit 25"
let rec insert_avl_aux (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Pure (wdm a & erased bool)
  True
  (fun (new_t, b) ->
    size_of_tree new_t = size_of_tree t + (int_of_bool b)
  )
  =
  match t with
  | Leaf -> Node new_data Leaf Leaf 1 1, hide true
  | Node data left right size height ->
    let delta = cmp new_data data in
    if delta = 0 then begin
      if r then Node new_data left right size height, hide false
           else t, hide false
    end
    else if delta < 0 then begin
      let new_left, b = insert_avl_aux r cmp left new_data in
      let new_t = merge_tree data new_left right in
      assert (is_wdm new_t);
      let new_t2 = rebalance_avl_wdm new_t in
      rebalance_avl_wds_size new_t;
      new_t2, b
    end else begin
      let new_right, b = insert_avl_aux r cmp right new_data in
      let new_t = merge_tree data left new_right in
      assert (is_wdm new_t);
      let new_t2 = rebalance_avl_wdm new_t in
      rebalance_avl_wds_size new_t;
      new_t2, b
    end

let rec skel_of_tree (#a: Type) (t: wdm a)
  : Pure (wdm nat)
  True
  (fun new_t ->
    size_of_tree new_t = size_of_tree t /\
    height_of_tree new_t = height_of_tree t
  )
  = match t with
  | Leaf -> Leaf
  | Node _ left right size height ->
      let new_left = skel_of_tree left in
      let new_right = skel_of_tree right in
      Node 0 new_left new_right size height

let rec skel_balanced (#a: Type) (t: wdm a)
  : Lemma (
  is_balanced t = is_balanced (skel_of_tree t)
  )
  = match t with
  | Leaf -> ()
  | Node _ left right size height ->
      skel_balanced left;
      skel_balanced right

let rec insert_in_place_preserves_skel (#a: Type)
  (r: bool) (cmp: cmp a) (t: avl a cmp) (new_data: a)
  : Lemma (
  let new_t, b = insert_avl_aux r cmp t new_data in
  not b <==> skel_of_tree new_t = skel_of_tree t
  )
  = match t with
  | Leaf -> ()
  | Node data left right size height ->
    let delta = cmp data new_data in
    if delta = 0 then ()
    else if delta > 0 then
      insert_in_place_preserves_skel r cmp left new_data
    else
      insert_in_place_preserves_skel r cmp right new_data

let rebalance_balanced_id (#a: Type) (cmp: cmp a) (t: bst a cmp)
  : Lemma
  (requires is_balanced t)
  (ensures rebalance_avl_wdm t == t)
  = ()

let rebalance_height (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (height_of_tree (rebalance_avl_wdm t) <= height_of_tree t)
  = admit ()

let rec insert_avl_aux_bst (#a: Type)
  (r: bool) (cmp: cmp a) (t: avl a cmp) (new_data: a)
  : Lemma (
    let new_t, b = insert_avl_aux r cmp t new_data in
    // 1
    is_bst cmp new_t /\
    // 2
    mem cmp new_t new_data = true /\
    (reveal b ==> add cmp t new_t new_data) /\
    (not (reveal b) ==> equal cmp t new_t)
  )
   =
  match t with
  | Leaf -> ()
  | Node data left right size height ->
      let rnew_t, rb = insert_avl_aux r cmp t new_data in
      let delta = cmp new_data data in
      if delta = 0 then begin
        if r then
          let new_t = Node new_data left right size height in
          forall_keys_trans left
            (key_left cmp data)
            (key_left cmp new_data);
          forall_keys_trans right
            (key_right cmp data)
            (key_right cmp new_data)
        else ()
      end else if delta < 0 then begin
        let new_left, b = insert_avl_aux r cmp left new_data in
        let size_new_left = size_of_tree new_left in
        let size_right = size_of_tree right in
        let new_size = size_new_left + size_right + 1 in
        let height_new_left = hot_wdh new_left in
        let height_right = hot_wdh right in
        let new_height = M.max height_new_left height_right + 1 in
        let new_t = Node data new_left right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);
        // 2
        insert_avl_aux_bst r cmp left new_data;
        assert (is_bst cmp new_left);
        if reveal b then begin
          assert (add cmp left new_left new_data);
          add_preserves_cond cmp left new_left new_data
            (key_left cmp data);
          assert (forall_keys new_left (key_left cmp data))
        end else begin
          assert (equal cmp left new_left);
          subset_preserves_cond cmp new_left left
            (key_left cmp data)
        end;
        assert (is_bst cmp new_t);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t2);
        // 3
        assert (
          (reveal b ==> add cmp t new_t new_data) /\
          (not (reveal b) ==> equal cmp t new_t));
        rebalance_equal cmp new_t;
        assert (
          (reveal b ==> add cmp t new_t2 new_data) /\
          (not (reveal b) ==> equal cmp t new_t2));
        ()
      end else begin
        let new_right, b = insert_avl_aux r cmp right new_data in
        let size_left = size_of_tree left in
        let size_new_right = size_of_tree new_right in
        let new_size = size_left + size_new_right + 1 in
        let height_left = hot_wdh left in
        let height_new_right = hot_wdh new_right in
        let new_height = M.max height_left height_new_right + 1 in
        let new_t = Node data left new_right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);
        // 2
        insert_avl_aux_bst r cmp right new_data;
        assert (is_bst cmp new_right);
        if reveal b then begin
          assert (add cmp right new_right new_data);
          add_preserves_cond cmp right new_right new_data
            (key_right cmp data);
          assert (forall_keys new_right (key_right cmp data))
        end else begin
          assert (equal cmp right new_right);
          subset_preserves_cond cmp new_right right
            (key_right cmp data)
        end;
        assert (is_bst cmp new_t);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t2);
        // 3
        assert (
          (reveal b ==> add cmp t new_t new_data) /\
          (not (reveal b) ==> equal cmp t new_t));
        rebalance_equal cmp new_t;
        assert (
          (reveal b ==> add cmp t new_t2 new_data) /\
          (not (reveal b) ==> equal cmp t new_t2));
        ()
      end

let rotate1_involutive (#a: Type) (t: wdm a)
  : Lemma
  (requires
    Some? (rotate_left t))
  (ensures
    opt_get (rotate_right (opt_get (rotate_left t))) == t)
  = ()

let rotate2_involutive (#a: Type) (t: wdm a)
  : Lemma
  (requires
    Some? (rotate_right t))
  (ensures
    opt_get (rotate_left (opt_get (rotate_right t))) == t)
  = ()

// TODO: to be shortened using merge_tree
let rotate_left_right_decomposition (#a: Type) (t: wdm a)
  : Pure (wdm a)
  (Some? (rotate_left_right t))
  (fun _ -> True)
  =
  let new_left = rotate_left (cleft t) in
  assert (Some? new_left);
  let new_left = opt_get new_left in
  let height_new_left = hot_wdh new_left in
  let height_right = hot_wdh (cright t) in
  let new_height = M.max height_new_left height_right + 1 in
  let new_t = Node (cdata t) new_left (cright t) (csize t) new_height in
  rotate_left_size (cleft t);
  let new_t2 = rotate_right new_t in
  assert (Some? new_t2);
  let new_t2 = opt_get new_t2 in
  assert (new_t2 == opt_get (rotate_left_right t));
  t

// TODO: to be shortened using merge_tree
let rotate_right_left_decomposition (#a: Type) (t: wdm a)
  : Pure (wdm a)
  (Some? (rotate_right_left t))
  (fun _ -> True)
  =
  let new_right = rotate_right (cright t) in
  assert (Some? new_right);
  let new_right = opt_get new_right in
  let height_left = hot_wdh (cleft t) in
  let height_new_right = hot_wdh new_right in
  let new_height = M.max height_left height_new_right + 1 in
  let new_t = Node (cdata t) (cleft t) new_right (csize t) new_height in
  rotate_right_size (cright t);
  let new_t2 = rotate_left new_t in
  assert (Some? new_t2);
  let new_t2 = opt_get new_t2 in
  assert (new_t2 == opt_get (rotate_right_left t));
  t

#push-options "--z3rlimit 50"
let rec insert_avl_aux_avl (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Lemma (
    let new_t, b = insert_avl_aux r cmp t new_data in
    // 1 height inequalities
    height_of_tree t <= height_of_tree new_t /\
    height_of_tree new_t <= height_of_tree t + 1 /\
    // 2 balanced
    is_avl cmp new_t
  )
  =
  match t with
  | Leaf -> ()
  | Node data left right size height ->
      let rnew_t, rb = insert_avl_aux r cmp t new_data in
      insert_avl_aux_bst r cmp t new_data;
      assert (is_bst cmp rnew_t);
      let delta = cmp new_data data in
      if delta = 0 then begin
        // 1
        assert (reveal rb = false);
        insert_in_place_preserves_skel r cmp t new_data;
        assert (skel_of_tree rnew_t = skel_of_tree t);
        assert (hot_wdh rnew_t = hot_wdh t);
        // 2
        assert (is_balanced (skel_of_tree rnew_t)
              = is_balanced (skel_of_tree t));
        skel_balanced t;
        assert (is_balanced (skel_of_tree rnew_t));
        skel_balanced rnew_t;
        assert (is_balanced rnew_t);
        assert (is_avl cmp rnew_t)
      end else if delta < 0 then begin
        let new_left, b = insert_avl_aux r cmp left new_data in
        let size_new_left = size_of_tree new_left in
        let size_right = size_of_tree right in
        let new_size = size_new_left + size_right + 1 in
        let height_new_left = hot_wdh new_left in
        let height_right = hot_wdh right in
        let new_height = M.max height_new_left height_right + 1 in
        let new_t = Node data new_left right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);
        //assert (is_wdm t);
        // 2
        insert_avl_aux_bst r cmp t new_data;
        assert (is_bst cmp new_t2);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t);
        insert_avl_aux_avl r cmp left new_data;
        assert (is_avl cmp new_left);
        assert (is_avl cmp right);
        // TODO: new_left/right
        assert (hot_wdh t <= hot_wdh new_t);
        assert (hot_wdh new_t <= hot_wdh t + 1);
        rebalance_avl_wds_proof cmp new_t data;
        assert (is_avl cmp new_t2);
        // 1
        if not (reveal b) then begin
          insert_in_place_preserves_skel r cmp t new_data;
          assert (skel_of_tree rnew_t = skel_of_tree t);
          assert (height_of_tree rnew_t = height_of_tree t);
          assert (height_of_tree new_t2 = height_of_tree t)
        end else begin
          assert (hot_wdh t <= hot_wdh new_t);
          assert (hot_wdh new_t <= hot_wdh t + 1);
          rebalance_height cmp new_t;
          assert (hot_wdh t <= hot_wdh new_t2);
          assert (hot_wdh new_t2 <= hot_wdh t + 1)
        end;
        assert (hot_wdh t <= hot_wdh new_t2);
        assert (hot_wdh new_t2 <= hot_wdh t + 1);
        ()
      end else begin
        let new_right, b = insert_avl_aux r cmp right new_data in
        let size_left = size_of_tree left in
        let size_new_right = size_of_tree new_right in
        let new_size = size_left + size_new_right + 1 in
        let height_left = hot_wdh left in
        let height_new_right = hot_wdh new_right in
        let new_height = M.max height_left height_new_right + 1 in
        let new_t = Node data left new_right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);
        //assert (is_wdm t);
        // 2
        insert_avl_aux_bst r cmp t new_data;
        assert (is_bst cmp new_t2);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t);
        insert_avl_aux_avl r cmp right new_data;
        assert (is_avl cmp left);
        assert (is_avl cmp new_right);
        // TODO: left/new_right
        assert (hot_wdh t <= hot_wdh new_t);
        assert (hot_wdh new_t <= hot_wdh t + 1);
        rebalance_avl_wds_proof cmp new_t data;
        assert (is_avl cmp new_t2);
        // 1
        if not (reveal b) then begin
          insert_in_place_preserves_skel r cmp t new_data;
          assert (skel_of_tree rnew_t = skel_of_tree t);
          assert (height_of_tree rnew_t = height_of_tree t);
          assert (height_of_tree new_t2 = height_of_tree t)
        end else begin
          assert (hot_wdh t <= hot_wdh new_t);
          assert (hot_wdh new_t <= hot_wdh t + 1);
          rebalance_height cmp new_t;
          assert (hot_wdh t <= hot_wdh new_t2);
          assert (hot_wdh new_t2 <= hot_wdh t + 1)
        end;
        assert (hot_wdh t <= hot_wdh new_t2);
        assert (hot_wdh new_t2 <= hot_wdh t + 1);
        ()
      end
#pop-options

let insert_avl (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Pure (avl a cmp)
  True
  (fun t' ->
    let _,b = insert_avl_aux r cmp t new_data in
    let b = reveal b in
    size_of_tree t' = size_of_tree t + (int_of_bool b) /\
    height_of_tree t' <= height_of_tree t + 1 /\
    height_of_tree t <= height_of_tree t' /\
    b ==> add cmp t t' new_data /\
    (not b) ==> equal cmp t t'
  )
  =
  insert_avl_aux_bst r cmp t new_data;
  insert_avl_aux_avl r cmp t new_data;
  fst (insert_avl_aux r cmp t new_data)

let insert_lemma (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Lemma
  (let t' = insert_avl r cmp t new_data in
    size_of_tree t <= size_of_tree t' /\
    size_of_tree t' <= size_of_tree t + 1 /\
    height_of_tree t' <= height_of_tree t + 1 /\
    height_of_tree t <= height_of_tree t'
  )
  = insert_avl_aux_avl r cmp t new_data


#push-options "--z3rlimit 50"
let rec remove_leftmost_avl (#a: Type0)
  (cmp:cmp a)
  (t: avl a cmp{Node? t})
  : Pure (avl a cmp & a)
  True
  (fun (t', leftmost) ->
    //1 returned element was part of the tree
    mem cmp t leftmost = true /\
    //2 returned element smaller than all elements of the new tree
    forall_keys t' (key_right cmp leftmost) /\
    //3 returned element has been removed
    mem cmp t' leftmost = false /\
    //4 rest of the tree preserved
    add cmp t' t leftmost /\
    //6 size decreased by 1
    size_of_tree t' = size_of_tree t - 1 /\
    //7
    height_of_tree t - 1 <= height_of_tree t' /\
    height_of_tree t' <= height_of_tree t
  )
    //(forall x. cmp x (snd r) <> 0
    //  ==> mem cmp t x = mem cmp (fst r) x) /\
    //5 subset
    //subset cmp (fst r) t /\
    //Node? (fst r) ==> is_balanced (cleft (fst r)) /\
    //Node? (fst r) ==> is_balanced (cright (fst r)) /\
  =
  match t with
  | Node data Leaf right size _ ->
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
  | Node data left right size _ ->
      let new_left, leftmost = remove_leftmost_avl cmp left in
      // (1 : IH)
      assert (mem cmp left leftmost = true);
      assert (mem cmp t leftmost = true);
      // (2 : IH)
      let height_new_left = hot_wdh new_left in
      let height_right = hot_wdh right in
      let new_height = M.max height_new_left height_right + 1 in
      let new_t = merge_tree data new_left right in
      assert (sot_wds new_t = size - 1);
      assert (hot_wdh new_t = new_height);
      //let new_t = Node data new_left right (size - 1) new_height in
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
      let new_t2 = rebalance_avl_wdm new_t in
      assert (is_balanced new_left);
      assert (is_balanced right);
      assert (height_of_tree left - 1 <= height_of_tree new_left);
      assert (height_of_tree new_left <= height_of_tree left);
      assert (height_of_tree right - height_of_tree new_left <= 2);
      assert (height_of_tree new_left - height_of_tree right <= 1);
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
      assert (height_of_tree new_t2 <= height_of_tree t);
      assert (height_of_tree t - 1 <= height_of_tree new_t2);
      assert (is_avl cmp new_t2);
      new_t2, leftmost
#pop-options

// https://en.wikipedia.org/wiki/Binary_search_tree#Deletion
#push-options "--z3rlimit 100"
let delete_avl_aux0 (#a: Type0)
  (cmp:cmp a)
  (t: avl a cmp)
  (data_to_rm: a)
  : Pure (avl a cmp)
  (Node? t /\ cmp (cdata t) data_to_rm = 0)
  (fun t' ->
    // 1 a b removal of one element
    mem cmp t data_to_rm = true /\
    mem cmp t' data_to_rm = false /\
    // 2 remaining tree unchanged
    add cmp t' t data_to_rm /\
    // 3 size decreased by one
    size_of_tree t' = size_of_tree t - 1 /\
    // 4 height inequalities
    height_of_tree t - 1 <= height_of_tree t' /\
    height_of_tree t' <= height_of_tree t
  )
  =
  match t with
  //| Node data Leaf Leaf 1 _ -> Leaf
  | Node data left Leaf size _ ->
      assert (forall_keys left (key_left cmp data));
      equiv cmp left (key_left cmp data);
      //greater_not_mem cmp left data;
      assert (mem cmp left data = false);
      assert (is_avl cmp t);
      assert (is_avl cmp left);
      left
  | Node data Leaf right size _ ->
      assert (forall_keys right (key_right cmp data));
      equiv cmp right (key_right cmp data);
      //smaller_not_mem cmp right data;
      assert (mem cmp right data = false);
      assert (is_avl cmp t);
      assert (is_avl cmp right);
      right
  // successor of z = to be retrieved
  | Node z l r sz hz ->
      assert (Node? r);
      // 1a
      assert (mem cmp t data_to_rm = true);
      // call to aux function, building new tree
      let new_right, succ_z = remove_leftmost_avl cmp r in
      let height_new_right = hot_wdh new_right in
      let height_left = hot_wdh l in
      let new_height = M.max height_left height_new_right + 1 in
      //let new_t = Node succ_z l new_right (sz - 1) new_height in
      let new_t = merge_tree succ_z l new_right in
      assert (sot_wds new_t = sz - 1);
      assert (hot_wdh new_t = new_height);
      let new_t2 = rebalance_avl_wdm new_t in
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
      // new_t2
      // 1 a b
      rebalance_preserves_bst cmp new_t;
      rebalance_equal cmp new_t;
      assert (mem cmp t data_to_rm = true);
      assert (mem cmp new_t2 data_to_rm = false);
      // 2
      assert (add cmp new_t2 t data_to_rm);
      // 3
      rebalance_avl_wds_size new_t;
      assert (size_of_tree new_t2 = size_of_tree t - 1);
      // 4: seemingly ok
      // avl
      assert (is_avl cmp l);
      assert (is_avl cmp new_right);
      assert (height_of_tree l - height_of_tree new_right <= 2);
      assert (height_of_tree new_right - height_of_tree l <= 2);
      rebalance_avl_wds_proof cmp new_t succ_z;
      assert (is_avl cmp new_t2);
      new_t2
#pop-options

//#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
//let delete_avl_aux1 (#a: Type0)
//  (cmp:cmp a)
//  (t: avl a cmp{Node? t})
//  (data_to_rm: a{cmp (cdata t) data_to_rm = 0})
//  //(t: avl a cmp{Node? t /\ cmp (cdata t) data_to_rm = 0})
//  : Pure (avl a cmp)
//  True
//  (fun r ->
//    // 1 a b removal of one element
//    mem cmp t data_to_rm = true /\
//    mem cmp r data_to_rm = false /\
//    // 2 remaining tree unchanged
//    add cmp r t data_to_rm /\
//    // 3 size decreased by one
//    size_of_tree r = size_of_tree t - 1 /\
//    // 4 height inequalities
//    height_of_tree t - 1 <= height_of_tree r /\
//    height_of_tree r <= height_of_tree t
//  )
//  =
//  let new_t1 = delete_avl_aux0 #a cmp t data_to_rm in
//  match t with
//  | Node data Leaf Leaf 1 _ ->
//      let new_t0 = Leaf
//      in assert (new_t0 == new_t1);
//      new_t0
//  | Node data left Leaf size _ ->
//      let new_t0 = left
//      in assert (new_t0 == new_t1);
//      new_t0
//  | Node data Leaf right size _ ->
//      let new_t0 = right
//      in assert (new_t0 == new_t1);
//      new_t0
//
// // | _ ->
////  let new_t0 = begin match t with
////  | Node z l (Node y Leaf x _ hr) sz _ ->
////      let new_height = M.max (hot_wdh l) (hr - 1) + 1 in
////      let new_t0 = Node y l x (sz - 1) new_height in
////      assert (is_balanced t);
////      assert (is_balanced (cright t));
////      assert (is_balanced (cright (cright t)));
////      assert (is_balanced (cleft new_t0));
////      assert (is_balanced (cright new_t0));
////      new_t0
//  | Node z l r sz _ ->
//      let new_right, succ_z = remove_leftmost_avl cmp r in
//      let height_left = hot_wdh l in
//      let height_new_right = hot_wdh new_right in
//      let new_height = M.max height_left height_new_right + 1 in
//      let new_t0 = Node succ_z l new_right (sz - 1) new_height in
//      assert (is_balanced (cleft new_t0));
//      assert (is_balanced (cright new_t0));
//    //  new_t0
//  //end
//  //in
//  assert (new_t0 == new_t1);
//  assert (is_balanced (cleft new_t0));
//  assert (is_balanced (cright new_t0));
//  assert (height_of_tree (cleft new_t0)
//  - height_of_tree (cright new_t0) <= 2);
//  assert (height_of_tree (cright new_t0)
//  - height_of_tree (cleft new_t0) <= 2);
//  let new_t2 = rebalance_avl_wdm new_t0 in
//  assert (is_bst cmp new_t0);
//  rebalance_avl_wds_proof cmp new_t0 (cdata new_t0);
//  assert (is_avl cmp new_t2);
//  // 1a
//  assert (mem cmp t data_to_rm = true);
//  // 1b
//  assert (mem cmp new_t0 data_to_rm = false);
//  rebalance_equal cmp new_t0;
//  assert (mem cmp new_t2 data_to_rm = false);
//  // 2
//  assert (add cmp new_t2 t data_to_rm);
//  // 3
//  rebalance_avl_wds_size new_t0;
//  assert (size_of_tree new_t2 = size_of_tree new_t0);
//  // 4
//  assert (height_of_tree t - 1 <= height_of_tree new_t0);
//  assert (height_of_tree new_t0 <= height_of_tree t);
//  assert (height_of_tree t - 1 <= height_of_tree new_t2);
//  assert (height_of_tree new_t2 <= height_of_tree t);
//
//  new_t2
//#pop-options

//let rec delete_avl_aux (#a: Type0)
//  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
//  : wdm a & bool
//  =
//  match t with
//  | Leaf -> Leaf, false
//  | Node data left right size height ->
//      let delta = cmp data_to_rm data in
//      if delta < 0 then begin
//        let new_left, b = delete_avl_aux cmp left data_to_rm in
//        let new_size = size - (int_of_bool b) in
//        let height_new_left = height_of_tree new_left in
//        let height_right = height_of_tree right in
//        let new_height = M.max height_new_left height_right + 1 in
//        let new_t = Node data new_left right new_size new_height in
//        let new_t2 = rebalance_avl_wdm new_t in
//        new_t2, b
//      end else if delta > 0 then begin
//        let new_right, b = delete_avl_aux cmp right data_to_rm in
//        let new_size = size - (int_of_bool b) in
//        let height_left = hot_wdh left in
//        let height_new_right = hot_wdh new_right in
//        let new_height = M.max height_left height_new_right + 1 in
//        let new_t = Node data left new_right new_size new_height in
//        let new_t2 = rebalance_avl_wdm new_t in
//        new_t2, b
//     end else begin
//        let new_t = delete_avl_aux1 cmp t data_to_rm in
//        new_t, true
//     end

//#push-options "--z3rlimit 25"
let rec delete_avl_aux (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : Pure (wdm a & erased bool)
  True
  (fun (new_t, b) ->
    size_of_tree new_t = size_of_tree t - (int_of_bool b)
  )
  =
  match t with
  | Leaf -> Leaf, hide false
  | Node data left right size height ->
      let delta = cmp data_to_rm data in
      if delta = 0 then begin
        let new_t = delete_avl_aux0 cmp t data_to_rm in
        new_t, hide true
      end else if delta < 0 then begin
        let new_left, b = delete_avl_aux cmp left data_to_rm in
        let new_t = merge_tree data new_left right in
        assert (is_wdm new_t);
        let new_t2 = rebalance_avl_wdm new_t in
        rebalance_avl_wds_size new_t;
        new_t2, b
      end else begin
        let new_right, b = delete_avl_aux cmp right data_to_rm in
        let new_t = merge_tree data left new_right in
        assert (is_wdm new_t);
        let new_t2 = rebalance_avl_wdm new_t in
        rebalance_avl_wds_size new_t;
        new_t2, b
      end

let rec delete_avl_aux_bst (#a: Type0)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : Lemma (
    let new_t, b = delete_avl_aux cmp t data_to_rm in
    // 1
    is_bst cmp new_t /\
    // 2
    mem cmp new_t data_to_rm = false /\
    // 3
    (reveal b ==> add cmp new_t t data_to_rm) /\
    (not (reveal b) ==> equal cmp new_t t)
    //subset cmp new_t t
  )
  =
  match t with
  | Leaf -> ()
  | Node data left right size height ->
      let rnew_t, rb = delete_avl_aux cmp t data_to_rm in
      let delta = cmp data_to_rm data in
      if delta = 0 then begin
        ()
      end else if delta < 0 then begin
        let new_left, b = delete_avl_aux cmp left data_to_rm in
        let size_new_left = size_of_tree new_left in
        let size_right = size_of_tree right in
        let new_size = size_new_left + size_right + 1 in
        let height_new_left = hot_wdh new_left in
        let height_right = hot_wdh right in
        let new_height = M.max height_new_left height_right + 1 in
        let new_t = Node data new_left right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);

        delete_avl_aux_bst cmp left data_to_rm;
        assert (is_bst cmp new_left);
        assert (forall_keys left (key_left cmp data));
        assert (subset cmp new_left left);
        subset_preserves_cond cmp new_left left (key_left cmp data);
        assert (forall_keys new_left (key_left cmp data));
        assert (forall_keys right (key_right cmp data));
        assert (is_bst cmp new_t);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t2);

        assert (mem cmp new_left data_to_rm = false);
        forall_keys_trans right
          (key_right cmp data)
          (key_right cmp data_to_rm);
        smaller_not_mem cmp right data_to_rm;
        assert (mem cmp new_t data_to_rm = false);
        rebalance_equal cmp new_t;
        assert (mem cmp new_t2 data_to_rm = false);
        assert (
         (reveal b ==> add cmp new_t t data_to_rm) /\
         (not (reveal b) ==> equal cmp new_t t));
        assert (
         (reveal b ==> add cmp new_t2 t data_to_rm) /\
         (not (reveal b) ==> equal cmp new_t2 t));
        ()

      end else begin
        let new_right, b = delete_avl_aux cmp right data_to_rm in
        let size_left = size_of_tree left in
        let size_new_right = size_of_tree new_right in
        let new_size = size_left + size_new_right + 1 in
        let height_left = hot_wdh left in
        let height_new_right = hot_wdh new_right in
        let new_height = M.max height_left height_new_right + 1 in
        let new_t = Node data left new_right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);

        delete_avl_aux_bst cmp right data_to_rm;
        assert (is_bst cmp new_right);
        assert (forall_keys right (key_right cmp data));
        assert (subset cmp new_right right);
        subset_preserves_cond cmp new_right right
          (key_right cmp data);
        assert (forall_keys new_right (key_right cmp data));
        assert (forall_keys left (key_left cmp data));
        assert (is_bst cmp new_t);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t2);

        assert (mem cmp new_right data_to_rm = false);
        forall_keys_trans left
          (key_left cmp data)
          (key_left cmp data_to_rm);
        greater_not_mem cmp left data_to_rm;
        assert (mem cmp new_t data_to_rm = false);
        rebalance_equal cmp new_t;
        assert (mem cmp new_t2 data_to_rm = false);
        assert (
         (reveal b ==> add cmp new_t t data_to_rm) /\
         (not (reveal b) ==> equal cmp new_t t));
        assert (
         (reveal b ==> add cmp new_t2 t data_to_rm) /\
         (not (reveal b) ==> equal cmp new_t2 t));
        ()
      end

#push-options "--z3rlimit 50"
let rec delete_avl_aux_avl (#a: Type0)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : Lemma (
    let new_t, b = delete_avl_aux cmp t data_to_rm in
    // 1 height inequalities
    hot_wdh t - 1 <= hot_wdh new_t /\
    hot_wdh new_t <= hot_wdh t /\
    // 2 balanced
    is_avl cmp new_t
  )
  =
  match t with
  | Leaf -> ()
  | Node data left right size height ->
      let rnew_t, rb = delete_avl_aux cmp t data_to_rm in
      let delta = cmp data_to_rm data in
      if delta = 0 then begin
        ()
      end else if delta < 0 then begin
        let new_left, b = delete_avl_aux cmp left data_to_rm in
        let size_new_left = size_of_tree new_left in
        let size_right = size_of_tree right in
        let new_size = size_new_left + size_right + 1 in
        let height_new_left = hot_wdh new_left in
        let height_right = hot_wdh right in
        let new_height = M.max height_new_left height_right + 1 in
        let new_t = Node data new_left right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);

        delete_avl_aux_bst cmp t data_to_rm;
        assert (is_bst cmp new_t2);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t);
        delete_avl_aux_avl cmp left data_to_rm;
        assert (is_avl cmp new_left);
        assert (is_avl cmp right);
        assert (hot_wdh new_left - hot_wdh right <= 2);
        assert (hot_wdh right - hot_wdh new_left <= 2);
        rebalance_avl_wds_proof cmp new_t data;
        assert (is_avl cmp new_t2);

        ()

      end else begin
        let new_right, b = delete_avl_aux cmp right data_to_rm in
        let size_left = size_of_tree left in
        let size_new_right = size_of_tree new_right in
        let new_size = size_left + size_new_right + 1 in
        let height_left = hot_wdh left in
        let height_new_right = hot_wdh new_right in
        let new_height = M.max height_left height_new_right + 1 in
        let new_t = Node data left new_right new_size new_height in
        let new_t2 = rebalance_avl_wdm new_t in
        assert (new_t2 == rnew_t);
        assert (rb == b);

        delete_avl_aux_bst cmp t data_to_rm;
        assert (is_bst cmp new_t2);
        rebalance_preserves_bst cmp new_t;
        assert (is_bst cmp new_t);
        delete_avl_aux_avl cmp right data_to_rm;
        assert (is_avl cmp new_right);
        assert (is_avl cmp left);
        assert (hot_wdh new_right - hot_wdh left <= 2);
        assert (hot_wdh left - hot_wdh new_right <= 2);
        rebalance_avl_wds_proof cmp new_t data;
        assert (is_avl cmp new_t2);
        ()
      end
#pop-options

let delete_avl (#a: Type0)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : Pure (avl a cmp)
  True
  (fun t' ->
    let _, b = delete_avl_aux cmp t data_to_rm in
    let b = reveal b in
    size_of_tree t' = size_of_tree t - (int_of_bool b) /\
    height_of_tree t - 1 <= height_of_tree t' /\
    height_of_tree t' <= height_of_tree t /\
    b ==> add cmp t' t data_to_rm /\
    (not b) ==> equal cmp t t'
  )
  =
  delete_avl_aux_bst cmp t data_to_rm;
  delete_avl_aux_avl cmp t data_to_rm;
  fst (delete_avl_aux cmp t data_to_rm)

let delete_lemma (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : Lemma
  (let t' = delete_avl cmp t data_to_rm in
    size_of_tree t - 1 <= size_of_tree t' /\
    size_of_tree t' <= size_of_tree t /\
    height_of_tree t - 1 <= height_of_tree t' /\
    height_of_tree t' <= height_of_tree t
  )
  = delete_avl_aux_avl cmp t data_to_rm



let rec lemma_insert (#a: Type)
  (r: bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Lemma
  (requires mem cmp t new_data = false)
  (ensures reveal (snd (insert_avl_aux r cmp t new_data)) = true)
  = match t with
  | Leaf -> ()
  | Node data left right _ _ ->
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
  (ensures reveal (snd (delete_avl_aux cmp t data_to_rm)) = true)
  = match t with
  | Leaf -> ()
  | Node data left right _ _ ->
      let delta = cmp data_to_rm data in
      if delta < 0 then begin
        unicity_left cmp t data_to_rm;
        lemma_delete cmp left data_to_rm
      end else if delta > 0 then begin
        unicity_right cmp t data_to_rm;
        lemma_delete cmp right data_to_rm
      end else ()

(*)
let functional_correctness (#a: Type)
  (r: bool) (cmp: cmp a) (t: avl a cmp) (v: a)
  : Lemma
  (requires mem cmp t v = false)
  (ensures (
    let new_t, b = insert_avl_aux r cmp t v in
    let new_t2, b = delete_avl_aux cmp new_t v in
    equal cmp t new_t2
  ))
  =
  let new_t, b1 = insert_avl_aux r cmp t v in
  assert (mem cmp t v = false);
  lemma_insert r cmp t v;
  assert (reveal b1 = true);
  assert (add cmp t new_t v);
  let new_t2, b2 = delete_avl_aux cmp new_t v in
  assert (mem cmp new_t v = true);
  lemma_delete cmp new_t v;
  assert (reveal b2 = true);
  assert (mem cmp new_t2 v = false);
  assert (mem cmp t v = mem cmp new_t2 v);
  assert (add cmp new_t2 new_t v);
  test cmp t new_t new_t2 v;
  assert (equal cmp t new_t2);
  ()
