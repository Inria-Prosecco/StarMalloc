module Spec.BST

module M = FStar.Math.Lib
open Spec.Trees

(*** Binary search trees *)

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
type cond (a: Type) (cmp:cmp a) = c: (a -> bool){
  squash (forall x y. cmp x y = 0 ==> (c x = c y))
}


//@BST
let rec forall_keys (#a: Type) (t: tree a) (cond: a -> bool)
  : GTot bool =
  match t with
  | Leaf -> true
  | Node data left right _ _ ->
    cond data && forall_keys left cond && forall_keys right cond

//@BST
let key_left (#a: Type) (compare:cmp a) (root key: a) : bool =
  compare key root < 0
let key_right (#a: Type) (compare : cmp a) (root key: a) : bool =
  compare key root > 0

//@BST
let rec is_bst (#a: Type) (compare : cmp a) (x: tree a)
  : GTot bool =
  match x with
  | Leaf -> true
  | Node data left right _ _ ->
    is_bst compare left && is_bst compare right &&
    forall_keys left (key_left compare data) &&
    forall_keys right (key_right compare data)

//@BST
let bst (a: Type) (cmp:cmp a) = x:wdm a {is_bst cmp x}

(*** Operations *)

(**** Lookup *)

//@BST
let rec bst_search (#a: Type) (cmp:cmp a) (x: bst a cmp) (key: a) : option a =
  match x with
  | Leaf -> None
  | Node data left right _ _ ->
    let delta = cmp data key in
    if delta < 0 then bst_search cmp right key else
    if delta > 0 then bst_search cmp left key else
    Some data

//@BST
let rec forall_keys_trans (#a: Type) (t: tree a) (cond1 cond2: a -> bool)
  : Lemma
  (requires (forall x. cond1 x ==> cond2 x) /\ forall_keys t cond1)
  (ensures forall_keys t cond2)
  = match t with
  | Leaf -> ()
  | Node data left right _ _ ->
    forall_keys_trans left cond1 cond2; forall_keys_trans right cond1 cond2

//@BST
let rec mem (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a) : bool =
  match t with
  | Leaf -> false
  | Node data left right _ _ ->
      let delta = cmp x data in
      (delta = 0) || (mem cmp left x) || (mem cmp right x)

//TODO: minify
let rec equiv_aux (#a: Type)
  (cmp:cmp a) (t: bst a cmp) (cond:cond a cmp) (x: a)
  : Lemma
  (requires forall_keys t cond /\ mem cmp t x)
  (ensures cond x)
  = match t with
  | Leaf -> ()
  | Node data left right _ _ ->
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
  | Node data left right _ _ ->
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
  | Node data left right _ _ ->
      let delta = cmp x data in
      if delta = 0 then begin
        true
      end else if delta < 0 then begin
        memopt cmp left x
      end else begin
        memopt cmp right x
      end

let unicity_left (#a: Type) (cmp: cmp a) (t: bst a cmp{Node? t})
  (x: a)
  : Lemma
  (requires mem cmp t x)
  (ensures (
    let delta = cmp x (cdata t) in
    delta < 0 <==> mem cmp (cleft t) x
  ))
  = match t with
  | Node data left right _ _ ->
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
  (x: a)
  : Lemma
  (requires mem cmp t x)
  (ensures (
    let delta = cmp x (cdata t) in
    delta > 0 <==> mem cmp (cright t) x
  ))
  = match t with
  | Node data left right _ _ ->
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
  | Node data left right _ _ ->
      equivmem1 cmp left x;
      equivmem1 cmp right x

let rec equivmem2 (#a: Type) (cmp:cmp a) (t: bst a cmp) (x: a)
  : Lemma
  (requires mem cmp t x)
  (ensures memopt cmp t x)
  = match t with
  | Leaf -> ()
  | Node data left right _ _ ->
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
  | Node data left right _ _ ->
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
  | Node data left right _ _ ->
    // ad absurdum
    if mem cmp t x then begin
      assert (forall_keys t (key_left cmp x));
      equiv cmp t (key_left cmp x);
      assert (mem cmp t x);
      assert (key_left cmp x x);
      assert (cmp x x < 0)
    end;
    assert (mem cmp t x = false)

let rec test_aux0 (#a: Type)
  (cmp:cmp a) (t: bst a cmp) (x y: a)
  : Lemma
  (requires mem cmp t x /\ cmp x y = 0)
  (ensures mem cmp t y)
  = match t with
  | Leaf -> ()
  | Node data left right _ _ ->
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

//@BST
let rotate_left_bst (#a:Type) (cmp:cmp a) (r:wdm a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_left r))
  (ensures is_bst cmp (Some?.v (rotate_left r)))
  = match r with
  | Node x t1 (Node z t2 t3 _ _ ) _ _ ->
      assert (is_bst cmp (Node z t2 t3 0 0));
      assert (is_bst cmp (Node x t1 t2 0 0));
      forall_keys_trans t1 (key_left cmp x) (key_left cmp z)

let rotate_right_bst (#a:Type) (cmp:cmp a) (r:wdm a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_right r))
  (ensures is_bst cmp (Some?.v (rotate_right r)))
  = match r with
  | Node x (Node z t1 t2 _ _) t3 _ _ ->
      assert (is_bst cmp (Node z t1 t2 0 0));
      assert (is_bst cmp (Node x t2 t3 0 0));
      forall_keys_trans t3 (key_right cmp x) (key_right cmp z)

let rotate1_involutive (#a: Type) (t: wdm a)
  : Lemma
  (requires
    Some? (rotate_left t))
  (ensures
    Some?.v (rotate_right (Some?.v (rotate_left t))) == t)
  = ()

let rotate2_involutive (#a: Type) (t: wdm a)
  : Lemma
  (requires
    Some? (rotate_right t))
  (ensures
    Some?.v (rotate_left (Some?.v (rotate_right t))) == t)
  = ()

let rotate_left_bst2 (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (requires
    Some? (rotate_left t) /\ is_bst cmp (Some?.v (rotate_left t)))
  (ensures
    is_bst cmp t)
  =
  rotate1_involutive t;
  assert (Some?.v (rotate_right (Some?.v (rotate_left t))) == t);
  rotate_right_bst cmp (Some?.v (rotate_left t))

let rotate_left_bst_eq (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (requires Some? (rotate_left t))
  (ensures
    is_bst cmp t = is_bst cmp (Some?.v (rotate_left t))
  )
  =
  if is_bst cmp t
  then rotate_left_bst cmp t;
  if is_bst cmp (Some?.v (rotate_left t))
  then rotate_left_bst2 cmp t

let rotate_right_bst2 (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (requires
    Some? (rotate_right t) /\ is_bst cmp (Some?.v (rotate_right t)))
  (ensures
    is_bst cmp t)
  =
  rotate2_involutive t;
  assert (Some?.v (rotate_left (Some?.v (rotate_right t))) == t);
  rotate_left_bst cmp (Some?.v (rotate_right t))

let rotate_right_bst_eq (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (requires Some? (rotate_right t))
  (ensures
    is_bst cmp t = is_bst cmp (Some?.v (rotate_right t))
  )
  =
  if is_bst cmp t
  then rotate_right_bst cmp t;
  if is_bst cmp (Some?.v (rotate_right t))
  then rotate_right_bst2 cmp t

let rotate_right_left_dec (#a: Type) (t: wdm a)
  : Lemma
  (requires Some? (rotate_right_left t))
  (ensures
    Some?.v (rotate_right_left t)
    ==
    Some?.v (rotate_left (merge_tree
      (cdata t)
      (cleft t)
      (Some?.v (rotate_right (cright t)))
  )))
  = ()

//@BST
let rotate_right_left_bst (#a:Type) (cmp:cmp a) (r:wdm a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_right_left r))
  (ensures is_bst cmp (Some?.v (rotate_right_left r)))
  = match r with
  | Node x t1 (Node z (Node y t2 t3 _ _) t4 _ _) _ _ ->
    // Node y (Node x t1 t2) (Node z t3 t4)
    assert (is_bst cmp (Node z (Node y t2 t3 0 0) t4 0 0));
    assert (is_bst cmp (Node y t2 t3 0 0));
    let left = Node x t1 t2 0 0 in
    let right = Node z t3 t4 0 0 in

    assert (forall_keys (Node y t2 t3 0 0) (key_right cmp x));
    assert (forall_keys t2 (key_right cmp x));
    assert (is_bst cmp left);

    assert (is_bst cmp right);

    forall_keys_trans t1 (key_left cmp x) (key_left cmp y);
    assert (forall_keys left (key_left cmp y));

    forall_keys_trans t4 (key_right cmp z) (key_right cmp y);
    assert (forall_keys right (key_right cmp y))

let rotate_left_right_dec (#a: Type) (t: wdm a)
  : Lemma
  (requires Some? (rotate_left_right t))
  (ensures
    Some?.v (rotate_left_right t)
    ==
    Some?.v (rotate_right (merge_tree
      (cdata t)
      (Some?.v (rotate_left (cleft t)))
      (cright t)
  )))
  = ()

let rotate3_involutive (#a: Type) (t: wdm a)
  : Lemma
  (requires Some? (rotate_left_right t))
  (ensures
    (let t' = Some?.v (rotate_left
      (Some?.v (rotate_left_right t))) in
    merge_tree (cdata t')
      (Some?.v (rotate_right (cleft t')))
      (cright t')
    ==
    t
  ))
  = ()

let rotate_left_right_bst2 (#a:Type) (cmp:cmp a) (t:wdm a)
  : Lemma
  (requires
    Some? (rotate_left_right t) /\
    is_bst cmp (Some?.v (rotate_left_right t)))
  (ensures is_bst cmp t)
  =
  rotate3_involutive t;
  let t2 = Some?.v (rotate_left_right t) in
  rotate_left_bst_eq cmp t2;
  let t3 = Some?.v (rotate_left t2) in
  rotate_right_bst_eq cmp (cleft t3)

let rotate4_involutive (#a: Type) (t: wdm a)
  : Lemma
  (requires Some? (rotate_right_left t))
  (ensures
    (let t' = Some?.v (rotate_right
      (Some?.v (rotate_right_left t))) in
    merge_tree (cdata t')
      (cleft t')
      (Some?.v (rotate_left (cright t')))
    ==
    t
  ))
  = ()

let rotate_right_left_bst2 (#a:Type) (cmp:cmp a) (t:wdm a)
  : Lemma
  (requires
    Some? (rotate_right_left t) /\
    is_bst cmp (Some?.v (rotate_right_left t)))
  (ensures is_bst cmp t)
  =
  rotate4_involutive t;
  let t2 = Some?.v (rotate_right_left t) in
  rotate_right_bst_eq cmp t2;
  let t3 = Some?.v (rotate_right t2) in
  rotate_left_bst_eq cmp (cright t3)

//@BST
let rotate_left_right_bst (#a:Type) (cmp:cmp a) (r:wdm a)
  : Lemma
  (requires is_bst cmp r /\ Some? (rotate_left_right r))
  (ensures is_bst cmp (Some?.v (rotate_left_right r)))
  = match r with
  | Node x (Node z t1 (Node y t2 t3 _ _) _ _) t4 _ _ ->
    // Node y (Node z t1 t2) (Node x t3 t4)
    assert (is_bst cmp (Node z t1 (Node y t2 t3 0 0) 0 0));
    assert (is_bst cmp (Node y t2 t3 0 0));
    let left = Node z t1 t2 0 0 in
    let right = Node x t3 t4 0 0 in

    assert (is_bst cmp left);

    assert (forall_keys (Node y t2 t3 0 0) (key_left cmp x));
    assert (forall_keys t2 (key_left cmp x));
    assert (is_bst cmp right);

    forall_keys_trans t1 (key_left cmp z) (key_left cmp y);
    assert (forall_keys left (key_left cmp y));

    forall_keys_trans t4 (key_right cmp x) (key_right cmp y);
    assert (forall_keys right (key_right cmp y))

let rotate_right_left_bst_eq (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (requires Some? (rotate_right_left t))
  (ensures
    is_bst cmp t = is_bst cmp (Some?.v (rotate_right_left t))
  )
  =
  if is_bst cmp t
  then rotate_right_left_bst cmp t;
  if is_bst cmp (Some?.v (rotate_right_left t))
  then rotate_right_left_bst2 cmp t

let rotate_left_right_bst_eq (#a: Type) (cmp: cmp a) (t: wdm a)
  : Lemma
  (requires Some? (rotate_left_right t))
  (ensures
    is_bst cmp t = is_bst cmp (Some?.v (rotate_left_right t))
  )
  =
  if is_bst cmp t
  then rotate_left_right_bst cmp t;
  if is_bst cmp (Some?.v (rotate_left_right t))
  then rotate_left_right_bst2 cmp t

let rotate_left_equal (#a: Type) (cmp: cmp a) (r: bst a cmp)
  : Lemma
  (requires Some? (rotate_left r))
  (ensures (
    let _ = rotate_left_bst cmp r in
    equal cmp (Some?.v (rotate_left r)) r))
  =
  let r2 = Some?.v (rotate_left r) in
  rotate_left_bst cmp r

let rotate_right_equal (#a: Type) (cmp: cmp a) (r: bst a cmp)
  : Lemma
  (requires Some? (rotate_right r))
  (ensures (
    let _ = rotate_right_bst cmp r in
    equal cmp (Some?.v (rotate_right r)) r))
  =
  let r2 = Some?.v (rotate_right r) in
  rotate_right_bst cmp r

#push-options "--z3rlimit 25"
let rotate_right_left_equal (#a: Type) (cmp: cmp a) (r: bst a cmp)
  : Lemma
  (requires Some? (rotate_right_left r))
  (ensures (
    let _ = rotate_right_left_bst cmp r in
    equal cmp (Some?.v (rotate_right_left r)) r))
  =
  let r2 = Some?.v (rotate_right_left r) in
  rotate_right_left_bst cmp r

let rotate_left_right_equal (#a: Type) (cmp: cmp a) (r: bst a cmp)
  : Lemma
  (requires Some? (rotate_left_right r))
  (ensures (
    let _ = rotate_left_right_bst cmp r in
    equal cmp (Some?.v (rotate_left_right r)) r))
  =
  let r2 = Some?.v (rotate_left_right r) in
  rotate_left_right_bst cmp r
#pop-options

//TODO: refactor, change for wds trees
//@BST
(** Same bounds before and after rotate **)
let rotate_left_key_left (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_left r))
  (ensures  forall_keys (Some?.v (rotate_left r)) (key_left cmp root))
  = match r with
  | Node x t1 (Node z t2 t3 _ _) _ _ ->
      assert (forall_keys (Node z t2 t3 0 0) (key_left cmp root));
      assert (forall_keys (Node x t1 t2 0 0) (key_left cmp root))

let rotate_left_key_right (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_left r))
  (ensures  forall_keys (Some?.v (rotate_left r)) (key_right cmp root))
  = match r with
  | Node x t1 (Node z t2 t3 _ _) _ _ ->
      assert (forall_keys (Node z t2 t3 0 0) (key_right cmp root));
      assert (forall_keys (Node x t1 t2 0 0) (key_right cmp root))

let rotate_right_key_left (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_right r))
  (ensures  forall_keys (Some?.v (rotate_right r)) (key_left cmp root))
  = match r with
  | Node x (Node z t1 t2 _ _) t3 _ _ ->
      assert (forall_keys (Node z t1 t2 0 0) (key_left cmp root));
      assert (forall_keys (Node x t2 t3 0 0) (key_left cmp root))

let rotate_right_key_right (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_right r))
  (ensures  forall_keys (Some?.v (rotate_right r)) (key_right cmp root))
  = match r with
  | Node x (Node z t1 t2 _ _) t3 _ _ ->
      assert (forall_keys (Node z t1 t2 0 0) (key_right cmp root));
      assert (forall_keys (Node x t2 t3 0 0) (key_right cmp root))

let rotate_right_left_key_left (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_right_left r))
  (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_left cmp root))
  = match r with
  | Node x t1 (Node z (Node y t2 t3 _ _) t4 _ _) _ _ ->
    assert (forall_keys (Node z (Node y t2 t3 0 0) t4 0 0) (key_left cmp root));
    assert (forall_keys (Node y t2 t3 0 0) (key_left cmp root));
    let left = Node x t1 t2 0 0 in
    let right = Node z t3 t4 0 0 in
    assert (forall_keys left (key_left cmp root));
    assert (forall_keys right (key_left cmp root))

let rotate_right_left_key_right (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_right_left r))
  (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_right cmp root))
  = match r with
  | Node x t1 (Node z (Node y t2 t3 _ _) t4 _ _) _ _ ->
    assert (forall_keys (Node z (Node y t2 t3 0 0) t4 0 0) (key_right cmp root));
    assert (forall_keys (Node y t2 t3 0 0) (key_right cmp root));
    let left = Node x t1 t2 0 0 in
    let right = Node z t3 t4 0 0 in
    assert (forall_keys left (key_right cmp root));
    assert (forall_keys right (key_right cmp root))

let rotate_left_right_key_left (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_left cmp root) /\ Some? (rotate_left_right r))
  (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_left cmp root))
  = match r with
  | Node x (Node z t1 (Node y t2 t3 _ _) _ _) t4 _ _ ->
    assert (forall_keys (Node z t1 (Node y t2 t3 0 0) 0 0) (key_left cmp root));
    assert (forall_keys (Node y t2 t3 0 0) (key_left cmp root));
    let left = Node x t1 t2 0 0 in
    let right = Node z t3 t4 0 0 in
    assert (forall_keys left (key_left cmp root));
    assert (forall_keys right (key_left cmp root))

let rotate_left_right_key_right (#a:Type) (cmp:cmp a) (r:wdm a) (root:a)
  : Lemma
  (requires forall_keys r (key_right cmp root) /\ Some? (rotate_left_right r))
  (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_right cmp root))
  = match r with
  | Node x (Node z t1 (Node y t2 t3 _ _) _ _) t4 _ _ ->
    assert (forall_keys (Node z t1 (Node y t2 t3 0 0) 0 0) (key_right cmp root));
    assert (forall_keys (Node y t2 t3 0 0) (key_right cmp root));
    let left = Node x t1 t2 0 0 in
    let right = Node z t3 t4 0 0 in
    assert (forall_keys left (key_right cmp root));
    assert (forall_keys right (key_right cmp root))
