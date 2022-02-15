(*
let induction_wds (#a: Type) (x: a) (l r:wds a)
  : Lemma (let s = size_of_tree l + size_of_tree r + 1 in
           let t = Node x l r s in
   is_wds t)
  =
  assert (is_wds l);
  assert (is_wds r);
  let s = size_of_tree l + size_of_tree r + 1 in
  let t = Node x l r s in
  assert (s == size_of_tree t);
  assert (is_wds t);
  ()
*)

//@D
//let rec mem_eq (#a: eqtype)  (r: tree a) (x: a) : bool =
//  match r with
//  | Leaf -> false
//  | Node data left right _ ->
//    (data = x) || (mem_eq right x) || (mem_eq left x)

(**** Append *)
//@D
//let aux_size_left_subtree (#a: Type) (t1: tree a) (t2: tree a)
//  : Lemma
//  (requires (size_of_tree t2 == size_of_tree t1 + 1))
//  (ensures (
//    forall (x:a) (tr: tree a) (n:nat).
//    size_of_tree (Node x t2 tr n) == size_of_tree (Node x t1 tr n) + 1))
//  = ()
//let aux_size_right_subtree (#a: Type) (t1: tree a) (t2: tree a)
//  : Lemma
//  (requires (size_of_tree t2 == size_of_tree t1 + 1))
//  (ensures (
//    forall (x:a) (tl: tree a) (n:nat).
//    size_of_tree (Node x tl t2 n) == size_of_tree (Node x tl t1 n) + 1))
//  = ()

//@D
//let rec append_left_aux (#a: Type) (t: wds a) (v: a)
//  : tree a
//  = match t with
//  | Leaf -> Node v Leaf Leaf 1
//  | Node x left right size ->
//    Node x (append_left_aux left v) right (size + 1)

//@D
//let rec append_left_aux_size (#a: Type) (t: wds a) (v: a)
//  : Lemma (size_of_tree (append_left_aux t v) == size_of_tree t + 1)
//  = match t with
//  | Leaf -> ()
//  | Node x left right size ->
//      append_left_aux_size left v;
//      aux_size_left_subtree left (append_left_aux left v)

//@D
(* random *)
//let rec append_left_aux_size2 (#a: Type) (t: wds a) (v: a)
//  : Lemma (is_wds (append_left_aux t v))
//  = match t with
//  | Leaf -> ()
//  | Node x left right size ->
//      let new_left = append_left_aux left v in
//      append_left_aux_size2 left v;
//      assert (is_wds (append_left_aux left v));
//      append_left_aux_size left v;
//      assert (size_of_tree new_left == size_of_tree left + 1);
//      aux_size_left_subtree left new_left
//
//let append_left (#a: Type) (t: wds a) (v: a)
//  : wds a
//  = append_left_aux_size2 t v; append_left_aux t v
//
//let rec append_left_mem (#a: eqtype) (t: wds a) (v: a) (x: a)
//  : Lemma (
//    let r = append_left t v in
//    x <> v ==> mem_eq t x = mem_eq r x /\
//    mem_eq r v
//  ) =
//  let r = append_left t v in
//  match t with
//  | Leaf ->
//      assert (mem_eq t x = false);
//      assert (mem_eq r v = true)
//  | Node data left right size ->
//      let new_left = append_left_aux left v in
//      append_left_mem left v x
//
//let rec append_right_aux (#a: Type) (t: tree a) (v: a)
//  : tree a =
//  match t with
//  | Leaf -> Node v Leaf Leaf 1
//  | Node x left right size ->
//    Node x left (append_right_aux right v) (size + 1)
//
//let rec append_right_aux_size (#a: Type) (t: wds a) (v: a)
//  : Lemma (size_of_tree (append_right_aux t v) == size_of_tree t + 1)
//  = match t with
//  | Leaf -> ()
//  | Node x left right size ->
//      append_right_aux_size right v;
//      aux_size_right_subtree right (append_right_aux right v)
//
//(* random *)
//let rec append_right_aux_size2 (#a: Type) (t: wds a) (v: a)
//  : Lemma (is_wds (append_right_aux t v))
//  = match t with
//  | Leaf -> ()
//  | Node x left right size ->
//      let new_right = append_right_aux right v in
//      append_right_aux_size2 right v;
//      assert (is_wds (append_right_aux right v));
//      append_right_aux_size right v;
//      assert (size_of_tree new_right == size_of_tree right + 1);
//      aux_size_right_subtree right new_right
//
//let append_right (#a: Type) (t: wds a) (v: a)
//  : wds a
//  = append_right_aux_size2 t v; append_right_aux t v

//@D
//let rec insert_bst_aux (#a: Type) (cmp:cmp a) (t: bst a cmp) (key: a)
//  : tree a =
//  match t with
//  | Leaf -> Node key Leaf Leaf 1
//  | Node data left right size ->
//    let delta = cmp data key in
//    if delta >= 0 then begin
//      let new_left = insert_bst_aux cmp left key in
//      Node data new_left right (size + 1)
//    end else begin
//      let new_right = insert_bst_aux cmp right key in
//      Node data left new_right (size + 1)
//    end
//
//let rec insert_bst_aux_size (#a: Type) (cmp:cmp a) (t: bst a cmp) (new_data: a)
//  : Lemma (
//    let new_t = insert_bst_aux cmp t new_data in
//    size_of_tree new_t == size_of_tree t + 1 /\
//    is_wds new_t)
//  = match t with
//  | Leaf -> ()
//  | Node data left right size ->
//    let delta = cmp data new_data in
//    if delta >= 0 then begin
//      let new_left = insert_bst_aux cmp left new_data in
//      insert_bst_aux_size cmp left new_data;
//      aux_size_left_subtree left new_left;
//      induction_wds data new_left right
//    end else begin
//      let new_right = insert_bst_aux cmp right new_data in
//      insert_bst_aux_size cmp right new_data;
//      aux_size_right_subtree right new_right;
//      induction_wds data left new_right
//    end
//
//let insert_bst (#a: Type) (cmp:cmp a) (x: bst a cmp) (key: a)
//  : t:wds a{size_of_tree t == size_of_tree x + 1}
//  =
//  insert_bst_aux_size cmp x key; insert_bst_aux cmp x key

//@D
(*)
let rec insert_bst_preserves_forall_keys
  (#a: Type)
  (cmp:cmp a)
  (x: bst a cmp)
  (key: a)
  (cond: a -> bool)
    : Lemma
      (requires (forall_keys x cond /\ cond key))
      (ensures (forall_keys (insert_bst cmp x key) cond))
  =
  match x with
  | Leaf -> ()
  | Node data left right _ ->
    let delta = cmp data key in
    if delta >= 0 then
      insert_bst_preserves_forall_keys cmp left key cond
    else
      insert_bst_preserves_forall_keys cmp right key cond

let rec insert_bst_preserves_bst
  (#a: Type)
  (cmp:cmp a)
  (x: bst a cmp)
  (key: a)
    : Lemma(is_bst cmp (insert_bst cmp x key))
  =
  match x with
  | Leaf -> ()
  | Node data left right _ ->
    let delta = cmp data key in
    if delta >= 0 then begin
      insert_bst_preserves_forall_keys cmp left key (key_left cmp data);
      insert_bst_preserves_bst cmp left key
    end else begin
      insert_bst_preserves_forall_keys cmp right key (key_right cmp data);
      insert_bst_preserves_bst cmp right key
    end
*)

// \forall x \in t1, cmp x v > 0
// \forall x \in t2, cmp x v >= 0
//@D
//let add_lower_bound (#a: Type) (cmp:cmp a) (t1 t2: bst a cmp) (v: a)
//  : Lemma
//  (requires
//    add cmp t1 t2 v /\
//    forall_keys t1 (fun x -> cmp x v > 0)
//  )
//  (ensures
//    forall_keys t2 (fun x -> cmp x v >= 0)
//  )
//  =
//  forall_keys_trans t1
//    (fun x -> cmp x v > 0)
//    (fun x -> cmp x v >= 0);
//  assert (forall_keys t1 (fun x -> cmp x v >= 0));
//  equiv cmp t1 (fun x -> cmp x v >= 0);
//  assert (forall x. mem cmp t1 x ==> cmp x v >= 0);
//  assert (forall x. mem cmp t2 x ==> cmp x v >= 0);
//  equiv cmp t2 (fun x -> cmp x v >= 0);
//  ()

(*
let add_right_no_intermediate_value (#a: Type)
  (cmp:cmp a) (t1 t2: bst a cmp) (v: a) (t3: bst a cmp{Node? t3})
  : Lemma
  (requires
    t2 == cright t3 /\
    cmp (cdata t3) v < 0 /\
    add cmp t1 t2 v /\
    forall_keys t1 (fun x -> cmp x v > 0)
  )
  (ensures
    forall_keys t3 (fun x -> cmp x (cdata t3) <= 0
                          || cmp x v >= 0)
  )
  =
  assert (forall x. mem cmp t3 x =
    (cmp (cdata t3) x = 0) ||
    mem cmp (cleft t3) x ||
    mem cmp (cright t3) x
  );
  // left + center
  assert (forall_keys (cleft t3) (key_left cmp (cdata t3)));
  forall_keys_trans (cleft t3)
    (key_left cmp (cdata t3))
    (fun x -> cmp x (cdata t3) <= 0);
  assert (forall_keys (cleft t3) (fun x -> cmp x (cdata t3) <= 0));
  equiv cmp (cleft t3) (fun x -> cmp x (cdata t3) <= 0);
  assert (forall x. (cmp (cdata t3) x = 0 || (mem cmp (cleft t3) x))
    ==> cmp x (cdata t3) <= 0);
  // right
  add_lower_bound cmp t1 t2 v;
  assert (forall_keys t2 (fun x -> cmp x v >= 0));
  equiv cmp (cright t3) (fun x -> cmp x v >= 0);
  // conclusion
  assert (forall x. mem cmp t3 x
    ==> cmp x (cdata t3) <= 0 || cmp x v >= 0);
  equiv cmp t3 (fun x -> cmp x (cdata t3) <= 0 || cmp x v >= 0);
  assert (forall_keys t3 (fun x -> cmp x (cdata t3) <= 0
                               || cmp x v >= 0))
*)

//@D
(*)
let rec delete_avl_aux_deprecated (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : result:(wds a & bool){
    let t',b = result in
    size_of_tree t' = size_of_tree t - (int_of_bool b) /\
    is_wds t'
  }
  =
  match t with
  | Leaf -> Leaf, false
  | Node data left right size ->
      let delta = cmp data data_to_rm in
      if delta > 0 then begin
        let new_left, b = delete_avl_aux cmp left data_to_rm in
        let new_size = size - (int_of_bool b) in
        let t, b = Node data new_left right new_size, b in
        rebalance_avl_wds_size t;
        rebalance_avl_wds t, b
      end
      else if delta < 0 then begin
        let new_right, b = delete_avl_aux cmp right data_to_rm in
        let new_size = size - (int_of_bool b) in
        let t, b = Node data left new_right new_size, b in
        rebalance_avl_wds_size t;
        rebalance_avl_wds t, b
      end else t, false
*)

(*
let rec insert_avl_aux_height (#a: Type)
  (cmp: cmp a) (x: avl a cmp) (key: a)
  : Lemma (
    height x <= height (insert_avl cmp x key) /\
    height (insert_avl cmp x key) <= height x + 1
  )
  = match x with
  | Leaf -> ()
  | Node data left right size ->
      let delta = cmp data key in
      if delta >= 0 then
        insert_avl_aux_height cmp left key
      else
        insert_avl_aux_height cmp right key

let insert_avl_aux_height2 (#a: Type)
  (cmp: cmp a) (x: avl a cmp) (key: a)
  : Lemma
  (
    Node? x ==> (
    let x2 = snd (insert_avl_aux cmp x key) in
    height (cleft x) == height (cleft x2)
    \/
    height (cright x) == height (cright x2)
  ))
  = match x with
  | Leaf -> ()
  | Node data left right size -> ()
*)

(*)
let delete_avl (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a)
  : t':wds a{
    let _,b = delete_avl_aux cmp t data_to_rm in
    size_of_tree t' = size_of_tree t - (int_of_bool b) /\
    is_wds t'
  }
  = fst (delete_avl_aux cmp t data_to_rm)
*)

(*
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rec insert_avl_proof_aux (#a: Type)
  (cmp:cmp a) (x: avl a cmp) (key: a) (root:a)
  : Lemma (requires is_avl cmp x)
    (ensures (
      let res = insert_avl cmp x key in
      is_avl cmp res /\
      height x <= height res /\
      height res <= height x + 1 /\
      (forall_keys x (key_left cmp root) /\ key_left cmp root key ==> forall_keys res (key_left cmp root)) /\
      (forall_keys x (key_right cmp root) /\ key_right cmp root key ==> forall_keys res (key_right cmp root)))
    )
  = match x with
  | Leaf -> ()
  | Node data left right size ->
    let delta = cmp data key in
    if delta >= 0 then (
      let new_left = insert_avl cmp left key in
      let tmp = Node data new_left right (size+1) in

      insert_avl_proof_aux cmp left key data;
      insert_avl_proof_aux cmp left key root;
      rebalance_avl_wds_proof cmp tmp root

    ) else (
      let new_right = insert_avl cmp right key in
      let tmp = Node data left new_right (size+1) in

      insert_avl_proof_aux cmp right key data;
      insert_avl_proof_aux cmp right key root;
      rebalance_avl_wds_proof cmp tmp root
    )
#pop-options
*)

(*
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rec delete_avl_proof_aux (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (data_to_rm: a) (root:a)
  : Lemma (requires is_avl cmp t)
    (ensures (
      let res = delete_avl cmp t data_to_rm  in
      is_avl cmp res /\
      height t - 1 <= height res /\
      height res <= height t /\
      (forall_keys t (key_left cmp root) /\
        key_left cmp root data_to_rm
        ==> forall_keys res (key_left cmp root)) /\
      (forall_keys t (key_right cmp root) /\
        key_right cmp root data_to_rm
        ==> forall_keys res (key_right cmp root)))
    )
  = match t with
  | Leaf -> ()
  //| Node data Leaf Leaf 1 -> ()
  | Node data left right size ->
    let delta = cmp data data_to_rm in
    if delta > 0 then (
      let new_left = delete_avl cmp left data_to_rm in
      let tmp = Node data new_left right (size-1) in
      assume (is_wds tmp);
      delete_avl_proof_aux cmp left data_to_rm data;
      delete_avl_proof_aux cmp left data_to_rm root;
      rebalance_avl_wds_proof cmp tmp root

    ) else if delta < 0 then (
      let new_right = delete_avl cmp right data_to_rm in
      let tmp = Node data left new_right (size-1) in
      assume (is_wds tmp);
      delete_avl_proof_aux cmp right data_to_rm data;
      delete_avl_proof_aux cmp right data_to_rm root;
      rebalance_avl_wds_proof cmp tmp root
    ) else ()
#pop-options
*)

(*
let insert_avl_proof (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Lemma
  (requires is_avl cmp t)
  (ensures is_avl cmp (insert_avl cmp t new_data))
  = Classical.forall_intro (
      Classical.move_requires (
        insert_avl_proof_aux cmp t new_data
      )
    )
*)

(*
let delete_avl_proof (#a: Type)
  (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Lemma
  (requires is_avl cmp t)
  (ensures is_avl cmp (delete_avl cmp t new_data))
  = Classical.forall_intro (
      Classical.move_requires (
        delete_avl_proof_aux cmp t new_data
      )
    )
*)
(*
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec insert_avl2_proof_aux (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a) (root:a)
  : Lemma (requires is_avl cmp t)
    (ensures (
      let res, _ = insert_avl2_aux r cmp t new_data in
      is_avl cmp res /\
      height t <= height res /\
      height res <= height t + 1 /\
      (forall_keys t (key_left cmp root) /\
        key_left cmp root new_data
        ==> forall_keys res (key_left cmp root)) /\
      (forall_keys t (key_right cmp root) /\
        key_right cmp root new_data
        ==> forall_keys res (key_right cmp root)))
    )
  =
  match t with
  | Leaf -> ()
  | Node data left right size ->
    let delta = cmp data new_data in
    if delta = 0 then begin
      if r then begin
        let t = Node new_data left right size in
        forall_keys_trans left
          (key_left cmp data) (key_left cmp new_data);
        forall_keys_trans right
          (key_right cmp data) (key_right cmp new_data);
        assert (is_bst cmp t)
      end else ()
    end
    else if delta > 0 then begin
      let new_left, b = insert_avl2_aux r cmp left new_data in
      let new_size = size + (int_of_bool b) in
      let t, b = Node data new_left right new_size, b in
      insert_avl2_proof_aux r cmp left new_data data;
      insert_avl2_proof_aux r cmp left new_data root;
      rebalance_avl_wds_proof cmp t root
    end else begin
      let new_right, b = insert_avl2_aux r cmp right new_data in
      let new_size = size + (int_of_bool b) in
      let t, b = Node data left new_right new_size, b in
      insert_avl2_proof_aux r cmp right new_data data;
      insert_avl2_proof_aux r cmp right new_data root;
      rebalance_avl_wds_proof cmp t root
    end
#pop-options

let insert_avl2_proof (#a: Type)
  (r:bool) (cmp:cmp a) (t: avl a cmp) (new_data: a)
  : Lemma
  (requires is_avl cmp t)
  (ensures is_avl cmp (insert_avl2 r cmp t new_data))
  = Classical.forall_intro (
      Classical.move_requires (
        insert_avl2_proof_aux r cmp t new_data
      )
    )
*)

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

