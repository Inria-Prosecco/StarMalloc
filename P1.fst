module P1


open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module Spec = Trees

open NTreeC3
/// The implementation of the Selectors.Tree interface.
/// Predicates prefixed by (**) correspond to stateful lemmas for folding and unfolding the tree predicate

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50 --ide_id_info_off"

let rec append_left #a (ptr: t a) (v: a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' ->  linked_tree ptr')
  (requires (fun h0 -> True))
  (ensures (fun h0 ptr' h1 -> v_linked_tree ptr' h1 == Spec.append_left (v_linked_tree ptr h0) v))
  =
  if is_null_t ptr then (
    (**) elim_linked_tree_leaf ptr;
    let sr = malloc 1 in
    let node = mk_node v ptr null_t sr in
    let new_tree = malloc node in
    (**) intro_linked_tree_leaf #a ();
    (**) pack_tree new_tree ptr null_t sr;
    new_tree
    // return new_tree
  ) else (
    let h1 = get () in
    (**) let node = NTreeC3.unpack_tree ptr in
    let h2 = get () in

    let ptr_t1 = hide (v_linked_tree ptr h1) in
    let ptr_t2 = hide (Spec.Node
      (get_data (sel ptr h2))
      (v_linked_tree (get_left node) h2)
      (v_linked_tree (get_right node) h2)
      (sel (get_size node) h2)) in
    assert (reveal ptr_t1 == reveal ptr_t2);
    assert (fst (Spec.is_wds ptr_t1));
    assert (fst (Spec.is_wds ptr_t2));
    let ptr_s1 = hide (Spec.csize (reveal ptr_t1)) in
    let ptr_s2 = hide (Spec.csize (reveal ptr_t2)) in
    assert (reveal ptr_s1 == reveal ptr_s2);
    Spec.check (reveal ptr_t1);
    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));

    (**) let new_left = append_left (get_left node) v in
    let h3 = get () in
    let old_left_t = hide (v_linked_tree (get_left node) h2) in
    let new_left_t = hide (v_linked_tree new_left h3) in
    let old_left_s = hide (Spec.size_of_tree (reveal old_left_t)) in
    let new_left_s = hide (Spec.size_of_tree (reveal new_left_t)) in
    let old_right_t = hide (v_linked_tree (get_right node) h2) in
    let new_right_t = hide (v_linked_tree (get_right node) h3) in
    let old_right_s = hide (Spec.size_of_tree (reveal old_right_t)) in
    let new_right_s = hide (Spec.size_of_tree (reveal new_right_t)) in
    assert (fst (Spec.is_wds (reveal ptr_t2)));
    assert (reveal ptr_s2 == reveal old_left_s + reveal old_right_s + 1);

    assert (fst (Spec.is_wds (reveal old_left_t)));
    assert (fst (Spec.is_wds (reveal new_left_t)));
    assert (old_right_t == new_right_t);
    assert (fst (Spec.is_wds old_right_t));
    Spec.append_left_aux_size (reveal old_left_t) v;
    assert (reveal new_left_s == reveal old_left_s + 1);
    assert (reveal old_right_s == reveal new_right_s);

    // TODO : incr (get_size node);
    let old_size = read (get_size node) in
    (***) write (get_size node) (old_size + 1);
    let h4 = get () in
    assert (sel (get_size node) h4 == sel (get_size node) h3 + 1);
    assert (sel (get_size node) h4 == new_left_s + new_right_s + 1);

    let new_node = mk_node (get_data node) new_left (get_right node) (get_size node) in
    assert (get_size new_node == get_size node);
    (***) write ptr new_node;

    (**) pack_tree ptr new_left (get_right node) (get_size node);
    return ptr
  )

// Alternative possible dans le corps de la fonction suivante
//free old_sr;
//let new_sr = malloc (old_size + 1) in

(*)
let rec append_left #a ptr v =
  if is_null_t ptr then (
    (**) elim_linked_tree_leaf ptr;
    let node = mk_node v ptr null_t in
    let new_tree = malloc node in
    (**) intro_linked_tree_leaf #a ();
    (**) pack_tree new_tree ptr null_t;
    new_tree
  ) else (
    (**) let node = unpack_tree ptr in
    let new_left = append_left (get_left node) v in
    let new_node = mk_node (get_data node) new_left (get_right node) in
    write ptr new_node;
    (**) pack_tree ptr new_left (get_right node);
    ptr
  )

let rec append_right #a ptr v =
  if is_null_t ptr then (
    (**) elim_linked_tree_leaf ptr;
    let node = mk_node v null_t ptr in
    let new_tree = malloc node in
    (**) intro_linked_tree_leaf #a ();
    (**) pack_tree new_tree null_t ptr;
    new_tree
  ) else (
    (**) let node = unpack_tree ptr in
    let new_right = append_right (get_right node) v in
    let new_node = mk_node (get_data node) (get_left node) new_right in
    write ptr new_node;
    (**) pack_tree ptr (get_left node) new_right;
    ptr
  )

let rec height #a ptr =
   if is_null_t ptr then (
     (**) elim_linked_tree_leaf ptr;
     0
   ) else (
     (**) let node = unpack_tree ptr in
     let hleft = height (get_left node) in
     let hright = height (get_right node) in
     (**) pack_tree ptr (get_left node) (get_right node);
     if hleft > hright then (
       hleft + 1
     ) else ( hright + 1 )
   )

let rec member ptr v =
  if is_null_t ptr then (
    (**) elim_linked_tree_leaf ptr;
    false
  ) else (
    (**) let node = unpack_tree ptr in
    if v = get_data node then (
      (**) pack_tree ptr (get_left node) (get_right node);
      true
    ) else (
      let mleft = member (get_left node) v in
      let mright = member (get_right node) v in
      (**) pack_tree ptr (get_left node) (get_right node);
      mleft || mright
    )
  )

#push-options "--ifuel 1 --fuel 2"
let rotate_left #a ptr =
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_right x_node);
  (**) let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  let new_subnode = mk_node x (get_left x_node) (get_left z_node) in
  let new_node = mk_node z ptr (get_right z_node) in
  write (get_right x_node) new_node;
  write ptr new_subnode;
  (**) pack_tree ptr (get_left x_node) (get_left z_node);
  (**) pack_tree (get_right x_node) ptr (get_right z_node);
  (get_right x_node)

let rotate_right #a ptr =
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_left x_node);
  let z_node = unpack_tree (get_left x_node) in
  let z = get_data z_node in
  let new_subnode = mk_node x (get_right z_node) (get_right x_node) in
  let new_node = mk_node z (get_left z_node) ptr in
  write (get_left x_node) new_node;
  write ptr new_subnode;
  (**) pack_tree ptr (get_right z_node) (get_right x_node);
  (**) pack_tree (get_left x_node) (get_left z_node) ptr;
  (get_left x_node)


let rotate_right_left #a ptr =
  (**) node_is_not_null ptr;
  // original root node
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_right x_node);
  // original right node
  // z = get_right x_node
  (**) let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  (**) node_is_not_null (get_left z_node);
  // original left (right node)
  // y = get_left (z_node)
  (**) let y_node = unpack_tree (get_left z_node) in
  let y = get_data y_node in
  let new_x = mk_node x (get_left x_node) (get_left y_node) in
  let new_z = mk_node z (get_right y_node) (get_right z_node) in
  let new_y = mk_node y ptr (get_right x_node) in

  write ptr new_x;
  write (get_right x_node) new_z;
  write (get_left z_node) new_y;

  (**) pack_tree ptr (get_left x_node) (get_left y_node);
  (**) pack_tree (get_right x_node) (get_right y_node) (get_right z_node);
  (**) pack_tree (get_left z_node) ptr (get_right x_node);

  (get_left z_node)


let rotate_left_right #a ptr =
  (**) node_is_not_null ptr;
  // original root node
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in

  (**) node_is_not_null (get_left x_node);

  // original left node
  // z = get_left x_node
  (**) let z_node = unpack_tree (get_left x_node) in
  let z = get_data z_node in

  (**) node_is_not_null (get_right z_node);

  // original right (left node)
  // y = get_right (z_node)
  (**) let y_node = unpack_tree (get_right z_node) in
  let y = get_data y_node in

  let new_z = mk_node z (get_left z_node) (get_left y_node) in
  let new_x = mk_node x (get_right y_node) (get_right x_node) in
  let new_y = mk_node y (get_left x_node) ptr in

  write (get_left x_node) new_z;
  write ptr new_x;
  write (get_right z_node) new_y;

  (**) pack_tree (get_left x_node) (get_left z_node) (get_left y_node);
  (**) pack_tree ptr (get_right y_node) (get_right x_node);
  (**) pack_tree (get_right z_node) (get_left x_node) ptr;

  (get_right z_node)

let rec is_balanced #a ptr =
  if is_null_t ptr then (
    (**) elim_linked_tree_leaf ptr;
    true
  ) else (

  (**) let node = unpack_tree ptr in
  let lh = height (get_left node) in
  let rh = height (get_right node) in

  let lbal = is_balanced(get_left node) in
  let rbal = is_balanced(get_right node) in

  (**) pack_tree ptr (get_left node) (get_right node);
  (lbal && rbal) && ((rh - lh) >= -1 && (rh - lh) <= 1))

#push-options "--ifuel 2"
let rebalance_avl #a cmp ptr =
  if is_balanced ptr then (
    return ptr
  ) else (

    (**) node_is_not_null ptr;
    (**) let node = unpack_tree ptr in

    let lh = height (get_left node) in
    let rh = height (get_right node) in

    if (lh - rh) > 1 then (

      (**) node_is_not_null (get_left node);
      (**) let l_node = unpack_tree (get_left node) in

      let llh = height (get_left l_node) in
      let lrh = height (get_right l_node) in

      (**) pack_tree (get_left node) (get_left l_node) (get_right l_node);
      (**) pack_tree ptr (get_left node) (get_right node);

      if lrh > llh then (
        rotate_left_right ptr

      ) else (
        rotate_right ptr
      )

    ) else (

      if (lh - rh) < - 1 then (

        (**) node_is_not_null (get_right node);
        (**) let r_node = unpack_tree (get_right node) in

        let rlh = height (get_left r_node) in
        let rrh = height (get_right r_node) in

        (**) pack_tree (get_right node) (get_left r_node) (get_right r_node);
        (**) pack_tree ptr (get_left node) (get_right node);

        if rlh > rrh then (
          rotate_right_left ptr
        ) else (
          rotate_left ptr
        )

      ) else (
        (**) pack_tree ptr (get_left node) (get_right node);
        ptr
      )
    )
  )
#pop-options

let rec insert_avl #a cmp ptr v =
  if is_null_t ptr then (
    (**) elim_linked_tree_leaf ptr;
    let node = mk_node v ptr null_t in
    let new_tree = malloc node in
    (**) intro_linked_tree_leaf #a ();
    (**) pack_tree new_tree ptr null_t;
    new_tree
  ) else (
    (**) let node = unpack_tree ptr in
    if cmp (get_data node) v >= 0 then (
      let new_left = insert_avl cmp (get_left node) v in
      let new_node = mk_node (get_data node) new_left (get_right node) in
      write ptr new_node;
      (**) pack_tree ptr new_left (get_right node);
      rebalance_avl cmp ptr
    )
    else (
      let new_right = insert_avl cmp (get_right node) v in
      let new_node = mk_node (get_data node) (get_left node) new_right in
      write ptr new_node;
      (**) pack_tree ptr (get_left node) new_right;
      rebalance_avl cmp ptr
    )
  )

#pop-options
