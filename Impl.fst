module Impl


open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

//module Spec = Trees
module U = FStar.UInt64
module I = FStar.Int64

open Impl.Core


/// The implementation of the Selectors.Tree interface.
/// Predicates prefixed by (**) correspond to stateful lemmas for folding and unfolding the tree predicate

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@Trees
let create_leaf (#a: Type0) (_: unit) : Steel (t a)
  emp (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_linked_tree ptr h1 == Spec.Leaf)
  = intro_linked_tree_leaf ();
    // TODO: it should be possible to remove next line
    let h = get () in
    return null_t

//@Trees
#push-options "--fuel 1 --ifuel 1"
let create_tree (#a: Type0) (v: a) : Steel (t a)
  emp (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 ->
    v_linked_tree ptr h1 ==
    Spec.Node v Spec.Leaf Spec.Leaf (U.v one))
  =
  let l = create_leaf () in
  let r = create_leaf () in
  let sr = malloc 1UL in
  let n = mk_node v l r sr in
  let ptr = malloc n in
  pack_tree ptr l r sr;
  return ptr
#pop-options

//@Trees
let sot_wds (#a: Type) (ptr: t a)
  : Steel (U.t)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures (fun h0 s h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    U.v s == Spec.sot_wds (v_linked_tree ptr h0) /\
    U.v s == Spec.size_of_tree (v_linked_tree ptr h0)
  ))
  =
  if is_null_t ptr then (
    assert (is_null_t ptr);
    null_is_leaf ptr;
    let h = get () in
    assert (0 == Spec.sot_wds (v_linked_tree ptr h));
    return zero
  ) else (
    let h1 = get () in
    (**) let node = unpack_tree ptr in
    let h2 = get () in
    let ptr_t1 = hide (v_linked_tree ptr h1) in
    let ptr_t2 = hide (Spec.Node
      (get_data (sel ptr h2))
      (v_linked_tree (get_left node) h2)
      (v_linked_tree (get_right node) h2)
      (U.v (sel (get_size node) h2))
    ) in
    assert (reveal ptr_t1 == reveal ptr_t2);
    assert (Spec.is_wds (reveal ptr_t1));
    let ptr_s1 = hide (Spec.sot_wds ptr_t1) in
    let ptr_s2 = hide (Spec.sot_wds ptr_t2) in
    assert (reveal ptr_s1 == reveal ptr_s2);
    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));
    let s = read (get_size node) in
    assert (U.v s == Spec.sot_wds (v_linked_tree ptr h1));
    pack_tree ptr (get_left node) (get_right node) (get_size node);
    return s
  )

//@Trees
let merge_tree (#a: Type0) (v: a) (l: t a) (r: t a) : Steel (t a)
  (linked_tree l `star` linked_tree r)
  (fun ptr -> linked_tree ptr)
  (requires fun h0 ->
    let s1 = Spec.size_of_tree (v_linked_tree l h0) in
    let s2 = Spec.size_of_tree (v_linked_tree r h0) in
    s1 + s2 + 1 <= c)
  (ensures fun h0 ptr h1 ->
    let s1 = Spec.size_of_tree (v_linked_tree l h0) in
    let s2 = Spec.size_of_tree (v_linked_tree r h0) in
    let s = s1 + s2 + 1 in
    s <= c /\
    v_linked_tree ptr h1 ==
    Spec.Node v
      (v_linked_tree l h0)
      (v_linked_tree r h0)
      s)
  =
  let s1 = sot_wds l in
  let s2 = sot_wds r in
  let s = U.add (U.add s1 s2) one in
  let sr = malloc s in
  let n = mk_node v l r sr in
  let ptr = malloc n in
  pack_tree ptr l r sr;
  return ptr

//let rec append_left #a (ptr: t a) (v: a)
//  : Steel (t a)
//  (linked_tree ptr)
//  (fun ptr' -> linked_tree ptr')
//  (requires (fun h0 ->
//    Spec.size_of_tree (v_linked_tree ptr h0) < c))
//  (ensures (fun h0 ptr' h1 ->
//    v_linked_tree ptr' h1
//    == Spec.append_left (v_linked_tree ptr h0) v /\
//    Spec.size_of_tree (v_linked_tree ptr' h1)
//    == Spec.size_of_tree (v_linked_tree ptr h0) + 1 /\
//    Spec.size_of_tree (v_linked_tree ptr' h1) <= c))
//  =
//  let h = get () in
//  assert (Spec.size_of_tree (v_linked_tree ptr h) < c);
//  if is_null_t ptr then (
//    // TODO: use create_leaf?
//    //(**) elim_linked_tree_leaf ptr;
//    (**) null_is_leaf ptr;
//    (**) let second_leaf = create_leaf () in
//    let sr = malloc one in
//    //let node = mk_node v ptr null_t sr in
//    let node = mk_node v ptr second_leaf sr in
//    let new_tree = malloc node in
//    //(**) intro_linked_tree_leaf ();
//    (**) pack_tree new_tree ptr second_leaf sr;
//    return new_tree
//    // return new_tree
//  ) else (
//    let h1 = get () in
//    (**) let node = NTreeC3.unpack_tree ptr in
//    let h2 = get () in
//
//    let ptr_t1 = hide (v_linked_tree ptr h1) in
//    let ptr_t2 = hide (Spec.Node
//      (get_data (sel ptr h2))
//      (v_linked_tree (get_left node) h2)
//      (v_linked_tree (get_right node) h2)
//      (U.v (sel (get_size node) h2))) in
//    assert (reveal ptr_t1 == reveal ptr_t2);
//    assert (Spec.is_wds ptr_t1);
//    assert (Spec.is_wds ptr_t2);
//    let ptr_s1 = hide (Spec.sot_wds (reveal ptr_t1)) in
//    let ptr_s2 = hide (Spec.sot_wds (reveal ptr_t2)) in
//    assert (reveal ptr_s1 == reveal ptr_s2);
//    //Spec.check (reveal ptr_t1);
//    assert (reveal ptr_s1 == Spec.size_of_tree (reveal ptr_t1));
//
//    (**) let new_left = append_left (get_left node) v in
//    let h3 = get () in
//    let old_left_t = hide (v_linked_tree (get_left node) h2) in
//    let new_left_t = hide (v_linked_tree new_left h3) in
//    let old_right_t = hide (v_linked_tree (get_right node) h2) in
//    let new_right_t = hide (v_linked_tree (get_right node) h3) in
//    //let old_left_s = hide (Spec.size_of_tree (reveal old_left_t)) in
//    //let new_left_s = hide (Spec.size_of_tree (reveal new_left_t)) in
//    //let old_right_s = hide (Spec.size_of_tree (reveal old_right_t)) in
//    //let new_right_s = hide (Spec.size_of_tree (reveal new_right_t)) in
//    //assert (fst (Spec.is_wds (reveal ptr_t2)));
//    //assert (reveal ptr_s2 ==
//    //reveal old_left_s + reveal old_right_s + 1);
//
//    //assert (fst (Spec.is_wds (reveal old_left_t)));
//    //assert (fst (Spec.is_wds (reveal new_left_t)));
//    //assert (old_right_t == new_right_t);
//    //assert (fst (Spec.is_wds old_right_t));
//    Spec.append_left_aux_size (reveal old_left_t) v;
//    //assert (reveal new_left_s == reveal old_left_s + 1);
//    //assert (reveal old_right_s == reveal new_right_s);
//
//    // TODO : incr (get_size node);
//    let old_size = read (get_size node) in
//    (***) write (get_size node) (U.add old_size one);
//    let h4 = get () in
//    //assert (sel (get_size node) h4 == U.add (sel (get_size node) h3) one);
//    //assert (U.v (sel (get_size node) h4) == new_left_s + new_right_s + 1);
//
//    let new_node = mk_node
//      (get_data node)
//      new_left
//      (get_right node)
//      (get_size node)
//    in
//    //assert (get_size new_node == get_size node);
//    (***) write ptr new_node;
//    let h5 = get () in
//    //assert (U.v (sel (get_size node) h5) <= c);
//    (**) pack_tree ptr new_left (get_right node) (get_size node);
//    return ptr
//  )
//
//// Alternative possible dans le corps de la fonction suivante
////free old_sr;
////let new_sr = malloc (old_size + 1) in
//
//let rec append_right #a (ptr: t a) (v: a)
//  : Steel (t a)
//  (linked_tree ptr)
//  (fun ptr' -> linked_tree ptr')
//  (requires (fun h0 ->
//    Spec.size_of_tree (v_linked_tree ptr h0) < c))
//  (ensures (fun h0 ptr' h1 ->
//    v_linked_tree ptr' h1
//    == Spec.append_right (v_linked_tree ptr h0) v))
//  =
//  let h = get () in
//  assert (Spec.size_of_tree (v_linked_tree ptr h) < c);
//  if is_null_t ptr then (
//    //(**) elim_linked_tree_leaf ptr;
//    (**) null_is_leaf ptr;
//    (**) let second_leaf = create_leaf () in
//    let sr = malloc one in
//    let node = mk_node v second_leaf ptr sr in
//    let new_tree = malloc node in
//    //(**) intro_linked_tree_leaf ();
//    (**) pack_tree new_tree second_leaf ptr sr;
//    return new_tree
//  ) else (
//    (**) let node = unpack_tree ptr in
//    let h2 = get () in
//    let ptr_t2 = hide (Spec.Node
//      (get_data (sel ptr h2))
//      (v_linked_tree (get_left node) h2)
//      (v_linked_tree (get_right node) h2)
//      (U.v (sel (get_size node) h2))) in
//    assert (Spec.is_wds ptr_t2);
//    let ptr_s2 = hide (Spec.sot_wds (reveal ptr_t2)) in
//    //Spec.check (reveal ptr_t2);
//    assert (reveal ptr_s2 == Spec.size_of_tree (reveal ptr_t2));
//
//    (**) let new_right = append_right (get_right node) v in
//    let h3 = get () in
//    let old_left_t = hide (v_linked_tree (get_left node) h2) in
//    let new_left_t = hide (v_linked_tree (get_left node) h3) in
//    let old_right_t = hide (v_linked_tree (get_right node) h2) in
//    let new_right_t = hide (v_linked_tree new_right h3) in
//    //let old_left_s = hide (Spec.size_of_tree (reveal old_left_t)) in
//    //let new_left_s = hide (Spec.size_of_tree (reveal new_left_t)) in
//    //let old_right_s = hide (Spec.size_of_tree (reveal old_right_t)) in
//    //let new_right_s = hide (Spec.size_of_tree (reveal new_right_t)) in
//    //assert (reveal ptr_s2
//    //== reveal old_left_s + reveal old_right_s + 1);
//    //assert (reveal new_left_s == reveal old_left_s);
//    Spec.append_right_aux_size (reveal old_right_t) v;
//    //assert (reveal new_right_s == reveal old_right_s + 1);
//
//    let old_size = read (get_size node) in
//    write (get_size node) (U.add old_size one);
//    let new_node = mk_node
//      (get_data node)
//      (get_left node)
//      new_right
//      (get_size node)
//    in
//    write ptr new_node;
//    (**) pack_tree ptr (get_left node) new_right (get_size node);
//    return ptr
//  )

//@Trees
#push-options "--fuel 1 --ifuel 1"
let rec height (#a: Type0) (ptr: t a)
  : Steel U.t (linked_tree ptr) (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun h0 x h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    Spec.height (v_linked_tree ptr h0) == U.v x)
  =
  if is_null_t ptr then (
    (**) null_is_leaf ptr;
    return zero
  ) else (
    let h = get () in
    (**) not_null_is_node ptr;
    let s = hide (Spec.sot_wds (v_linked_tree ptr h)) in
    (**) let node = unpack_tree ptr in
    assert (reveal s <= c);
    Spec.height_lte_size (v_linked_tree ptr h);
    assert (Spec.height (v_linked_tree ptr h) <= c);
    let hleft = height (get_left node) in
    let hright = height (get_right node) in
    (**) pack_tree ptr (get_left node) (get_right node) (get_size node);
    let hptr = if U.gt hleft hright then U.add hleft one else U.add hright one in
    return hptr
  )
#pop-options

//@BST
#push-options "--fuel 1 --ifuel 1"
let rec member (#a: Type) (cmp:cmp a) (ptr: t a) (v: a)
  : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 b h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0) /\
    (Spec.mem (convert cmp) (v_linked_tree ptr h0) v <==> b) /\
    (Spec.memopt (convert cmp) (v_linked_tree ptr h0) v <==> b))
  =
  let h = get () in
  Spec.equivmem (convert cmp) (v_linked_tree ptr h) v;
  if is_null_t #a ptr then (
    (**) null_is_leaf ptr;
    return false
  ) else (
    (**) let node = unpack_tree ptr in
    let data = get_data node in
    let delta = cmp v data in
    if I.eq delta szero then begin
      (**) pack_tree ptr (get_left node) (get_right node) (get_size node);
      return true
    end else if I.lt delta szero then begin
      let b = member cmp (get_left node) v in
      (**) pack_tree ptr (get_left node) (get_right node) (get_size node);
      return b
    end else begin
      let b = member cmp (get_right node) v in
      (**) pack_tree ptr (get_left node) (get_right node) (get_size node);
      return b
    end
  )
#pop-options

//let rec insert_bst (#a: Type0) (cmp:cmp a) (ptr:t a) (v: a)
//  : Steel (t a)
//  (linked_tree ptr)
//  (fun ptr' -> linked_tree ptr')
//  (requires fun h0 ->
//    Spec.size_of_tree (v_linked_tree ptr h0) < c /\
//    Spec.is_bst (convert cmp) (v_linked_tree ptr h0))
//  (ensures fun h0 ptr' h1 ->
//    Spec.is_bst (convert cmp) (v_linked_tree ptr h0) /\
//    Spec.insert_bst (convert cmp) (v_linked_tree ptr h0) v
//    == v_linked_tree ptr' h1
//  )
//  =
//  if is_null_t #a ptr then (
//    (**) elim_linked_tree_leaf ptr;
//    (**) let ptr' = create_tree v in
//    return ptr'
//  ) else (
//    (**) let node = unpack_tree ptr in
//    let delta = cmp (get_data node) v in
//    if I.gte delta szero then (
//      let new_left = insert_bst cmp (get_left node) v in
//      let old_size = read (get_size node) in
//      write (get_size node) (U.add old_size one);
//      let new_node = mk_node (get_data node) new_left (get_right node) (get_size node) in
//      write ptr new_node;
//      (**) pack_tree ptr new_left (get_right node) (get_size node);
//      return ptr
//    ) else (
//      let new_right = insert_bst cmp (get_right node) v in
//      let old_size = read (get_size node) in
//      write (get_size node) (U.add old_size one);
//      let new_node = mk_node (get_data node) (get_left node) new_right (get_size node) in
//      write ptr new_node;
//      (**) pack_tree ptr (get_left node) new_right (get_size node);
//      return ptr
//    )
//  )

(*
let uincr (b: bool) (ptr: ref U.t)
  : Steel unit
  (vptr ptr)
  (fun _ -> vptr ptr)
  // TODO: bug with U.n_minus_one, type U32.t instead of U64.t
  (requires fun h0 -> U.lt (sel ptr h0) (U.uint_to_t c))
  (ensures fun h0 _ h1 ->
    U.lt (sel ptr h0) (U.uint_to_t c) /\
    (b ==> sel ptr h1 = U.add (sel ptr h0) one))
  =
  if b then (
    let old_value = read ptr in
    let new_value = U.add old_value one in
    write ptr new_value;
    return ()
  ) else ( return () )
*)

//@BST
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rec insert_bst2 (#a: Type)
  (r:bool) (cmp:cmp a) (ptr:t a) (new_data: a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.size_of_tree (v_linked_tree ptr h0) < c /\
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_bst (convert cmp) (v_linked_tree ptr h0) /\
    Spec.insert_bst2 r (convert cmp) (v_linked_tree ptr h0) new_data
    == v_linked_tree ptr' h1
  )
  =
  if is_null_t #a ptr then (
    (**) elim_linked_tree_leaf ptr;
    (**) let ptr' = create_tree new_data in
    return ptr'
  ) else (
    (**) let node = unpack_tree ptr in
    let delta = cmp (get_data node) new_data in
    if I.eq delta szero then (
      if r then (
        let new_node = mk_node new_data
          (get_left node) (get_right node) (get_size node) in
        write ptr new_node;
        pack_tree ptr
          (get_left node) (get_right node) (get_size node);
        return ptr
      ) else (
        pack_tree ptr
          (get_left node) (get_right node) (get_size node);
        return ptr
      )
    ) else (
      if I.gt delta szero then (
        let old_left_s = sot_wds (get_left node) in
        let new_left = insert_bst2 r cmp (get_left node) new_data in
        let new_left_s = sot_wds new_left in
        //assert (U.lte old_left_s new_left_s);
        let diff = U.sub new_left_s old_left_s in
        let old_size = read (get_size node) in
        write (get_size node) (U.add old_size diff);
        let new_node = mk_node (get_data node) new_left (get_right node) (get_size node) in
        write ptr new_node;
        (**) pack_tree ptr new_left (get_right node) (get_size node);
        return ptr
      ) else (
        let old_right_s = sot_wds (get_right node) in
        let new_right = insert_bst2 r cmp (get_right node) new_data in
        let new_right_s = sot_wds new_right in
        //assert (U.lte old_left_s new_left_s);
        let diff = U.sub new_right_s old_right_s in
        let old_size = read (get_size node) in
        write (get_size node) (U.add old_size diff);
        let new_node = mk_node (get_data node) (get_left node) new_right (get_size node) in
        write ptr new_node;
        (**) pack_tree ptr (get_left node) new_right (get_size node);
        return ptr
      )
    )
  )
#pop-options

// TODO : please prettify output after squash equiv...
//#push-options "--ifuel 1 --fuel 2 --z3rlimit 200"
(*
let rotate_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 -> Some? (Spec.rotate_left (v_linked_tree ptr h0)))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_left_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
  ))
  =
  let h0 = get () in
  Spec.rotate_left_size (v_linked_tree ptr h0);
  assert (Spec.size_of_tree (Spec.get (Spec.rotate_left_wds (v_linked_tree ptr h0)))
  == Spec.size_of_tree (v_linked_tree ptr h0));
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  // let ptr2 = get_right x_node in
  // TODO : node_is_not_null ptr2 should work
  (**) node_is_not_null (get_right x_node);
  (**) let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  //let h1 = get () in
  //let t1 = v_linked_tree (get_left x_node) h1 in
  //let t2 = v_linked_tree (get_left z_node) h1 in
  //let t3 = v_linked_tree (get_right z_node) h1 in
  let s1 = sot_wds (get_left x_node) in
  let s2 = sot_wds (get_left z_node) in
  let sx = U.add (U.add s1 s2) one in
  //assert (U.v sx == (U.v s1) + (U.v s2) + 1);
  //assert (U.v s1 = Spec.sot_wds (v_linked_tree (get_left x_node) h1));
  //assert (U.v s2 = Spec.sot_wds (v_linked_tree (get_left z_node) h1));
  write (get_size z_node) sx;
  let tx = mk_node x (get_left x_node) (get_left z_node) (get_size z_node) in
  write ptr tx;
  //let h = get () in
  //assert (fst (Spec.is_wds (v_linked_tree ptr h)));
  //assert (U.v (sel (get_size z_node) h) == Spec.size_of_tree (v_linked_tree (get_left x_node) h)
                                  //+ Spec.size_of_tree (v_linked_tree (get_left z_node) h) + 1);
  //let h = get () in
  //assert (fst (Spec.is_wds (v_linked_tree ptr h)));
  pack_tree ptr (get_left x_node) (get_left z_node) (get_size z_node);
  let tz = mk_node z ptr (get_right z_node) (get_size x_node) in
  write (get_right x_node) tz;
  //let h2 = get() in
  //let t1' = v_linked_tree (get_left x_node) h2 in
  //let h = get () in
  //assert (fst (Spec.is_wds (v_linked_tree (get_right x_node) h)));
  //assert (sel (get_size x_node) h == Spec.size_of_tree (v_linked_tree ptr h)
  //                                 + Spec.size_of_tree (v_linked_tree (get_right z_node) h) + 1);
  pack_tree (get_right x_node) ptr (get_right z_node) (get_size x_node);
  //let h1 = get () in
  //assert (Spec.size_of_tree (v_linked_tree ptr h1) == Spec.size_of_tree (v_linked_tree ptr h0));
  return (get_right x_node)
*)
//(*)
//#push-options "--ifuel 1 --fuel 2"

//@Trees (rotate*)
#push-options "--fuel 1 --ifuel 1"
let rotate_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    Some? (Spec.rotate_left_wds (v_linked_tree ptr h0))))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_left_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_left_size (v_linked_tree ptr h);
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_right x_node);
  (**) let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  let s1 = sot_wds (get_left x_node) in
  let s2 = sot_wds (get_left z_node) in
  let sx = U.add (U.add s1 s2) one in
  write (get_size z_node) sx;
  let new_subnode = mk_node x (get_left x_node) (get_left z_node) (get_size z_node) in
  let new_node = mk_node z ptr (get_right z_node) (get_size x_node) in
  write (get_right x_node) new_node;
  write ptr new_subnode;
  (**) pack_tree ptr (get_left x_node) (get_left z_node) (get_size z_node);
  (**) pack_tree (get_right x_node) ptr (get_right z_node) (get_size x_node);
  return (get_right x_node)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rotate_right (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    Some? (Spec.rotate_right_wds (v_linked_tree ptr h0))))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_right_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_right_size (v_linked_tree ptr h);
  (**) node_is_not_null ptr;
  (**) let x_node = unpack_tree ptr in
  let x = get_data x_node in
  (**) node_is_not_null (get_left x_node);
  let z_node = unpack_tree (get_left x_node) in
  let z = get_data z_node in
  let s1 = sot_wds (get_right z_node) in
  let s2 = sot_wds (get_right x_node) in
  let sx = U.add (U.add s1 s2) one in
  write (get_size z_node) sx;
  let new_subnode = mk_node x (get_right z_node) (get_right x_node) (get_size z_node) in
  let new_node = mk_node z (get_left z_node) ptr (get_size x_node) in
  write (get_left x_node) new_node;
  write ptr new_subnode;
  (**) pack_tree ptr (get_right z_node) (get_right x_node) (get_size z_node);
  (**) pack_tree (get_left x_node) (get_left z_node) ptr (get_size x_node);
  return (get_left x_node)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rotate_right_left (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires (fun h0 ->
    Some? (Spec.rotate_right_left_wds (v_linked_tree ptr h0))))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_right_left_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_right_left_size (v_linked_tree ptr h);
  assert (Spec.size_of_tree (Spec.get (Spec.rotate_right_left_wds (v_linked_tree ptr h)))
  == Spec.size_of_tree (v_linked_tree ptr h));
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
  let s1 = sot_wds (get_left x_node) in
  let s2 = sot_wds (get_left y_node) in
  let s3 = sot_wds (get_right y_node) in
  let s4 = sot_wds (get_right z_node) in
  let s12 = U.add (U.add s1 s2) one in
  let s34 = U.add (U.add s3 s4) one in
  write (get_size y_node) s12;
  write (get_size z_node) s34;

  let new_x = mk_node x (get_left x_node) (get_left y_node) (get_size y_node) in
  let new_z = mk_node z (get_right y_node) (get_right z_node) (get_size z_node) in
  let new_y = mk_node y ptr (get_right x_node) (get_size x_node) in

  write ptr new_x;
  write (get_right x_node) new_z;
  write (get_left z_node) new_y;

  (**) pack_tree ptr (get_left x_node) (get_left y_node) (get_size y_node);
  (**) pack_tree (get_right x_node) (get_right y_node) (get_right z_node) (get_size z_node);
  (**) pack_tree (get_left z_node) ptr (get_right x_node) (get_size x_node);

  return (get_left z_node)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rotate_left_right (#a: Type) (ptr: t a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 -> Some? (Spec.rotate_left_right_wds (v_linked_tree ptr h0)))
  (ensures (fun h0 ptr' h1 ->
    Spec.rotate_left_right_wds (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
  ))
  =
  let h = get () in
  assert (Spec.size_of_tree (v_linked_tree ptr h) <= c);
  Spec.rotate_left_right_size (v_linked_tree ptr h);
  assert (Spec.size_of_tree (Spec.get (Spec.rotate_left_right_wds (v_linked_tree ptr h)))
  == Spec.size_of_tree (v_linked_tree ptr h));
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
  let s1 = sot_wds (get_left z_node) in
  let s2 = sot_wds (get_left y_node) in
  let s3 = sot_wds (get_right y_node) in
  let s4 = sot_wds (get_right x_node) in
  let s12 = U.add (U.add s1 s2) one in
  let s34 = U.add (U.add s3 s4) one in
  write (get_size y_node) s12;
  write (get_size z_node) s34;

  let new_z = mk_node z (get_left z_node) (get_left y_node) (get_size y_node) in
  let new_x = mk_node x (get_right y_node) (get_right x_node) (get_size z_node) in
  let new_y = mk_node y (get_left x_node) ptr (get_size x_node) in

  write (get_left x_node) new_z;
  write ptr new_x;
  write (get_right z_node) new_y;

  (**) pack_tree (get_left x_node) (get_left z_node) (get_left y_node) (get_size y_node);
  (**) pack_tree ptr (get_right y_node) (get_right x_node) (get_size z_node);
  (**) pack_tree (get_right z_node) (get_left x_node) ptr (get_size x_node);

  return (get_right z_node)
#pop-options

//@AVL (?)
#push-options "--fuel 1 --ifuel 1"
let rec is_balanced (#a: Type) (ptr: t a)
  : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
  (requires fun h0 -> True)
  (ensures (fun h0 b h1 ->
      v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
      Spec.is_balanced (v_linked_tree ptr h0) == b))
  =
  if is_null_t ptr then (
    (**) null_is_leaf ptr;
    return true
  ) else (
    let h = get () in
    Spec.height_lte_size (v_linked_tree ptr h);
    (**) let node = unpack_tree ptr in
    let lh = height (get_left node) in
    let rh = height (get_right node) in

    let lbal = is_balanced(get_left node) in
    let rbal = is_balanced(get_right node) in

    (**) pack_tree ptr (get_left node) (get_right node) (get_size node);
    //rh + 1 >= lh
    //lh + 1 >= rh
    //TODO: will fail when c is set to MAX_UINT64 - 1
    let b1 = U.gte (U.add rh one) lh in
    let b2 = U.gte (U.add lh one) rh in
    let v = (lbal && rbal) && b1 && b2 in
    return v
  )
#pop-options

//@AVL
//#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
#push-options "--fuel 1 --ifuel 1"
let rebalance_avl (#a: Type) (ptr: t a)
  : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
  (requires fun h0 -> True)
  (ensures fun h0 ptr' h1 ->
      Spec.rebalance_avl_wds (v_linked_tree ptr h0) == v_linked_tree ptr' h1)
  =
  admit ();
  let h0 = get () in
  if is_balanced #a ptr then (
    // TODO : fails without the assertion, why?
    // any additional line (h0, h1 or both and the assert) is enough for everything to work
    let h1 = get () in
    assert (v_linked_tree ptr h0 == v_linked_tree ptr h1);
    return ptr
  ) else (

    (**) node_is_not_null ptr;
    (**) let node = unpack_tree ptr in
    Spec.height_lte_size (v_linked_tree ptr h0);

    let lh = height (get_left node) in
    let rh = height (get_right node) in

    if U.gt lh (U.add rh one) then (

      (**) node_is_not_null (get_left node);
      (**) let l_node = unpack_tree (get_left node) in

      let llh = height (get_left l_node) in
      let lrh = height (get_right l_node) in

      (**) pack_tree (get_left node) (get_left l_node) (get_right l_node) (get_size l_node);
      (**) pack_tree ptr (get_left node) (get_right node) (get_size node);

      if U.gt lrh llh then (
        rotate_left_right ptr

      ) else (
        rotate_right ptr
      )

    ) else //(
    if U.gt rh (U.add lh one) then (

        (**) node_is_not_null (get_right node);
        (**) let r_node = unpack_tree (get_right node) in

        let rlh = height (get_left r_node) in
        let rrh = height (get_right r_node) in

        (**) pack_tree (get_right node) (get_left r_node) (get_right r_node) (get_size r_node);
        (**) pack_tree ptr (get_left node) (get_right node) (get_size node);

        if U.gt rlh rrh then (
          rotate_right_left ptr
        ) else (
          rotate_left ptr
        )

      ) else (
        (**) pack_tree ptr (get_left node) (get_right node) (get_size node);
        return ptr
      )
    )
  //)
#pop-options

//let rec insert_avl (#a: Type)
//  (cmp:cmp a) (ptr: t a) (new_data: a)
//  : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
//  (requires fun h0 ->
//    Spec.size_of_tree (v_linked_tree ptr h0) < c /\
//    Spec.is_avl (convert cmp) (v_linked_tree ptr h0))
//  (ensures fun h0 ptr' h1 -> //True
//     //TODO: remove redundancy
//     Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
//     Spec.insert_avl (convert cmp) (v_linked_tree ptr h0) new_data
//     == v_linked_tree ptr' h1)
//  =
//  if is_null_t ptr then (
//    (**) null_is_leaf ptr;
//    (**) let second_leaf = create_leaf () in
//    let sr = malloc one in
//    let node = mk_node new_data ptr second_leaf sr in
//    let new_tree = malloc node in
//    (**) pack_tree new_tree ptr second_leaf sr;
//    return new_tree
//  ) else (
//    (**) let node = unpack_tree ptr in
//    let delta = cmp (get_data node) new_data in
//    if I.gte delta szero then (
//      let new_left = insert_avl cmp (get_left node) new_data in
//      let old_size = read (get_size node) in
//      write (get_size node) (U.add old_size one);
//      let new_node = mk_node (get_data node) new_left (get_right node) (get_size node) in
//      write ptr new_node;
//      (**) pack_tree ptr new_left (get_right node) (get_size node);
//      rebalance_avl ptr
//    )
//    else (
//      let new_right = insert_avl cmp (get_right node) new_data in
//      let old_size = read (get_size node) in
//      write (get_size node) (U.add old_size one);
//      let new_node = mk_node (get_data node) (get_left node) new_right (get_size node) in
//      write ptr new_node;
//      (**) pack_tree ptr (get_left node) new_right (get_size node);
//      rebalance_avl ptr
//    )
//  )

//@AVL
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rec insert_avl2 (#a: Type)
  (r:bool) (cmp:cmp a) (ptr: t a) (new_data: a)
  : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.size_of_tree (v_linked_tree ptr h0) < c /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
     Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
     Spec.insert_avl2 r (convert cmp) (v_linked_tree ptr h0) new_data
     == v_linked_tree ptr' h1 /\
     Spec.is_avl (convert cmp) (v_linked_tree ptr' h1))
  =
  if is_null_t ptr then (
    (**) null_is_leaf ptr;
    (**) let second_leaf = create_leaf () in
    let sr = malloc one in
    let node = mk_node new_data ptr second_leaf sr in
    let new_tree = malloc node in
    (**) pack_tree new_tree ptr second_leaf sr;
    return new_tree
  ) else (
    (**) let node = unpack_tree ptr in
    let delta = cmp (get_data node) new_data in
    if I.eq delta szero then (
      if r then (
        let new_node = mk_node new_data
          (get_left node) (get_right node) (get_size node) in
        write ptr new_node;
        pack_tree ptr
          (get_left node) (get_right node) (get_size node);
        return ptr
      ) else (
        pack_tree ptr
          (get_left node) (get_right node) (get_size node);
        return ptr
      )
    ) else (
      if I.gte delta szero then (
        let old_left_s = sot_wds (get_left node) in
        let new_left = insert_avl2 r cmp (get_left node) new_data in
        let new_left_s = sot_wds new_left in
        let diff = U.sub new_left_s old_left_s in
        let old_size = read (get_size node) in
        write (get_size node) (U.add old_size diff);
        let new_node = mk_node (get_data node) new_left (get_right node) (get_size node) in
        write ptr new_node;
        (**) pack_tree ptr new_left (get_right node) (get_size node);
        rebalance_avl ptr
      ) else (
        let old_right_s = sot_wds (get_right node) in
        let new_right = insert_avl2 r cmp (get_right node) new_data in
        let new_right_s = sot_wds new_right in
        let diff = U.sub new_right_s old_right_s in
        let old_size = read (get_size node) in
        write (get_size node) (U.add old_size diff);
        let new_node = mk_node (get_data node) (get_left node) new_right (get_size node) in
        write ptr new_node;
        (**) pack_tree ptr (get_left node) new_right (get_size node);
        rebalance_avl ptr
      )
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec remove_leftmost_avl (#a: Type0) (cmp:cmp a) (ptr: t a)
  : Steel (t a & a)
  (linked_tree ptr)
  (fun r -> linked_tree (fst r))
  (requires fun h0 ->
    Spec.Node? (v_linked_tree ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 r h1 ->
    Spec.Node? (v_linked_tree ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
    v_linked_tree (fst r) h1
    == fst (Spec.remove_leftmost_avl
      (convert cmp) (v_linked_tree ptr h0)) /\
    snd r == snd (Spec.remove_leftmost_avl
      (convert cmp) (v_linked_tree ptr h0)) /\
    Spec.size_of_tree (v_linked_tree (fst r) h1)
    == Spec.size_of_tree (v_linked_tree ptr h0) - 1 /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0))
  =
  (**) node_is_not_null ptr;
  (**) let node = unpack_tree ptr in
  if is_null_t (get_left node) then (
    let data = get_data node in
    elim_linked_tree_leaf (get_left node);
    free (get_size node);
    free ptr;
    return (get_right node, data)
  ) else (
    (**) not_null_is_node (get_left node);
    let r0 = remove_leftmost_avl cmp (get_left node) in
    let old_size = read (get_size node) in
    write (get_size node) (U.sub old_size one);
    let new_node = mk_node (get_data node)
      (fst r0) (get_right node) (get_size node) in
    write ptr new_node;
    (**) pack_tree ptr
      (fst r0) (get_right node) (get_size node);
    let new_ptr = rebalance_avl ptr in
    return (new_ptr, snd r0)
  )
#pop-options

let cdata = Spec.cdata
let cleft = Spec.cleft
let cright = Spec.cright

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
//#push-options "--fuel 1 --ifuel 1"
let delete_avl_aux0 (#a: Type0)
  (cmp:cmp a) (ptr: t a) (data_to_rm: a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.Node? (v_linked_tree ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
    (convert cmp) (Spec.cdata (v_linked_tree ptr h0)) data_to_rm = 0)
  (ensures fun h0 ptr' h1 ->
    Spec.Node? (v_linked_tree ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
    (convert cmp) (Spec.cdata (v_linked_tree ptr h0)) data_to_rm = 0 /\
    (v_linked_tree ptr' h1
    == Spec.delete_avl_aux0_wo_refinement
      (convert cmp) (v_linked_tree ptr h0) data_to_rm) /\
    Spec.size_of_tree (v_linked_tree ptr' h1)
    == Spec.size_of_tree (v_linked_tree ptr h0) - 1)
  =
  let h00 = get () in
  (**) node_is_not_null ptr;
  (**) let node = unpack_tree ptr in
  if is_null_t (get_left node) && is_null_t (get_right node) then (
    elim_linked_tree_leaf (get_left node);
    free (get_size node);
    free ptr;
    return (get_right node)
  ) else if is_null_t (get_right node) then (
    elim_linked_tree_leaf (get_right node);
    free (get_size node);
    free ptr;
    return (get_left node)
  ) else if is_null_t (get_left node) then (
    elim_linked_tree_leaf (get_left node);
    free (get_size node);
    free ptr;
    return (get_right node)
  ) else (
    let right_node = unpack_tree (get_right node) in
    if is_null_t (get_left right_node) then (
      let y = get_data right_node in
      elim_linked_tree_leaf (get_left right_node);
      free (get_size right_node);
      free (get_right node);
      let sz = read (get_size node) in
      write (get_size node) (U.sub sz one);
      let new_node = mk_node
        y (get_left node) (get_right right_node) (get_size node) in
      write ptr new_node;
      pack_tree ptr
        (get_left node) (get_right right_node) (get_size node);
      return ptr
    ) else (
      pack_tree (get_right node)
        (get_left right_node) (get_right right_node)
        (get_size right_node);
      let h0 = get () in
      let result_spec = hide (Spec.remove_leftmost_avl
        (convert cmp) (v_linked_tree (get_right node) h0)) in
      let result = remove_leftmost_avl cmp (get_right node) in
      assert (snd result == snd (reveal result_spec));
      let sz = read (get_size node) in
      write (get_size node) (U.sub sz one);
      let h1 = get () in
      assert (
       Spec.size_of_tree (v_linked_tree (fst result) h1)
       ==
       Spec.size_of_tree (v_linked_tree (get_right node) h0) - 1);
      assert (U.v (sel (get_size node) h0)
      == Spec.size_of_tree (v_linked_tree (get_left node) h0)
       + Spec.size_of_tree (v_linked_tree (get_right node) h0)
       + 1);
      assert (U.v (sel (get_size node) h0)
      == U.v (sel (get_size node) h1) + 1);

      let new_node = mk_node (snd result)
        (get_left node) (fst result) (get_size node) in
      write ptr new_node;
      let h = get () in
      assert (U.v (sel (get_size node) h)
      == Spec.size_of_tree (v_linked_tree (get_left node) h)
       + Spec.size_of_tree (v_linked_tree (fst result) h)
       + 1);
      pack_tree ptr
        (get_left node) (fst result) (get_size node);
      let orig = hide (v_linked_tree ptr h00) in
      let result_spec = hide (Spec.delete_avl_aux0_wo_refinement
        (convert cmp) (reveal orig) data_to_rm) in
      let h = get () in
      let result = hide (v_linked_tree ptr h) in
      //assert (cdata (reveal result) == cdata (reveal result_spec));
      //assert (cleft (reveal result) == cleft (reveal result_spec));
      //assert (cright (reveal result) == cright (reveal result_spec));
      return ptr
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
let delete_avl_aux1 (#a: Type0)
  (cmp:cmp a) (ptr: t a) (data_to_rm: a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.Node? (v_linked_tree ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
    (convert cmp) (Spec.cdata (v_linked_tree ptr h0)) data_to_rm = 0)
  (ensures fun h0 ptr' h1 ->
    Spec.Node? (v_linked_tree ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
    (convert cmp) (Spec.cdata (v_linked_tree ptr h0)) data_to_rm = 0 /\
    (v_linked_tree ptr' h1
    == Spec.delete_avl_aux1
      (convert cmp) (v_linked_tree ptr h0) data_to_rm) /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr' h1) /\
    Spec.size_of_tree (v_linked_tree ptr' h1)
    == Spec.size_of_tree (v_linked_tree ptr h0) - 1)
  =
  let h0 = get () in
  assert (Spec.is_avl (convert cmp) (
    Spec.delete_avl_aux1
      (convert cmp) (v_linked_tree ptr h0) data_to_rm)
  );
  let ptr = delete_avl_aux0 cmp ptr data_to_rm in
  rebalance_avl ptr
#pop-options

let u_of_bool (b:bool) : x:U.t{U.v x = Spec.int_of_bool b}
= match b with
| true -> one
| false -> zero

#push-options "--fuel 1 --ifuel 1"
let dincr
  (b: bool)
  (ptr: ref U.t)
  : Steel unit
  (vptr ptr) (fun _ -> vptr ptr)
  (requires fun h0 ->
    U.gt (sel ptr h0) zero)
  (ensures fun h0 _ h1 ->
    (let old_value = sel ptr h0 in
    U.gt (sel ptr h0) zero /\
    sel ptr h1 = U.sub old_value (u_of_bool b)))
  =
  if b then (
    let old_value = read ptr in
    write ptr (U.sub old_value one);
    return ()
  ) else (
    return ()
  )


#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec delete_avl_aux (#a: Type0)
  (cmp:cmp a) (ptr: t a) (data_to_rm: a)
  : Steel (t a & bool)
  (linked_tree ptr)
  (fun r -> linked_tree (fst r))
  (requires fun h0 ->
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 r h1 ->
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
    (let r2 = Spec.delete_avl_aux
      (convert cmp) (v_linked_tree ptr h0) data_to_rm in
    v_linked_tree (fst r) h1 == fst r2 /\
    snd r == snd r2) /\
    Spec.is_avl (convert cmp) (v_linked_tree (fst r) h1))
  =
  if is_null_t #a ptr then (
    (**) null_is_leaf ptr;
    let h = get () in
    return (ptr, false)
  ) else (
    (**) let node = unpack_tree ptr in
    let delta = cmp data_to_rm (get_data node) in
    if I.lt delta szero then (
      let h0 = get () in
      let result = delete_avl_aux cmp (get_left node) data_to_rm in
      let h1 = get () in
      dincr (snd result) (get_size node);
      let h1 = get () in
      assert (
      U.v (sel (get_size node) h1)
      ==
      U.v (sel (get_size node) h0)
      - (Spec.int_of_bool (snd result))
      );
      let new_node = mk_node (get_data node)
        (fst result) (get_right node) (get_size node) in
      write ptr new_node;
      pack_tree ptr
        (fst result) (get_right node) (get_size node);
      let ptr = rebalance_avl ptr in
      return (ptr, snd result)
    ) else if I.gt delta szero then (
      let h0 = get () in
      let result = delete_avl_aux cmp (get_right node) data_to_rm in
      dincr (snd result) (get_size node);
      let h1 = get () in
      assert (
      U.v (sel (get_size node) h1)
      ==
      U.v (sel (get_size node) h0)
      - (Spec.int_of_bool (snd result))
      );
      let new_node = mk_node (get_data node)
        (get_left node) (fst result) (get_size node) in
      write ptr new_node;
      pack_tree ptr
        (get_left node) (fst result) (get_size node);
      let ptr = rebalance_avl ptr in
      return (ptr, snd result)
    ) else (
      pack_tree ptr
        (get_left node) (get_right node) (get_size node);
      let ptr = delete_avl_aux1 cmp ptr data_to_rm in
      return (ptr, true)
    )
  )

let delete_avl (#a: Type0)
  (cmp:cmp a) (ptr: t a) (data_to_rm: a)
  : Steel (t a)
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (convert cmp) (v_linked_tree ptr h0) /\
    Spec.delete_avl (convert cmp) (v_linked_tree ptr h0) data_to_rm
    == v_linked_tree ptr' h1 /\
    Spec.is_avl (convert cmp) (v_linked_tree ptr' h1))
  =
  let r = delete_avl_aux cmp ptr data_to_rm in
  fst r
