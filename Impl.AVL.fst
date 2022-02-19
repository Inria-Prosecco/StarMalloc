module Impl.AVL

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

//module Spec = Trees
module U = FStar.UInt64
module I = FStar.Int64
module M = FStar.Math.Lib

open Impl.Core
open Impl.Common
open Impl.Trees
open Impl.Trees.Rotate
open Impl.Trees.Rotate2
open Impl.Trees.Rotate3
open Impl.BST

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@AVL (?)
#push-options "--fuel 1 --ifuel 1"
let rec is_balanced_g (#a: Type) (ptr: t a)
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
    let lh = hot_wdh (get_left node) in
    let rh = hot_wdh (get_right node) in

    let lbal = is_balanced_g (get_left node) in
    let rbal = is_balanced_g (get_right node) in

    (**) pack_tree ptr (get_left node) (get_right node)
      (get_size node) (get_height node);
    //rh + 1 >= lh
    //lh + 1 >= rh
    //TODO: will fail when c is set to MAX_UINT64 - 1
    let b1 = U.gte (U.add rh one) lh in
    let b2 = U.gte (U.add lh one) rh in
    let v = (lbal && rbal) && b1 && b2 in
    return v
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
let is_balanced_spec (#a: Type) (t: Spec.wdm a)
  : bool
  = match t with
  | Spec.Leaf -> true
  | Spec.Node _ left right _ _ ->
      let lh = Spec.hot_wdh left in
      let rh = Spec.hot_wdh right in
      (lh - rh <= 1) && (rh - lh <= 1)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let is_balanced (#a: Type) (ptr: t a)
  : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
  (requires fun h0 -> True)
  (ensures (fun h0 b h1 ->
//      let t = v_linked_tree ptr h0 in
//      (Spec.Node? t /\
//      Spec.is_balanced (Spec.cleft t) /\
//      Spec.is_balanced (Spec.cright t) /\
//      b
//      ==> Spec.is_balanced t) /\
      v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
      is_balanced_spec (v_linked_tree ptr h0) == b))
  =
  if is_null_t ptr then (
    (**) null_is_leaf ptr;
    return true
  ) else (
    let h = get () in
    Spec.height_lte_size (v_linked_tree ptr h);
    (**) let node = unpack_tree ptr in
    let lh = hot_wdh (get_left node) in
    let rh = hot_wdh (get_right node) in

    (**) pack_tree ptr (get_left node) (get_right node)
      (get_size node) (get_height node);
    //rh + 1 >= lh
    //lh + 1 >= rh
    //TODO: will fail when c is set to MAX_UINT64 - 1
    let b1 = U.gte (U.add rh one) lh in
    let b2 = U.gte (U.add lh one) rh in
    let v = b1 && b2 in
    return v
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
//let height_to_node (#a: Type) (t: Spec.wdm a)
//  : Lemma
//  (Spec.height_of_tree t > 0 ==> Spec.Node? t)
//  = ()

let is_balanced_spec_not_null (#a: Type) (t: Spec.wdm a)
  : Lemma
  (not (is_balanced_spec t) ==> Spec.Node? t)
  = ()

let rotate_left_h (#a: Type) (t: Spec.wdm a)
  : Lemma
  (requires (
    let t' = Spec.rotate_left_wdm t in
    Some? t' /\ Spec.Node? (Spec.get t') /\
    Spec.Node? t /\ Spec.Node? (Spec.cright t) /\
    Spec.hot_wdh (Spec.cleft t)
    <= Spec.hot_wdh (Spec.cright (Spec.cright t))
  ))
  (ensures (
    let t' = Spec.get (Spec.rotate_left_wdm t) in
    Spec.hot_wdh t' <= Spec.hot_wdh t
  ))
  = ()

let rotate_right_h (#a: Type) (t: Spec.wdm a)
  : Lemma
  (requires (
    let t' = Spec.rotate_right_wdm t in
    Some? t' /\ Spec.Node? (Spec.get t') /\
    Spec.Node? t /\ Spec.Node? (Spec.cleft t) /\
    Spec.hot_wdh (Spec.cright t)
    <= Spec.hot_wdh (Spec.cleft (Spec.cleft t))
  ))
  (ensures (
    let t' = Spec.get (Spec.rotate_right_wdm t) in
    Spec.hot_wdh t' <= Spec.hot_wdh t
  ))
  = ()

#push-options "--fuel 2"
let rotate_right_left_h (#a: Type) (t: Spec.wdm a)
  : Lemma
  (requires (
    let t' = Spec.rotate_right_left_wdm t in
    Some? t' /\ Spec.Node? (Spec.get t') /\
    Spec.Node? t /\ Spec.Node? (Spec.cright t) /\
    Spec.hot_wdh (Spec.cleft t)
    <= Spec.hot_wdh (Spec.cright (Spec.cright t))
  ))
  (ensures (
    let t' = Spec.get (Spec.rotate_right_left_wdm t) in
    Spec.hot_wdh t' <= Spec.hot_wdh t
  ))
  = ()

let rotate_left_right_h (#a: Type) (t: Spec.wdm a)
  : Lemma
  (requires (
    let t' = Spec.rotate_left_right_wdm t in
    Some? t' /\ Spec.Node? (Spec.get t') /\
    Spec.Node? t /\ Spec.Node? (Spec.cleft t) /\
    Spec.hot_wdh (Spec.cright t)
    <= Spec.hot_wdh (Spec.cleft (Spec.cleft t))
  ))
  (ensures (
    let t' = Spec.get (Spec.rotate_left_right_wdm t) in
    Spec.hot_wdh t' <= Spec.hot_wdh t
  ))
  = ()
#pop-options

#pop-options

//let lemma0 (w x y z: nat)
//  : Lemma
//  (requires
//    w = M.max x y + 1 /\
//    w > (z + 1) /\
//    x > y
//  )
//  (ensures
//    x > z
//  )
//  =
//  assert (M.max x y > z);
//  ()


//@AVL
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
//#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
let rebalance_avl (#a: Type) (ptr: t a)
  : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
  (requires fun h0 -> True)
  (ensures fun h0 ptr' h1 ->
      Spec.rebalance_avl_wdm (v_linked_tree ptr h0) == v_linked_tree ptr' h1)
  =
  //admit ();
  let h0 = get () in
  if is_balanced #a ptr then (
    // TODO : fails without the assertion, why?
    // any additional line (h0, h1 or both and the assert) is enough for everything to work
    let h1 = get () in
    assert (v_linked_tree ptr h0 == v_linked_tree ptr h1);
    return ptr
  ) else (
    is_balanced_spec_not_null (v_linked_tree ptr h0);
    assert (Spec.Node? (v_linked_tree ptr h0));
    (**) node_is_not_null ptr;
    (**) let node = unpack_tree ptr in
    Spec.height_lte_size (v_linked_tree ptr h0);

    let lh = hot_wdh (get_left node) in
    let rh = hot_wdh (get_right node) in

    if U.gt lh (U.add rh one) then (

      (**) node_is_not_null (get_left node);
      (**) let l_node = unpack_tree (get_left node) in

      let llh = hot_wdh (get_left l_node) in
      let lrh = hot_wdh (get_right l_node) in

      (**) pack_tree (get_left node) (get_left l_node) (get_right l_node)
        (get_size l_node) (get_height l_node);
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      let h = get () in
      assert (U.v llh = Spec.hot_wdh (Spec.cleft (Spec.cleft (v_linked_tree ptr h))));
      assert (U.v lrh = Spec.hot_wdh (Spec.cright (Spec.cleft (v_linked_tree ptr h))));
      assert (U.v rh = Spec.hot_wdh (Spec.cright (v_linked_tree ptr h)));
      assert (lh = U.add (umax llh lrh) one);
      assert (U.gt (umax llh lrh) rh);

      if U.gt lrh llh then (
        assert (U.gt lrh rh);
        assume (Spec.is_balanced (Spec.cleft (v_linked_tree ptr h)));
        assert (U.gte llh rh);
        rotate_left_right_h (v_linked_tree ptr h);
        rotate_left_right ptr

      ) else (
        assert (U.gt llh rh);
        rotate_right_h (v_linked_tree ptr h);
        rotate_right ptr
      )

    ) else //(
    if U.gt rh (U.add lh one) then (

      (**) node_is_not_null (get_right node);
      (**) let r_node = unpack_tree (get_right node) in

      let rlh = hot_wdh (get_left r_node) in
      let rrh = hot_wdh (get_right r_node) in

      (**) pack_tree (get_right node) (get_left r_node) (get_right r_node)
        (get_size r_node) (get_height r_node);
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      let h = get () in
      assert (U.v rlh = Spec.hot_wdh (Spec.cleft (Spec.cright (v_linked_tree ptr h))));
      assert (U.v rrh = Spec.hot_wdh (Spec.cright (Spec.cright (v_linked_tree ptr h))));
      assert (U.v lh = Spec.hot_wdh (Spec.cleft (v_linked_tree ptr h)));
      assert (rh = U.add (umax rlh rrh) one);
      assert (U.gt (umax rlh rrh) lh);

      if U.gt rlh rrh then (
        assert (U.gt rlh lh);
        assume (Spec.is_balanced (Spec.cright (v_linked_tree ptr h)));
        assert (U.gte rrh lh);
        rotate_right_left_h (v_linked_tree ptr h);
        rotate_right_left ptr
      ) else (
        assert (U.gt rrh lh);
        rotate_left_h (v_linked_tree ptr h);
        rotate_left ptr
      )

    ) else (
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      return ptr
    )
  )
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
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
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
    Spec.is_avl (convert cmp) (v_linked_tree ptr' h1) /\
    Spec.size_of_tree (v_linked_tree ptr' h1)
    <= Spec.size_of_tree (v_linked_tree ptr h0) + 1)
  =
  admit ();
  if is_null_t ptr then (
    (**) null_is_leaf ptr;
    (**) let second_leaf = create_leaf () in
    let sr = malloc one in
    let hr = malloc one in
    let node = mk_node new_data ptr second_leaf sr hr in
    let new_tree = malloc node in
    (**) pack_tree new_tree ptr second_leaf sr hr;
    return new_tree
  ) else (
    (**) let node = unpack_tree ptr in
    let delta = cmp (get_data node) new_data in
    if I.eq delta szero then (
      if r then (
        let new_node = mk_node new_data
          (get_left node) (get_right node)
          (get_size node) (get_height node) in
        write ptr new_node;
        pack_tree ptr
          (get_left node) (get_right node)
          (get_size node) (get_height node);
        return ptr
      ) else (
        pack_tree ptr
          (get_left node) (get_right node)
          (get_size node) (get_height node);
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
        let height_new_left = hot_wdh new_left in
        let height_right = hot_wdh (get_right node) in
        let new_height = umax height_new_left height_right in
        write (get_height node) (U.add new_height one);
        let new_node = mk_node (get_data node) new_left (get_right node)
          (get_size node) (get_height node) in
        write ptr new_node;
        (**) pack_tree ptr new_left (get_right node)
          (get_size node) (get_height node);
        let h = get () in
        Spec.height_lte_size (v_linked_tree ptr h);
        rebalance_avl ptr
      ) else (
        let old_right_s = sot_wds (get_right node) in
        let new_right = insert_avl2 r cmp (get_right node) new_data in
        let new_right_s = sot_wds new_right in
        let diff = U.sub new_right_s old_right_s in
        let old_size = read (get_size node) in
        write (get_size node) (U.add old_size diff);
        let height_left = hot_wdh (get_left node) in
        let height_new_right = hot_wdh new_right in
        let new_height = umax height_left height_new_right in
        write (get_height node) (U.add new_height one);
        let new_node = mk_node (get_data node) (get_left node) new_right
          (get_size node) (get_height node) in
        write ptr new_node;
        (**) pack_tree ptr (get_left node) new_right
          (get_size node) (get_height node);
        let h = get () in
        Spec.height_lte_size (v_linked_tree ptr h);
        rebalance_avl ptr
      )
    )
  )
#pop-options

(*)
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
inline_for_extraction noextract
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
#pop-options


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
#pop-options

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
