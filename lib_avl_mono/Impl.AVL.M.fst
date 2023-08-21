module Impl.AVL.M

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
module I = FStar.Int64

open Impl.Core
open Impl.Common
open Impl.Trees.Types
open Impl.Trees.M
open Impl.Trees.Rotate.M
open Impl.Trees.Rotate2.M
open Impl.Trees.Rotate3.M
open Impl.BST.M

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

//@AVL
#push-options "--fuel 1 --ifuel 1"
let rec is_balanced_global (ptr: t)
  : Steel bool (linked_tree p ptr) (fun _ -> linked_tree p ptr)
  (requires fun h0 -> True)
  (ensures (fun h0 b h1 ->
      v_linked_tree p ptr h0 == v_linked_tree p ptr h1 /\
      Spec.is_balanced_global (v_linked_tree p ptr h0) == b))
  =
  if is_null_t ptr then (
    (**) null_is_leaf p ptr;
    return true
  ) else (
    let h = get () in
    Spec.height_lte_size (v_linked_tree p ptr h);
    (**) let node = unpack_tree p ptr in
    let lh = hot_wdh (get_left node) in
    let rh = hot_wdh (get_right node) in

    let lbal = is_balanced_global (get_left node) in
    let rbal = is_balanced_global (get_right node) in

    (**) pack_tree p ptr (get_left node) (get_right node)
      (get_size node) (get_height node);
    //rh + 1 >= lh
    //lh + 1 >= rh
    //TODO: will fail when c is set to MAX_UINT64 - 1
    //does not fail as lh, rh < height of the whole tree
    let b1 = U.gte (U.add rh one) lh in
    let b2 = U.gte (U.add lh one) rh in
    let v = (lbal && rbal) && b1 && b2 in
    return v
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
let is_balanced_local (ptr: t)
  : Steel bool (linked_tree p ptr) (fun _ -> linked_tree p ptr)
  (requires fun h0 -> True)
  (ensures (fun h0 b h1 ->
      v_linked_tree p ptr h0 == v_linked_tree p ptr h1 /\
      Spec.is_balanced_local (v_linked_tree p ptr h0) == b))
  =
  if is_null_t ptr then (
    (**) null_is_leaf p ptr;
    return true
  ) else (
    let h = get () in
    Spec.height_lte_size (v_linked_tree p ptr h);
    (**) let node = unpack_tree p ptr in
    let lh = hot_wdh (get_left node) in
    let rh = hot_wdh (get_right node) in

    (**) pack_tree p ptr (get_left node) (get_right node)
      (get_size node) (get_height node);
    //rh + 1 >= lh
    //lh + 1 >= rh
    //TODO: will fail when c is set to MAX_UINT64 - 1
    //does not fail as lh, rh < height of the whole tree
    let b1 = U.gte (U.add rh one) lh in
    let b2 = U.gte (U.add lh one) rh in
    let v = b1 && b2 in
    return v
  )
#pop-options

//@AVL
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rebalance_avl (ptr: t)
  : Steel t (linked_tree p ptr) (fun ptr' -> linked_tree p ptr')
  (requires fun h0 ->
    Spec.Node? (v_linked_tree p ptr h0)
    ==>
    Spec.is_avl (convert cmp) (Spec.cleft (v_linked_tree p ptr h0)) /\
    Spec.is_avl (convert cmp) (Spec.cright (v_linked_tree p ptr h0)))
  (ensures fun h0 ptr' h1 ->
    Spec.rebalance_avl (v_linked_tree p ptr h0) == v_linked_tree p ptr' h1)
    //Spec.is_avl (convert cmp) (v_linked_tree ptr' h1))
  =
  let h0 = get () in
  if is_balanced_local ptr then (
    // TODO : fails without the assertion, why?
    // any additional line (h0, h1 or both and the assert) is enough for everything to work
    let h1 = get () in
    assert (v_linked_tree p ptr h0 == v_linked_tree p ptr h1);
    return ptr
  ) else (
    Spec.not_balanced_is_not_null (v_linked_tree p ptr h0);
    assert (Spec.Node? (v_linked_tree p ptr h0));
    (**) node_is_not_null p ptr;
    (**) let node = unpack_tree p ptr in
    Spec.height_lte_size (v_linked_tree p ptr h0);

    let lh = hot_wdh (get_left node) in
    let rh = hot_wdh (get_right node) in

    if U.gt lh (U.add rh one) then (

      (**) node_is_not_null p (get_left node);
      (**) let l_node = unpack_tree p (get_left node) in

      let llh = hot_wdh (get_left l_node) in
      let lrh = hot_wdh (get_right l_node) in

      (**) pack_tree p (get_left node) (get_left l_node) (get_right l_node)
        (get_size l_node) (get_height l_node);
      (**) pack_tree p ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      let h = get () in
      assert (v_linked_tree p ptr h == v_linked_tree p ptr h0);
      assert (Spec.is_wdm (v_linked_tree p ptr h0));
      assert (Spec.is_wdm (Spec.cleft (v_linked_tree p ptr h0)));
      assert (Spec.is_wdm (Spec.cleft (Spec.cleft (v_linked_tree p ptr h0))));
      assert (Spec.is_wdm (Spec.cright (Spec.cleft (v_linked_tree p ptr h0))));
      assert (Spec.is_wdm (Spec.cright (v_linked_tree p ptr h0)));
      assert (U.v llh = Spec.hot_wdh (Spec.cleft (Spec.cleft (v_linked_tree p ptr h0))));
      assert (U.v lrh = Spec.hot_wdh (Spec.cright (Spec.cleft (v_linked_tree p ptr h0))));
      assert (U.v rh = Spec.hot_wdh (Spec.cright (v_linked_tree p ptr h0)));
      assert (lh = U.add (umax llh lrh) one);
      assert (U.gt (umax llh lrh) rh);

      if U.gt lrh llh then (
        assert (U.gt lrh rh);
        assert (U.gte llh rh);
        Spec.rotate_left_right_height (v_linked_tree p ptr h0);
        rotate_left_right ptr

      ) else (
        assert (U.gt llh rh);
        Spec.rotate_right_height (v_linked_tree p ptr h0);
        rotate_right ptr
      )

    ) else //(
    if U.gt rh (U.add lh one) then (

      (**) node_is_not_null p (get_right node);
      (**) let r_node = unpack_tree p (get_right node) in

      let rlh = hot_wdh (get_left r_node) in
      let rrh = hot_wdh (get_right r_node) in

      (**) pack_tree p (get_right node) (get_left r_node) (get_right r_node)
        (get_size r_node) (get_height r_node);
      (**) pack_tree p ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      let h = get () in
      assert (v_linked_tree p ptr h == v_linked_tree p ptr h0);
      assert (Spec.is_wdm (Spec.cright (v_linked_tree p ptr h0)));
      assert (Spec.is_wdm (Spec.cleft (Spec.cright (v_linked_tree p ptr h0))));
      assert (Spec.is_wdm (Spec.cright (Spec.cright (v_linked_tree p ptr h0))));
      assert (Spec.is_wdm (Spec.cleft (v_linked_tree p ptr h0)));
      assert (U.v rlh = Spec.hot_wdh (Spec.cleft (Spec.cright (v_linked_tree p ptr h0))));
      assert (U.v rrh = Spec.hot_wdh (Spec.cright (Spec.cright (v_linked_tree p ptr h0))));
      assert (U.v lh = Spec.hot_wdh (Spec.cleft (v_linked_tree p ptr h0)));
      assert (rh = U.add (umax rlh rrh) one);
      assert (U.gt (umax rlh rrh) lh);

      if U.gt rlh rrh then (
        assert (U.gt rlh lh);
        assert (U.gte rrh lh);
        Spec.rotate_right_left_height (v_linked_tree p ptr h0);
        rotate_right_left ptr
      ) else (
        assert (U.gt rrh lh);
        Spec.rotate_left_height (v_linked_tree p ptr h0);
        rotate_left ptr
      )

    ) else (
      (**) pack_tree p ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      return ptr
    )
  )
#pop-options

//@AVL
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec insert_avl
  (f1: f_malloc) (f2: f_free)
  (r:bool) (ptr: t) (new_data: data)
  : Steel t (linked_tree p ptr) (fun ptr' -> linked_tree p ptr')
  (requires fun h0 ->
    Spec.size_of_tree (v_linked_tree p ptr h0) < c /\
    Spec.height_of_tree (v_linked_tree p ptr h0) < c /\
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0))

  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0) /\
    Spec.insert_avl r (convert cmp) (v_linked_tree p ptr h0) new_data
    == v_linked_tree p ptr' h1)
  =
  //let h0 = get () in
  //let t1 = hide (v_linked_tree ptr h0) in
  //assert (Spec.size_of_tree (reveal t1) < c);
  //Spec.height_lte_size (v_linked_tree ptr h0);
  //let height_tree = hide (Spec.height_of_tree (reveal t1)) in
  //assert (reveal height_tree < c);
  //let t2 = hide (Spec.insert_avl
  //  r (convert cmp) (reveal t1) new_data) in
  // TODO: this fails, is this a normalization bug?
  //assert (
  //  Spec.size_of_tree (reveal t2)
  //  <= Spec.size_of_tree (reveal t1) + 1);
  //assert (Spec.height_of_tree t2
  //  <= Spec.height_of_tree t1 + 1);

  if is_null_t ptr then (
    (**) null_is_leaf p ptr;
    elim_linked_tree_leaf p ptr;
    create_tree f1 f2 new_data
  ) else (
    (**) let node = unpack_tree p ptr in
    let delta = cmp (get_data node) new_data in
    if I.eq delta szero then (
      if r then (
        let new_node = mk_node new_data
          (get_left node) (get_right node)
          (get_size node) (get_height node) in
        write ptr new_node;
        pack_tree p ptr
          (get_left node) (get_right node)
          (get_size node) (get_height node);
        return ptr
      ) else (
        pack_tree p ptr
          (get_left node) (get_right node)
          (get_size node) (get_height node);
        return ptr
      )
    ) else if I.gt delta szero then (
      let h0 = get () in
      let new_left = insert_avl f1 f2 r (get_left node) new_data in
      let h1 = get () in
      assert (v_linked_tree p new_left h1
      == Spec.insert_avl r (convert cmp)
        (v_linked_tree p (get_left node) h0) new_data);
      Spec.insert_lemma r (convert cmp)
        (v_linked_tree p (get_left node) h0) new_data;
      assert (Spec.size_of_tree (v_linked_tree p new_left h1)
      <= Spec.size_of_tree (v_linked_tree p (get_left node) h0) + 1);
      assert (Spec.height_of_tree (v_linked_tree p new_left h1)
      <= Spec.height_of_tree (v_linked_tree p (get_left node) h0) + 1);
      let new_ptr = merge_tree_no_alloc
        (get_data node) new_left (get_right node)
        ptr in
      rebalance_avl new_ptr
    ) else (
      let h0 = get () in
      let new_right = insert_avl f1 f2 r (get_right node) new_data in
      let h1 = get () in
      assert (v_linked_tree p new_right h1
      == Spec.insert_avl r (convert cmp)
        (v_linked_tree p (get_right node) h0) new_data);
      Spec.insert_lemma r (convert cmp)
        (v_linked_tree p (get_right node) h0) new_data;
      assert (Spec.size_of_tree (v_linked_tree p new_right h1)
      <= Spec.size_of_tree (v_linked_tree p (get_right node) h0) + 1);
      assert (Spec.height_of_tree (v_linked_tree p new_right h1)
      <= Spec.height_of_tree (v_linked_tree p (get_right node) h0) + 1);
      let new_ptr = merge_tree_no_alloc
        (get_data node) (get_left node) new_right
        ptr in
      rebalance_avl new_ptr
    )
  )
#pop-options

noeq
type result =
  { ptr: t; data: data}

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec remove_leftmost_avl
  (f1: f_malloc) (f2: f_free)
  (ptr: t)
  : Steel result
  (linked_tree p ptr)
  (fun r -> linked_tree p r.ptr)
  (requires fun h0 ->
    Spec.Node? (v_linked_tree p ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0))
  (ensures fun h0 r h1 ->
    Spec.Node? (v_linked_tree p ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0) /\
    v_linked_tree p r.ptr h1
    == fst (Spec.remove_leftmost_avl
      (convert cmp) (v_linked_tree p ptr h0)) /\
    r.data == snd (Spec.remove_leftmost_avl
      (convert cmp) (v_linked_tree p ptr h0)) /\
    Spec.size_of_tree (v_linked_tree p r.ptr h1)
    == Spec.size_of_tree (v_linked_tree p ptr h0) - 1 /\
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0))
  =
  (**) node_is_not_null p ptr;
  (**) let node = unpack_tree p ptr in
  if is_null_t (get_left node) then (
    let data = get_data node in
    elim_linked_tree_leaf p (get_left node);
    f2 ptr;
    return {ptr = get_right node; data}
  ) else (
    (**) not_null_is_node p (get_left node);
    let r0 = remove_leftmost_avl f1 f2 (get_left node) in
    let new_ptr = merge_tree_no_alloc
      (get_data node) r0.ptr (get_right node)
      ptr in
    let new_ptr = rebalance_avl new_ptr in
    return {ptr = new_ptr; data=r0.data}
  )
#pop-options

let cdata = Spec.cdata
let cleft = Spec.cleft
let cright = Spec.cright
let csize = Spec.csize
let cheight = Spec.cheight

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
//#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
let delete_avl_aux0
  (f1: f_malloc) (f2: f_free)
  (ptr: t) (data_to_rm: data)
  : Steel t
  (linked_tree p ptr)
  (fun ptr' -> linked_tree p ptr')
  (requires fun h0 ->
    Spec.Node? (v_linked_tree p ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0) /\
    (convert cmp) (Spec.cdata (v_linked_tree p ptr h0)) data_to_rm = 0)
  (ensures fun h0 ptr' h1 ->
    Spec.Node? (v_linked_tree p ptr h0) /\
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0) /\
    (convert cmp) (Spec.cdata (v_linked_tree p ptr h0)) data_to_rm = 0 /\
    v_linked_tree p ptr' h1
    == Spec.delete_avl_aux0
      (convert cmp) (v_linked_tree p ptr h0) data_to_rm)
  =
  (**) node_is_not_null p ptr;
  (**) let node = unpack_tree p ptr in
  if is_null_t (get_right node) then (
    elim_linked_tree_leaf p (get_right node);
    f2 ptr;
    return (get_left node)
  ) else if is_null_t (get_left node) then (
    elim_linked_tree_leaf p (get_left node);
    f2 ptr;
    return (get_right node)
  ) else (
    not_null_is_node p (get_right node);
    let r0 = remove_leftmost_avl f1 f2 (get_right node) in
    let new_ptr = merge_tree_no_alloc r0.data
      (get_left node) r0.ptr
      ptr in
    let new_ptr = rebalance_avl new_ptr in
    return new_ptr
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let rec delete_avl
  (f1: f_malloc) (f2: f_free)
  (ptr: t) (data_to_rm: data)
  : Steel t (linked_tree p ptr) (fun ptr' -> linked_tree p ptr')
  (requires fun h0 ->
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (convert cmp) (v_linked_tree p ptr h0) /\
    Spec.delete_avl (convert cmp) (v_linked_tree p ptr h0) data_to_rm
    == v_linked_tree p ptr' h1)
  =
  if is_null_t ptr then (
    (**) null_is_leaf p ptr;
    return ptr
  ) else (
    (**) let node = unpack_tree p ptr in
    let delta = cmp data_to_rm (get_data node) in
  if I.eq delta szero then (
    pack_tree p ptr
      (get_left node) (get_right node)
      (get_size node) (get_height node);
    let ptr = delete_avl_aux0 f1 f2 ptr data_to_rm in
    return ptr
  ) else if I.lt delta szero then (
    let h0 = get () in
    let new_left = delete_avl f1 f2 (get_left node) data_to_rm in
    let h1 = get () in
    assert (v_linked_tree p new_left h1
    == Spec.delete_avl (convert cmp)
      (v_linked_tree p (get_left node) h0) data_to_rm);
    Spec.delete_lemma (convert cmp)
      (v_linked_tree p (get_left node) h0) data_to_rm;
    assert (Spec.size_of_tree (v_linked_tree p new_left h1)
    <= Spec.size_of_tree (v_linked_tree p (get_left node) h0));
    assert (Spec.height_of_tree (v_linked_tree p new_left h1)
    <= Spec.height_of_tree (v_linked_tree p (get_left node) h0));
    let new_ptr = merge_tree_no_alloc
      (get_data node) new_left (get_right node)
      ptr in
    rebalance_avl new_ptr
  ) else (
    let h0 = get () in
    let new_right = delete_avl f1 f2 (get_right node) data_to_rm in
    let h1 = get () in
    assert (v_linked_tree p new_right h1
    == Spec.delete_avl (convert cmp)
      (v_linked_tree p (get_right node) h0) data_to_rm);
    Spec.delete_lemma (convert cmp)
      (v_linked_tree p (get_right node) h0) data_to_rm;
    assert (Spec.size_of_tree (v_linked_tree p new_right h1)
    <= Spec.size_of_tree (v_linked_tree p (get_right node) h0));
    assert (Spec.height_of_tree (v_linked_tree p new_right h1)
    <= Spec.height_of_tree (v_linked_tree p (get_right node) h0));
    let new_ptr = merge_tree_no_alloc
      (get_data node) (get_left node) new_right
      ptr in
    rebalance_avl new_ptr
  ))
