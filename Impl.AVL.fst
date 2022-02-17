module Impl.AVL

open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

//module Spec = Trees
module U = FStar.UInt64
module I = FStar.Int64

open Impl.Core
open Impl.Common
open Impl.Trees
open Impl.Trees.Rotate
open Impl.BST

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

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
