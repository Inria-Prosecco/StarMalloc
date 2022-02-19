module Impl.BST

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

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

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
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      return true
    end else if I.lt delta szero then begin
      let b = member cmp (get_left node) v in
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
      return b
    end else begin
      let b = member cmp (get_right node) v in
      (**) pack_tree ptr (get_left node) (get_right node)
        (get_size node) (get_height node);
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

inline_for_extraction noextract
let umax (x y: U.t) : U.t
  = if U.gt x y then x else y

(*)
//@BST
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
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
  let h = get () in
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
      if I.gt delta szero then (
        let old_left_s = sot_wds (get_left node) in
        let new_left = insert_bst2 r cmp (get_left node) new_data in
        let new_left_s = sot_wds new_left in
        //assert (U.lte old_left_s new_left_s);
        let diff = U.sub new_left_s old_left_s in
        let old_size = read (get_size node) in
        write (get_size node) (U.add old_size diff);
        let height_new_left = hot_wdh new_left in
        let height_right = hot_wdh (get_right node) in
        Spec.height_lte_size (v_linked_tree ptr h);
        let new_height = umax height_new_left height_right in
        write (get_height node) (U.add new_height one);
        let new_node = mk_node (get_data node) new_left (get_right node)
          (get_size node) (get_height node) in
        write ptr new_node;
        (**) pack_tree ptr new_left (get_right node)
          (get_size node) (get_height node);
        return ptr
      ) else (
        let old_right_s = sot_wds (get_right node) in
        let new_right = insert_bst2 r cmp (get_right node) new_data in
        let new_right_s = sot_wds new_right in
        //assert (U.lte old_left_s new_left_s);
        let diff = U.sub new_right_s old_right_s in
        let old_size = read (get_size node) in
        write (get_size node) (U.add old_size diff);
        let height_left = hot_wdh (get_left node) in
        let height_new_right = hot_wdh new_right in
        Spec.height_lte_size (v_linked_tree ptr h);
        let new_height = umax height_left height_new_right in
        write (get_height node) (U.add new_height one);
        let new_node = mk_node (get_data node) (get_left node) new_right
          (get_size node) (get_height node) in
        write ptr new_node;
        (**) pack_tree ptr (get_left node) new_right
          (get_size node) (get_height node);
        return ptr
      )
    )
  )
#pop-options
