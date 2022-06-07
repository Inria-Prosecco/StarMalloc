module Impl.Test.Mono

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
module I64 = FStar.Int64
module Impl = Impl.Mono

unfold let a = U.t & U.t

let compare (x y: a) : I64.t
  =
  let x = fst x in
  let y = fst y in
  if U.gt x y then 1L
  else if U.eq x y then 0L
  else -1L

let mk_node = Impl.mk_node
let create_leaf = Impl.create_leaf
let create_tree = Impl.create_tree
let merge_tree  = Impl.merge_tree
let insert_avl = Impl.insert_avl
let delete_avl = Impl.delete_avl

let sot_wds     = Impl.sot_wds
let hot_wdh     = Impl.hot_wdh
let member = Impl.member

let main (v: a) : SteelT U.t
  emp (fun _ -> emp)
  =
  let ptr = create_tree v in
  let s = sot_wds ptr in
  sladmit ();
  return s


(*)
module Impl.Test.Mono

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
module I64 = FStar.Int64

//let a = U.t & U.t
let a = Impl.Trees.M.a

let compare (x y: a) : I64.t
  =
  //let x = fst x in
  //let y = fst y in
  if U.gt x y then 1L
  else if U.eq x y then 0L
  else -1L

//let a = Impl.Trees.M.a
//let a = Impl.Trees.M.a
let t = Impl.Core.t
let linked_tree = Impl.Core.linked_tree
let unpack_tree = Impl.Trees.M.unpack_tree
//let pack_tree = Impl.Core.pack_tree #_

let create_leaf = Impl.Trees.M.create_leaf
let create_tree = Impl.Trees.M.create_tree

inline_for_extraction noextract
let sot_wds     = Impl.Trees.M.sot_wds
noextract
let hot_wdh     = Impl.Trees.M.hot_wdh

inline_for_extraction noextract
let merge_tree  = Impl.Mono.merge_tree

inline_for_extraction noextract
let get_left = Impl.Core.get_left #a
inline_for_extraction noextract
let get_right = Impl.Core.get_right #a
inline_for_extraction noextract
let get_size = Impl.Core.get_size #a
inline_for_extraction noextract
let get_data = Impl.Core.get_data #a
inline_for_extraction noextract
let get_height = Impl.Core.get_height #a


#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let main3 ()
  : Steel U.t
  emp (fun r_n -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
  =
  let ptr = Impl.Trees.M.create_tree 1UL in
 // let node = Impl.Core.unpack_tree ptr in
 // Impl.Core.pack_tree ptr
 //   (get_left node) (get_right node)
 //   (get_size node) (get_height node);
  let h = Impl.Trees.M.sot_wds ptr in
  sladmit ();
  return 1UL



(*)
open Map.M


(* stdlib *)
let rotate_left = Impl.Mono.rotate_left
let rotate_right = Impl.Mono.rotate_right
let rotate_right_left = Impl.Mono.rotate_right_left
let rotate_left_right = Impl.Mono.rotate_left_right
let is_balanced_local = Impl.Mono.is_balanced_local
let rebalance_avl = Impl.Mono.rebalance_avl

let sot_wds     = Impl.Trees.M.sot_wds
let member     = Map.M.mem
(*)
// will be useful later? if so, null or null_t?
//inline_for_extraction noextract
//let null = Steel.Reference.null
inline_for_extraction noextract
let is_null_t = Impl.Core.is_null_t #a

inline_for_extraction noextract
let mk_node = Impl.Core.mk_node #a

(* not inlined *)

//inline_for_extraction
//noextract
inline_for_extraction
let insert_avl = Map.M.insert
//inline_for_extraction
//noextract
inline_for_extraction
let delete_avl = Map.M.delete
//noextract
inline_for_extraction
let member     = Map.M.mem

let destruct_linked_tree_leaf (ptr: t a) : Steel unit
  (linked_tree ptr) (fun _ -> emp)
  (requires fun _ -> is_null_t ptr)
  (ensures fun _ _ _ -> True)
  = sladmit ()

//inline_for_extraction
let rec destruct (ptr: t a) : Steel unit
  (linked_tree ptr) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  sladmit ()
  (*)
  if is_null_t ptr then (
    destruct_linked_tree_leaf ptr
  ) else (
    let n = unpack_tree ptr in
    destruct (get_left n);
    destruct (get_right n);
    free (get_size n);
    free ptr
  )*)


//let main ()
//  : Steel U32.t
//  (emp)
//  (fun _ -> emp)
//  (requires fun _ -> True)
//  (ensures fun _ _ _-> True)
//  =
//  let ptr = create_tree val1 in
//  let ptr = append_left ptr val2 in
//  let b = member ptr val1 in
//  let vr = if b then val42 else val0 in
//  destruct ptr;
//  return (fst vr)

//let main2 ()
//  : Steel U64.t
//  (emp)
//  (fun n -> emp)
//  (requires fun _ -> True)
//  (ensures fun _ _ _-> True)
//  =
//  let ptr = create_leaf () in
//  let ptr = append_right ptr val1 in
//  let ptr = append_right ptr val2 in
//  let ptr = append_right ptr val3 in
//  let h = height ptr in
//  destruct ptr;
//  h


let compare_is_cmp () : Lemma
(
  (forall x. I64.eq (compare x x) I64.zero) /\
  (forall x y. I64.gt (compare x y) I64.zero
                 <==> I64.lt (compare y x) I64.zero) /\
  (forall x  y z. I64.gte (compare x y) I64.zero /\
                         I64.gte (compare y z) I64.zero ==>
                         I64.gte (compare x z) I64.zero)
) = ()

//let main3 ()
//  : Steel U32.t
//  emp (fun r_n -> emp)
//  (requires fun _ -> True)
//  (ensures fun _ _ _-> True)
//  =
//  let ptr = create_leaf () in
//  let ptr = append_left ptr val0 in
//  let ptr = append_right ptr val1 in
//  let ptr = insert_avl compare ptr val3 in
//  //let h = get () in
//  //compare_is_cmp ();
//  //assert (Trees.is_bst (P1.convert compare) (NTreeC3.v_linked_tree ptr h));
//  let ptr = insert_bst compare ptr val2 in
//  //let h = get () in
//  //assert (Trees.is_bst (P1.convert compare) (NTreeC3.v_linked_tree ptr h));
//  let h = sot_wds ptr in
//  let b = member ptr val3 in
//  let vr = if b then val42 else val0 in
//  destruct ptr;
//  return (fst vr)

//let main4()
//  : Steel U32.t
//  emp (fun _ -> emp)
//  (requires fun _ -> True)
//  (ensures fun _ _ _ -> True)
//  =
//  let ptr = create_tree val3 in
//  let valn1 = 2ul, 1729ul in
//  let valn2 = 2ul, 42ul in
//  // toggling this flag allow one to check
//  // whether the r arg of insert_bst2 is taken into account
//  let f = true in
//  let ptr = insert_avl f compare ptr valn1 in
//  let ptr = insert_avl f compare ptr valn2 in
//  assert (I64.eq (compare valn1 valn2) I64.zero);
//  let b = member compare ptr valn2 in
//  let vr = if b then val42 else val0 in
//  destruct ptr;
//  return (fst vr)

#push-options "--z3rlimit 50"
let rec main5_aux (ptr: t a) (v: a)
  : Steel (t a)
  (linked_tree ptr) (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.is_avl (Impl.convert compare) (Impl.v_linked_tree ptr h0)
  )
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (Impl.convert compare) (Impl.v_linked_tree ptr' h1)
  )
  =
  if U64.eq (fst v) zero then (
    let h = get () in
    return ptr
  ) else (
    let h = get () in
    assume (Spec.size_of_tree (Impl.v_linked_tree ptr h) < 1000000000);
    assume (Spec.height_of_tree (Impl.v_linked_tree ptr h) < 1000000000);
    assume (U64.gt (fst v) zero);
    let ptr' = insert_avl true compare ptr v in
    let v' = U64.sub (fst v) one in
    let v'' = (v', snd v) in
    main5_aux ptr' v''
  )
#pop-options

(*)
let main5 (x: a)
  : Steel (t a)
  emp (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  let ptr = create_leaf () in
  main5_aux ptr x

let rec main6_aux (ptr: t a) (v: a) (check: bool)
  : Steel a
  (linked_tree ptr) (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_avl (Impl.convert compare) (Impl.v_linked_tree ptr h0))
  (ensures fun h0 v' h1 ->
    Spec.is_avl (Impl.convert compare) (Impl.v_linked_tree ptr h0) /\
    Impl.v_linked_tree ptr h0 == Impl.v_linked_tree ptr h1)
  =
  if I64.eq v zero then (
    return zero
  ) else (
    let b = member compare ptr v in
    if (b = check) then (
      assume (I64.gt v zero);
      let v' = I64.sub v one in
      main6_aux ptr v' check
    ) else (
      return v
    )
  )

#push-options "--z3rlimit 50"
let rec main7_aux (ptr: t a) (v: a)
  : Steel (t a)
  (linked_tree ptr) (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.is_avl (Impl.convert compare) (Impl.v_linked_tree ptr h0)
  )
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (Impl.convert compare) (Impl.v_linked_tree ptr' h1)
  )
  =
  if I64.eq v zero then (
    let h = get () in
    return ptr
  ) else (
    let h = get () in
    let ptr' = delete_avl compare ptr v in
    assume (I64.gt v zero);
    let v' = I64.sub v one in
    main7_aux ptr' v'
  )
#pop-options

let rec main8_aux (v: I64.t)
  : SteelT (option I64.t)
  emp (fun _ -> emp)
  =
  if I64.eq v zero then (
    return None
  ) else (
    return (Some v)
  )
