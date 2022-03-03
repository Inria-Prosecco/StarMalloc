module P1_UInt32

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I64 = FStar.Int64
//open NTreeC3
//open P1

let t = Impl.Core.t
let linked_tree = Impl.Core.linked_tree



let a = U64.t

//inline_for_extraction noextract
let one = Impl.Common.one
//inline_for_extraction noextract
let zero = Impl.Common.zero

let val0 = 0UL
let val1 = 1UL
let val2 = 2UL
let val3 = 3UL
let val4 = 4UL
let val42 = 42UL
let compare (x y: U64.t) : I64.t
  =
  if U64.gt x y then 1L
  else if U64.eq x y then 0L
  else -1L

//let a = (U32.t & U32.t)
//let val0 = 0ul, 0ul
//let val1 = 1ul, 1ul
//let val2 = 2ul, 2ul
//let val3 = 3ul, 3ul
//let val4 = 4ul, 4ul
//let val42 = 42ul, 42ul
//let compare (x y: a) : I64.t
//  =
//  let x = fst x in
//  let y = fst y in
//  if U32.gt x y then 1L
//  else if U32.eq x y then 0L
//  else -1L

inline_for_extraction noextract
let get_left = Impl.Core.get_left #a
inline_for_extraction noextract
let get_right = Impl.Core.get_right #a
inline_for_extraction noextract
let get_size = Impl.Core.get_size #a
inline_for_extraction noextract
let get_data = Impl.Core.get_data #a

// will be useful later? if so, null or null_t?
//inline_for_extraction noextract
//let null = Steel.Reference.null
inline_for_extraction noextract
let is_null_t = Impl.Core.is_null_t #a

inline_for_extraction noextract
let mk_node = Impl.Core.mk_node #a

(* not inlined *)
let unpack_tree = Impl.Core.unpack_tree #a

(* stdlib *)
//let append_left = P1.append_left #a
//let append_right = P1.append_right #a
//let insert_bst = P1.insert_bst #a
//let insert_avl = Impl.insert_avl #a
let create_leaf = Impl.create_leaf #a
let create_tree = Impl.create_tree #a
let merge_tree  = Impl.merge_tree #a
let sot_wds     = Impl.sot_wds #a
let hot_wdh     = Impl.hot_wdh #a
let member      = Impl.member #a
//let insert_bst2 = Impl.insert_bst2 #a
let rotate_left = Impl.rotate_left #a
let rotate_right = Impl.rotate_right #a
let rotate_right_left = Impl.rotate_right_left #a
let rotate_left_right = Impl.rotate_left_right #a
let is_balanced = Impl.is_balanced #a
let rebalance_avl = Impl.rebalance_avl #a
let insert_avl = Impl.insert_avl #a
let delete_avl = Impl.delete_avl #a

(*
let one ()
  : Steel (ref nat)
  (emp)
  (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  let v = 1 + 1 in
  let r = malloc v in r
*)

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
  if U64.eq v zero then (
    let h = get () in
    return ptr
  ) else (
    let h = get () in
    assume (Spec.size_of_tree (Impl.v_linked_tree ptr h) < 1000000000);
    assume (Spec.height_of_tree (Impl.v_linked_tree ptr h) < 1000000000);
    let ptr' = insert_avl true compare ptr v in
    let v' = U64.sub v one in
    main5_aux ptr' v'
  )
#pop-options


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
  if U64.eq v zero then (
    return zero
  ) else (
    let b = member compare ptr v in
    if (b = check) then (
      let v' = U64.sub v one in
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
  if U64.eq v zero then (
    let h = get () in
    return ptr
  ) else (
    let h = get () in
    let ptr' = delete_avl compare ptr v in
    let v' = U64.sub v one in
    main7_aux ptr' v'
  )
#pop-options
