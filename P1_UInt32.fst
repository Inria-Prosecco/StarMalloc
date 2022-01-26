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

let t = NTreeC3.t
let linked_tree = NTreeC3.linked_tree

//let a = U32.t
//let val0 = 0ul
//let val1 = 1ul
//let val2 = 2ul
//let val3 = 3ul
//let val4 = 4ul
//let val42 = 42ul
//let compare (x y: U32.t) : I64.t
//  =
//  if U32.gt x y then 1L
//  else if U32.eq x y then 0L
//  else -1L

let a = (U32.t & U32.t)
let val0 = 0ul, 0ul
let val1 = 1ul, 1ul
let val2 = 2ul, 2ul
let val3 = 3ul, 3ul
let val4 = 4ul, 4ul
let val42 = 42ul, 42ul
let compare (x y: a) : I64.t
  =
  let x = fst x in
  let y = fst y in
  if U32.gt x y then 1L
  else if U32.eq x y then 0L
  else -1L

inline_for_extraction noextract
let get_left = NTreeC3.get_left #a
inline_for_extraction noextract
let get_right = NTreeC3.get_right #a
inline_for_extraction noextract
let get_size = NTreeC3.get_size #a
inline_for_extraction noextract
let get_data = NTreeC3.get_data #a

// will be useful later? if so, null or null_t?
//inline_for_extraction noextract
//let null = Steel.Reference.null
inline_for_extraction noextract
let is_null_t = NTreeC3.is_null_t #a

inline_for_extraction noextract
let mk_node = NTreeC3.mk_node #a

(* not inlined *)
let unpack_tree = NTreeC3.unpack_tree #a

(* stdlib *)
let create_leaf = P1.create_leaf #a
let create_tree = P1.create_tree #a
let merge_tree = P1.merge_tree #a
let sot_wds = P1.sot_wds #a
let append_left = P1.append_left #a
let append_right = P1.append_right #a
let height = P1.height #a
let member = P1.member #a
let insert_bst = P1.insert_bst #a
let insert_bst2 = P1.insert_bst2 #a
let rotate_left = P1.rotate_left #a
let rotate_right = P1.rotate_right #a
let rotate_right_left = P1.rotate_right_left #a
let rotate_left_right = P1.rotate_left_right #a
let is_balanced = P1.is_balanced #a
(*
let rebalance_avl = P1.rebalance_avl #U32.t
let insert_avl = P1.insert_avl #U32.t
*)

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


let main ()
  : Steel U32.t
  (emp)
  (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
  =
  let ptr = create_tree val1 in
  let ptr = append_left ptr val2 in
  let b = member ptr val1 in
  let vr = if b then val42 else val0 in
  destruct ptr;
  return (fst vr)

let main2 ()
  : Steel U64.t
  (emp)
  (fun n -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
  =
  let ptr = create_leaf () in
  let ptr = append_right ptr val1 in
  let ptr = append_right ptr val2 in
  let ptr = append_right ptr val3 in
  let h = height ptr in
  destruct ptr;
  h


let compare_is_cmp () : Lemma
(
  (forall x. I64.eq (compare x x) I64.zero) /\
  (forall x y. I64.gt (compare x y) I64.zero
                 <==> I64.lt (compare y x) I64.zero) /\
  (forall x  y z. I64.gte (compare x y) I64.zero /\
                         I64.gte (compare y z) I64.zero ==>
                         I64.gte (compare x z) I64.zero)
) = admit ()

let main3 ()
  : Steel U32.t
  emp (fun r_n -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
  =
  let ptr = create_leaf () in
  let ptr = append_left ptr val0 in
  let ptr = append_right ptr val1 in
  //let h = get () in
  //compare_is_cmp ();
  //assert (Trees.is_bst (P1.convert compare) (NTreeC3.v_linked_tree ptr h));
  let ptr = insert_bst compare ptr val2 in
  //let h = get () in
  //assert (Trees.is_bst (P1.convert compare) (NTreeC3.v_linked_tree ptr h));
  let h = sot_wds ptr in
  let b = member ptr val2 in
  let vr = if b then val42 else val0 in
  destruct ptr;
  return (fst vr)

let main4()
  : Steel U32.t
  emp (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  let ptr = create_tree val3 in
  let valn1 = 2ul, 1729ul in
  let valn2 = 2ul, 42ul in
  // toggling this flag allow one to check
  // whether the r arg of insert_bst2 is taken into account
  let f = true in
  let ptr = insert_bst2 f compare ptr valn1 in
  let ptr = insert_bst2 f compare ptr valn2 in
  assert (I64.eq (compare valn1 valn2) I64.zero);
  let b = member ptr valn2 in
  let vr = if b then val42 else val0 in
  destruct ptr;
  return (fst vr)
