module P1_UInt32

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module U32 = FStar.UInt32
//open NTreeC3
//open P1

let t = NTreeC3.t
let linked_tree = NTreeC3.linked_tree

inline_for_extraction noextract
let get_left = NTreeC3.get_left #U32.t
inline_for_extraction noextract
let get_right = NTreeC3.get_right #U32.t
inline_for_extraction noextract
let get_size = NTreeC3.get_size #U32.t
inline_for_extraction noextract
let get_data = NTreeC3.get_data #U32.t

// will be useful later? if so, null or null_t?
//inline_for_extraction noextract
//let null = Steel.Reference.null
inline_for_extraction noextract
let is_null_t = NTreeC3.is_null_t #U32.t

inline_for_extraction noextract
let mk_node = NTreeC3.mk_node #U32.t

(* not inlined *)
let unpack_tree = NTreeC3.unpack_tree #U32.t
let create_leaf = NTreeC3.create_leaf #U32.t

(* stdlib *)
(* TODO: failure wrt Prims addition *)
(*
let append_left = P1.append_left #U32.t
let append_right = P1.append_right #U32.t
let height = P1.height #U32.t
*)
let member = P1.member #U32.t
(* TODO: another failure "nth" *)
(*
let rotate_left = P1.rotate_left #U32.t
let rotate_right = P1.rotate_right #U32.t
let rotate_right_left = P1.rotate_right_left #U32.t
let rotate_left_right = P1.rotate_left_right #U32.t
let is_balanced = P1.is_balanced #U32.t
let rebalance_avl = P1.rebalance_avl #U32.t
let insert_avl = P1.insert_avl #U32.t
*)

let one ()
  : Steel (ref nat)
  (emp)
  (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  let v = 1 + 1 in
  let r = malloc v in r

let destruct_linked_tree_leaf (ptr: t U32.t) : Steel unit
  (linked_tree ptr) (fun _ -> emp)
  (requires fun _ -> is_null_t ptr)
  (ensures fun _ _ _ -> True)
  = sladmit ()

//inline_for_extraction
let rec destruct (ptr: t U32.t) : Steel unit
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
  //: Steel (t U32.t)
  : Steel U32.t
  (emp)
  //(fun ptr -> linked_tree ptr)
  (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _-> True)
  =
  let l = create_leaf () in
  let r = create_leaf () in
  let sr = malloc 1 in
  let v = 0ul in
  let n = mk_node v l r sr in
  let ptr = malloc n in
  NTreeC3.pack_tree ptr l r sr;
  //let ptr = append_left ptr 0ul in
  //let vr = leftmost ptr 12ul in
  let b = member ptr 0ul in
  let vr = if b then 42ul else 11ul in
  //ptr
  destruct ptr;
  vr
