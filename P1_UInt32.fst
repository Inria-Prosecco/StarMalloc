module P1_UInt32

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
//open NTreeC3
//open P1
module U32 = FStar.UInt32
module I32 = FStar.Int32
module B = LowStar.Buffer


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

//let is_null = is_null #U32.t
//let null_t = null_t #U32.t
//let null_t = null_t #U32.t
inline_for_extraction noextract
let null = Steel.Reference.null
inline_for_extraction noextract
let is_null_t = NTreeC3.is_null_t #U32.t
let mk_node = NTreeC3.mk_node #U32.t
let unpack_tree = NTreeC3.unpack_tree #U32.t

//inline_for_extraction
//let intro_linked_tree_leaf = NTreeC3.intro_linked_tree_leaf #U32.t

//let elim_linked_tree_leaf = NTreeC3.elim_linked_tree_leaf #U32.t
let create_leaf = NTreeC3.create_leaf #U32.t

//noextract
//let pack_tree = NTreeC3.pack_tree #U32.t

let member = P1.member #U32.t
//inline_for_extraction
//let append_left = append_left #U32.t
//let append_right = append_right #U32.t
//let height = height #U32.t

//let rotate_left = rotate_left #U32.t
//let rotate_right = rotate_right #U32.t
//let rotate_right_left = rotate_right_left #U32.t
//let rotate_left_right = rotate_left_right #U32.t
//
//let is_balanced = is_balanced #U32.t
//let rebalance_avl = rebalance_avl #U32.t
//let insert_avl = insert_avl #U32.t

(*)
let one ()
  : Steel (ref nat)
  (emp)
  (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  let r = malloc 1 in
  r*)

(*)
let rec free_wds #a (ptr: t a) : Steel unit
  (linked_tree ptr)
  //(fun _ -> admit(); sladmit (); emp)
  (fun _ -> admit(); sladmit (); emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
  =
  sladmit ();
  let n = NTreeC3.unpack_tree ptr in
  //free_wds (get_left n);
  //free_wds (get_right n);
  //free (get_size n);
  //write (get_size n) 0;
  pack_tree ptr (get_left n) (get_right n) (get_size n);
  free ptr;
  ()
  //free (get_data n)
*)

(*)
let create_leaf ()
  : Steel (t U32.t)
  (emp)
  (fun ptr -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun _ ptr h1 -> Trees.Leaf? (v_linked_tree ptr h1))
  =
  intro_linked_tree_leaf ();
  null_t
*)

(*)
let rec leftmost_p' (#a: eqtype) (x: Trees.tree a) (d: a) : a
  = match x with
  | Trees.Leaf -> d
  | Trees.Node x l _ _ ->
      let v = leftmost_p' l d in
      if v = d then x else v
let leftmost_p = leftmost_p' #U32.t

let rec leftmost (ptr: t U32.t) (d: U32.t) : Steel U32.t
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun h0 x h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    x == leftmost_p (v_linked_tree ptr h0) d
  )
  =
  if is_null_t ptr then (
    elim_linked_tree_leaf ptr;
    return d
  ) else (
    let n = unpack_tree ptr in
    let v = leftmost (get_left n) d in
    let vr = if v = d then (get_data n) else v in
    pack_tree ptr (get_left n) (get_right n) (get_size n);
    return vr
  )
*)

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
  let v = 1ul in
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

(*)
open FStar.HyperStack.ST
open FStar.HyperStack
let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let r = one () in
  let n = mk_node 1ul null_t null_t r in
  pop_frame ();
  0l
