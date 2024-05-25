module Impl.Core

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
module M = FStar.Math.Lib
module Spec = Spec.Trees

#set-options "--ide_id_info_off"

(*** Type declarations *)

(**** Base types *)

(** A node of the tree *)
val node (a: Type0) : Type0

(** A tree is a ref to a node, themselves referencing other nodes *)
let t (a: Type0) = ref (node a)

module G = FStar.Ghost

unfold
let hpred (a: Type0) = p:G.erased (t a -> prop){
  (G.reveal p) (null #(node a))
}

(** This type reflects the contents of a tree without the memory layout *)
// TODO: to be replaced with MAX_UINT64
noextract
let c = FStar.UInt.max_int 64
let wdm (a: Type0) = x:Spec.wdm a{
  Spec.size_of_tree x <= c /\
  Spec.height_of_tree x <= c
}

(**** Operations on nodes *)

inline_for_extraction noextract
val get_left (#a: Type0) (n: node a) : t a
inline_for_extraction noextract
val get_right (#a: Type0) (n: node a) : t a
inline_for_extraction noextract
val get_data (#a: Type0) (n: node a) : a
inline_for_extraction noextract
val get_size (#a: Type0) (n: node a) : U.t
inline_for_extraction noextract
val get_height (#a: Type0) (n: node a) : U.t
inline_for_extraction noextract
val mk_node (#a: Type0)
  (data: a) (left right: t a) (size height: U.t)
    : Pure (node a)
      (requires True)
      (ensures (fun n ->
        get_left n == left
     /\ get_right n == right
     /\ get_data n == data
     /\ get_size n == size
     /\ get_height n == height))


(**** Slprop and selector *)

inline_for_extraction noextract
val null_t (#a: Type0) : v:t a//{v == null}
inline_for_extraction noextract
val is_null_t (#a: Type0) (r: t a) : (b:bool{b <==> r == null_t})


(** The separation logic proposition representing the memory layout of the tree *)
val tree_sl (#a: Type0) (p: hpred a) (ptr: t a) : slprop u#1

(** Selector retrieving the contents of a tree in memory *)
val tree_sel (#a: Type0) (p: hpred a) (ptr: t a) : selector (wdm a) (tree_sl p ptr)

[@@__steel_reduce__]
let linked_tree' (#a: Type0) (p: hpred a) (ptr: t a) : vprop' = {
  hp = tree_sl p ptr;
  t = wdm a;
  sel = tree_sel p ptr
}

(** The view proposition encapsulating the separation logic proposition and the selector *)
unfold let linked_tree (#a: Type0) (p: hpred a) (ptr: t a) : vprop = VUnit (linked_tree' p ptr)

(** This convenience helper retrieves the contents of a tree from an [rmem] *)
[@@ __steel_reduce__]
let v_linked_tree
  (#a:Type0)
  (#vp:vprop)
  (p: hpred a)
  (ptr:t a)
  (h:rmem vp{
    FStar.Tactics.with_tactic selector_tactic (can_be_split vp (linked_tree p ptr) /\ True)
  })
    : GTot (wdm a)
  = h (linked_tree p ptr)

(*** Operations *)

(**** Low-level operations on trees *)

val intro_linked_tree_leaf (#opened:inames) (#a: Type0) (p: hpred a) (_: unit)
  : SteelGhost unit opened
  emp
  (fun _ -> emp `star` linked_tree p (null_t #a))
  (requires fun _ -> True)
  (ensures fun _ _ h1 ->
    v_linked_tree #a p null_t h1 == Spec.Leaf
  )

val elim_linked_tree_leaf (#opened:inames) (#a: Type0) (p: hpred a) (ptr: t a)
  : SteelGhost unit opened
  (linked_tree p ptr)
  (fun _ -> emp)
  (requires fun _ -> is_null_t ptr)
  (ensures fun h0 _ h1 ->
    v_linked_tree p ptr h0 == Spec.Leaf
  )

val null_is_leaf (#opened:inames) (#a: Type0) (p: hpred a) (ptr: t a)
  : SteelGhost unit opened
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun _ -> is_null_t ptr)
  (ensures fun h0 _ h1 ->
    Spec.Leaf? (v_linked_tree p ptr h0) /\
    v_linked_tree p ptr h0 == v_linked_tree p ptr h1
  )

val leaf_is_null (#opened:inames) (#a: Type0) (p: hpred a) (ptr: t a)
  : SteelGhost unit opened
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun h0 -> Spec.Leaf? (v_linked_tree p ptr h0))
  (ensures fun h0 _ h1 ->
    is_null_t ptr /\
    v_linked_tree p ptr h0 == v_linked_tree p ptr h1
  )

val node_is_not_null (#opened:inames) (#a: Type0) (p: hpred a) (ptr: t a)
  : SteelGhost unit opened
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun h0 -> Spec.Node? (v_linked_tree p ptr h0))
  (ensures fun h0 _ h1 ->
     not (is_null_t ptr) /\
     v_linked_tree p ptr h0 == v_linked_tree p ptr h1
  )

val not_null_is_node (#opened:inames) (#a: Type0) (p: hpred a) (ptr: t a)
  : SteelGhost unit opened
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun _ -> not (is_null_t ptr))
  (ensures fun h0 _ h1 ->
    Spec.Node? (v_linked_tree p ptr h0) /\
    v_linked_tree p ptr h0 == v_linked_tree p ptr h1
  )

val extract_pred (#opened:inames) (#a: Type0) (p: hpred a) (ptr: t a)
  : SteelGhost unit opened
  (linked_tree p ptr)
  (fun _ -> linked_tree p ptr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    (G.reveal p) ptr /\
    h1 (linked_tree p ptr) == h0 (linked_tree p ptr)
  )

val pack_tree (#opened:inames) (#a: Type0) (p: hpred a)
  (ptr: t a) (left right: t a) (sr hr: U.t)
  : SteelGhost unit opened
  (vptr ptr `star`
  linked_tree p left `star`
  linked_tree p right)
  (fun _ -> linked_tree p ptr)
  (requires fun h0 ->
    get_left (sel ptr h0) == left /\
    get_right (sel ptr h0) == right /\
    get_size (sel ptr h0) == sr /\
    get_height (sel ptr h0) == hr /\
    U.v sr == Spec.size_of_tree (v_linked_tree p left h0) +
              Spec.size_of_tree (v_linked_tree p right h0) +
              1 /\
    U.v hr == M.max
      (Spec.height_of_tree (v_linked_tree p left h0))
      (Spec.height_of_tree (v_linked_tree p right h0))
      + 1 /\
    U.v sr <= c /\
    (G.reveal p) ptr
  )
  (ensures fun h0 _ h1 ->
    let x = get_data (sel ptr h0) in
    let l = v_linked_tree p left h0 in
    let r = v_linked_tree p right h0 in
    v_linked_tree p ptr h1 == Spec.Node x l r (U.v sr) (U.v hr)
  )

inline_for_extraction noextract
val unpack_tree (#a: Type0) (p: hpred a) (ptr: t a)
  : Steel (node a)
  (linked_tree p ptr)
  (fun node ->
    vptr ptr `star`
    linked_tree p (get_left node) `star`
    linked_tree p (get_right node))
  (requires fun h0 -> not (is_null_t ptr))
  (ensures fun h0 node h1 ->
    v_linked_tree p ptr h0 == Spec.Node
      (get_data (sel ptr h1))
      (v_linked_tree p (get_left node) h1)
      (v_linked_tree p (get_right node) h1)
      (U.v (get_size node))
      (U.v (get_height node))
    /\
    sel ptr h1 == node /\
    U.v (get_size node)
    == Spec.size_of_tree (v_linked_tree p (get_left node) h1)
     + Spec.size_of_tree (v_linked_tree p (get_right node) h1) + 1 /\
    U.v (get_height node)
    == M.max (Spec.height_of_tree (v_linked_tree p (get_left node) h1))
             (Spec.height_of_tree (v_linked_tree p (get_right node) h1)) + 1 /\
    U.v (get_size node) <= c /\
    U.v (get_height node) <= c /\
    (G.reveal p) ptr /\
    // extract_pred could be used manually, adding this postcondition makes verification easier
    (G.reveal p) (get_left node) /\
    (G.reveal p) (get_right node)
  )
