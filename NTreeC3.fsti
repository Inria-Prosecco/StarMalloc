module NTreeC3

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module Spec = Trees
module U = FStar.UInt64

#set-options "--ide_id_info_off"

(*** Type declarations *)

(**** Base types *)

(** A node of the tree *)
val node (a: Type0) : Type0

(** A tree is a ref to a node, themselves referencing other nodes *)
let t (a: Type0) = ref (node a)

(** This type reflects the contents of a tree without the memory layout *)
// TODO: to be replaced with MAX_UINT64
let c = 100
let wds (a: Type0) = x:Spec.wds a{Spec.size_of_tree x < c}
//let tree (a: Type0) = x:Spec.tree a{fst (Spec.is_wds x)}
//let tree (a: Type0) = Spec.tree a

(**** Operations on nodes *)

inline_for_extraction noextract
val get_left (#a: Type0) (n: node a) : t a
inline_for_extraction noextract
val get_right (#a: Type0) (n: node a) : t a
inline_for_extraction noextract
val get_data (#a: Type0) (n: node a) : a
inline_for_extraction noextract
val get_size (#a: Type0) (n: node a) : ref U.t
inline_for_extraction noextract
val mk_node (#a: Type0) (data: a) (left right: t a) (size: ref U.t)
    : Pure (node a)
      (requires True)
      (ensures (fun n ->
        get_left n == left
     /\ get_right n == right
     /\ get_data n == data
     /\ get_size n == size))


(**** Slprop and selector *)

inline_for_extraction noextract
val null_t (#a: Type0) : t a
inline_for_extraction noextract
val is_null_t (#a: Type0) (r: t a) : (b:bool{b <==> r == null_t})


(** The separation logic proposition representing the memory layout of the tree *)
val tree_sl (#a: Type0) (r: t a) : slprop u#1

(** Selector retrieving the contents of a tree in memory *)
val tree_sel (#a: Type0) (r: t a) : selector (wds a) (tree_sl r)

[@@__steel_reduce__]
let linked_tree' (#a: Type0) (r: t a) : vprop' = {
  hp = tree_sl r;
  t = wds a;
  sel = tree_sel r
}

(** The view proposition encapsulating the separation logic proposition and the selector *)
unfold let linked_tree (#a: Type0) (tr: t a) : vprop = VUnit (linked_tree' tr)

(** This convenience helper retrieves the contents of a tree from an [rmem] *)
[@@ __steel_reduce__]
let v_linked_tree
  (#a:Type0)
  (#p:vprop)
  (r:t a)
  (h:rmem p{
    FStar.Tactics.with_tactic selector_tactic (can_be_split p (linked_tree r) /\ True)
  })
    : GTot (Spec.wds a)
  = h (linked_tree r)

(*** Operations *)

(**** Low-level operations on trees *)

val intro_linked_tree_leaf (#opened:inames) (#a: Type0) (_: unit)
    : SteelGhost unit
      opened emp (fun _ -> linked_tree (null_t #a))
      (requires (fun _ -> True))
      (ensures (fun _ _ h1 -> v_linked_tree #a null_t h1 == Spec.Leaf))

val elim_linked_tree_leaf (#opened:inames) (#a: Type0) (ptr: t a)
    : SteelGhost unit
       opened (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun _ -> is_null_t ptr))
       (ensures (fun h0 _ h1 ->
         v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
         v_linked_tree ptr h1 == Spec.Leaf))

val node_is_not_null (#opened:inames) (#a: Type0) (ptr: t a)
    : SteelGhost unit
       opened (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun h0 -> Spec.Node? (v_linked_tree ptr h0)))
       (ensures (fun h0 _ h1 -> not (is_null_t ptr) /\ v_linked_tree ptr h0 == v_linked_tree ptr h1))

val not_null_is_node (#opened:inames) (#a: Type0) (ptr: t a)
    : SteelGhost unit
       opened (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun h0 -> not (is_null_t ptr)))
       (ensures (fun h0 _ h1 -> Spec.Node? (v_linked_tree ptr h0) /\ v_linked_tree ptr h0 == v_linked_tree ptr h1))

val pack_tree (#opened:inames) (#a: Type0) (ptr: t a) (left right: t a) (sr: ref U.t)
    : SteelGhost unit
      opened (vptr ptr `star` linked_tree left `star` linked_tree right `star` vptr sr)
      (fun _ -> linked_tree ptr)
      (requires (fun h0 ->
        get_left (sel ptr h0) == left /\
        get_right (sel ptr h0) == right /\
        get_size (sel ptr h0) == sr /\
        U.v (sel sr h0) == Spec.size_of_tree (v_linked_tree left h0)
              + Spec.size_of_tree (v_linked_tree right h0)
              + 1 /\
        U.v (sel sr h0) < c
        ))
      (ensures (fun h0 _ h1 ->
        let x = get_data (sel ptr h0) in
        let l = v_linked_tree left h0 in
        let r = v_linked_tree right h0 in
        let s = sel sr h0 in
        //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in
        v_linked_tree ptr h1 == Spec.Node x l r (U.v s)))

val unpack_tree (#a: Type0) (ptr: t a)
    : Steel (node a)
      (linked_tree ptr)
      (fun node ->
        vptr ptr `star`
        linked_tree (get_left node) `star`
        linked_tree (get_right node) `star`
        vptr (get_size node))
      (requires (fun h0 -> not (is_null_t ptr)))
      (ensures (fun h0 node h1 ->
        v_linked_tree ptr h0 == Spec.Node
          (get_data (sel ptr h1))
          (v_linked_tree (get_left node) h1)
          (v_linked_tree (get_right node) h1)
          (U.v (sel (get_size node) h1)) /\
        sel ptr h1 == node /\
        U.v (sel (get_size node) h1) == Spec.size_of_tree (v_linked_tree (get_left node) h1)
                                + Spec.size_of_tree (v_linked_tree (get_right node) h1) + 1 /\
        U.v (sel (get_size node) h1) < c
      ))

(*)
        let l = v_linked_tree (get_left node) h1 in
        let r = v_linked_tree (get_right node) h1 in
        let s = get_size node in
        //let s = Spec.size_of_tree l + Spec.size_of_tree r + 1 in

        v_linked_tree ptr h0 == Spec.Node
          (get_data (sel ptr h1))
          l r s /\
          //(v_linked_tree (get_left node) h1)
          //(v_linked_tree (get_right node) h1) /\
        (sel ptr h1) == node
      ))*)

