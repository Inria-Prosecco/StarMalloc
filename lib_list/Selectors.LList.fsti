module Selectors.LList

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module L = FStar.List.Tot

/// This module provides the basis for implementing list operations with selectors

/// Abstract type of a list cell containing a value of type [a]
val cell (a:Type0) : Type0
/// The type of a list: A reference to a cell
let t (a:Type0) = ref (cell a)

(* Helpers to manipulate cells while keeping its definition abstract *)

inline_for_extraction noextract
val get_next (#a:Type0) (c:cell a) : t a
inline_for_extraction noextract
val get_data (#a:Type0) (c:cell a) : a
inline_for_extraction noextract
val mk_cell (#a:Type0) (n: t a) (d:a)
  : Pure (cell a)
    (requires True)
    (ensures fun c ->
      get_next c == n /\
      get_data c == d)

/// The null list pointer
inline_for_extraction noextract
val null_t (#a:Type) : t a

/// Lifting the null pointer check to empty lists
inline_for_extraction noextract
val is_null_t (#a:Type) (ptr:t a) : (b:bool{b <==> ptr == null_t})

/// Separation logic predicate stating that reference [r] points to a valid list in memory
val llist_sl (#a:Type0) (p: a -> vprop) (r: t a): slprop u#1
/// Selector of a list. Returns an F* list of elements of type [a]

val llist_sel (#a:Type0) (p : a -> vprop) (r:t a) : selector (list a) (llist_sl p r)

/// Combining the two above into a linked list vprop
[@@__steel_reduce__]
let llist' #a (p : a -> vprop) r : vprop' =
  {hp = llist_sl p r;
   t = list a;
   sel = llist_sel p r}
unfold
let llist (#a:Type0) (p : a -> vprop) (r:t a) = VUnit (llist' p r)

/// A wrapper to access a list selector more easily.
/// Ensuring that the corresponding llist vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common
[@@ __steel_reduce__]
let v_llist (#a:Type0) (#p2:vprop) (p : a -> vprop) (r:t a)
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic (can_be_split p2 (llist p r) /\ True)}) : GTot (list a)
  = h (llist p r)

(** Stateful lemmas to fold and unfold the llist predicate **)

val intro_llist_nil (#opened:inames) (#a:Type0) (p : a -> vprop)
  : SteelGhost unit opened
    emp (fun _ -> llist p (null_t #a))
    (requires fun _ -> True)
    (ensures fun _ _ h1 -> v_llist #a p null_t h1 == [])

val elim_llist_nil (#opened:inames) (#a:Type0) (p : a -> vprop) (ptr:t a)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun _ -> ptr == null_t)
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    v_llist p ptr h1 == [])

val cons_is_not_null (#opened:inames) (#a:Type0) (p : a -> vprop) (ptr:t a)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun h -> Cons? (v_llist p ptr h))
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    ptr =!= null_t)

// val null_is_nil
// val nil_is_null
// val not_null_is_cons

val pack_list (#opened:inames) (#a:Type0)
  (p: a -> vprop)
  (ptr1 ptr2: t a)
  (x: a)
  : SteelGhost unit opened
  (vptr ptr1 `star`
  llist p ptr2 `star`
  p x)
  (fun _ -> llist p ptr1)
  (requires fun h ->
    get_next (sel ptr1 h) == ptr2 /\
    x == get_data (sel ptr1 h)
  )
  (ensures fun h0 _ h1 ->
    v_llist p ptr1 h1 ==
      (get_data (sel ptr1 h0)) :: v_llist p ptr2 h0)

val unpack_list (#a:Type0)
  (p: a -> vprop)
  (ptr:t a)
  : Steel (cell a)
  (llist p ptr)
  (fun n -> vptr ptr `star` llist p (get_next n) `star` p (get_data n))
  (requires fun _ -> ptr =!= null_t)
  (ensures fun h0 n h1 ->
    Cons? (v_llist p ptr h0) /\
    v_llist p ptr h0 ==
      (get_data (sel ptr h1)) :: (v_llist p (get_next n) h1) /\
     sel ptr h1 == n)

(*)
(** A variant of lists with an additional indirection pointer to enable in-place operations **)

val ind_llist_sl (#a:Type0) (r:ref (t a)) : slprop u#1
val ind_llist_sel (#a:Type0) (r:ref (t a)) : selector (list a) (ind_llist_sl r)

[@@__steel_reduce__]
let ind_llist' (#a:Type0) (r:ref (t a)) : vprop' =
  { hp = ind_llist_sl r;
    t = list a;
    sel = ind_llist_sel r}
unfold
let ind_llist (#a:Type0) (r:ref (t a)) = VUnit (ind_llist' r)

[@@ __steel_reduce__]
let v_ind_llist (#a:Type0) (#p:vprop) (r:ref (t a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ind_llist r) /\ True)}) : GTot (list a)
  = h (ind_llist r)

val unpack_ind (#a:Type0) (r:ref (t a))
  : Steel (t a)
             (ind_llist r)
             (fun p -> vptr r `star` llist p)
             (requires fun _ -> True)
             (ensures fun h0 p h1 ->
               sel r h1 == p /\
               v_llist p h1 == v_ind_llist r h0)

val pack_ind (#a:Type0) (r:ref (t a)) (p:t a)
  : Steel unit
             (vptr r `star` llist p)
             (fun _ -> ind_llist r)
             (requires fun h -> sel r h == p)
             (ensures fun h0 _ h1 -> v_llist p h0 == v_ind_llist r h1)
