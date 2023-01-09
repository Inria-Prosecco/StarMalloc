module Selectors.LList3

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef

module L = FStar.List.Tot

/// This module provides the same interface as Selectors.LList.
/// The difference is in the implementation, it uses a newer, promising style to handle vprop.
/// Instead of going down all the way to the underlying slprop representation, it uses different
/// combinators to define the core list vprop

/// Abstract type of a list cell containing a value of type [a]
val cell (a:Type0) : Type0
/// The type of a list: A reference to a cell
inline_for_extraction
let t (a:Type0) = ref (cell a)

(* Helpers to manipulate cells while keeping its definition abstract *)

inline_for_extraction
val get_next (#a:Type0) (c:cell a) : t a
inline_for_extraction
val get_data (#a:Type0) (c:cell a) : a
inline_for_extraction
val mk_cell (#a:Type0) (n: t a) (d:a)
  : Pure (cell a)
    (requires True)
    (ensures fun c ->
      get_next c == n /\
      get_data c == d)


/// The null list pointer
inline_for_extraction
val null_t (#a:Type) : t a

/// Lifting the null pointer check to empty lists
inline_for_extraction
val is_null_t (#a:Type) (ptr:t a) : (b:bool{b <==> ptr == null_t})

/// Separation logic predicate stating that reference [r] points to a valid list in memory
val llist_sl (#a:Type0) (p: a -> vprop) (r:t a) : slprop u#1

/// Selector of a list. Returns an F* list of elements of type [a]
val llist_sel (#a:Type0) (p: a -> vprop) (r:t a) : selector (list a) (llist_sl p r)

/// Combining the two above into a linked list vprop
[@@__steel_reduce__]
let llist' #a (p: a -> vprop) r : vprop' =
  {hp = llist_sl p r;
   t = list a;
   sel = llist_sel p r}
unfold
let llist (#a:Type0) (p: a -> vprop) (r:t a) = VUnit (llist' p r)

/// A wrapper to access a list selector more easily.
/// Ensuring that the corresponding llist vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common
[@@ __steel_reduce__]
let v_llist (#a:Type0) (#p2:vprop) (p: a -> vprop) (r:t a)
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic (can_be_split p2 (llist p r) /\ True)}) : GTot (list a)
  = h (llist p r)

(** Stateful lemmas to fold and unfold the llist predicate **)


val intro_llist_nil (#opened:inames) (#a:Type0) (p: a -> vprop)
  : SteelGhost unit opened
    emp (fun _ -> llist p (null_t #a))
    (requires fun _ -> True)
    (ensures fun _ _ h1 -> v_llist #a p null_t h1 == [])

val elim_llist_nil (#opened:inames) (#a:Type0) (p: a -> vprop) (ptr:t a)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun _ -> ptr == null_t)
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    v_llist p ptr h1 == [])

val cons_is_not_null (#opened:inames) (#a:Type0) (p: a -> vprop) (ptr:t a)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun h -> Cons? (v_llist p ptr h))
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    ptr =!= null_t)

val cons_imp_not_null (#opened:inames) (#a:Type0) (p: a -> vprop) (ptr:t a)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun h -> True)
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    Cons? (v_llist p ptr h0) = not (is_null_t ptr))

// val null_is_nil
// val nil_is_null
// val not_null_is_cons

val pack_list (#a:Type0)
  (p: a -> vprop)
  (ptr1 ptr2: t a)
  (x: a)
  : Steel unit
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

val intro_singleton_llist_no_alloc
  (#a: Type)
  (p: a -> vprop)
  (r: t a)
  (v: a)
  : Steel unit
  (vptr r `star` p v)
  (fun r' -> llist p r)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 ->
    v_llist p r h1 == [v]
  )


(** A variant of lists with an additional indirection pointer to enable in-place operations **)

val ind_llist_sl (#a:Type0) (p: a -> vprop) (r:ref (t a)) : slprop u#1
val ind_llist_sel (#a:Type0) (p: a -> vprop) (r:ref (t a)) : selector (list a) (ind_llist_sl p r)

[@@__steel_reduce__]
let ind_llist' (#a:Type0) (p: a -> vprop) (r:ref (t a)) : vprop' =
  { hp = ind_llist_sl p r;
    t = list a;
    sel = ind_llist_sel p r}
unfold
let ind_llist (#a:Type0) (p: a -> vprop) (r:ref (t a)) = VUnit (ind_llist' p r)

[@@ __steel_reduce__]
let v_ind_llist (#a:Type0) (#p2:vprop) (p: a -> vprop) (r:ref (t a))
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic (can_be_split p2 (ind_llist p r) /\ True)}) : GTot (list a)
  = h (ind_llist p r)

val unpack_ind (#a:Type0) (p: a -> vprop) (r:ref (t a))
  : Steel (t a)
  (ind_llist p r)
  (fun r2 -> vptr r `star` llist p r2)
  (requires fun _ -> True)
  (ensures fun h0 r2 h1 ->
    sel r h1 == r2 /\
    v_llist p r2 h1 == v_ind_llist p r h0)

val pack_ind (#opened:inames) (#a:Type0) (p: a -> vprop) (r:ref (t a)) (r2:t a)
  : SteelGhost unit opened
  (vptr r `star` llist p r2)
  (fun _ -> ind_llist p r)
  (requires fun h -> sel r h == r2)
  (ensures fun h0 _ h1 -> v_llist p r2 h0 == v_ind_llist p r h1)
