module BlobList

module U8 = FStar.UInt8
module U32 = FStar.UInt32

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef
module SR = Steel.Reference
module A = Steel.Array
module SL = Selectors.LList3

open Utils2

(** A monomorphized version of lists, for blobs *)

unfold
let blob
  = slab_metadata &
    (arr:array U8.t{A.length arr = U32.v page_size})

let cell = SL.cell blob
let t = SL.t blob

inline_for_extraction noextract
let get_next (c:cell) : t = SL.get_next c
inline_for_extraction noextract
let get_data (c:cell) : blob = SL.get_data c
inline_for_extraction noextract
let mk_cell (n: t) (d:blob)
  : Pure cell
    (requires True)
    (ensures fun c ->
      get_next c == n /\
      get_data c == d)
= SL.mk_cell n d

/// The null list pointer
inline_for_extraction noextract
let null_t : t = SL.null_t

/// Lifting the null pointer check to empty lists
inline_for_extraction noextract
let is_null_t (ptr:t) : (b:bool{b <==> ptr == null_t}) = SL.is_null_t ptr

unfold
let llist (p: blob -> vprop) (r:t) = SL.llist p r

[@@ __steel_reduce__]
let v_llist (#p2:vprop) (p: blob -> vprop) (r:t)
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic (can_be_split p2 (llist p r) /\ True)}) : GTot (list blob)
  = h (llist p r)

let intro_llist_nil (#opened:inames) (p: blob -> vprop)
  : SteelGhost unit opened
    emp (fun _ -> llist p (null_t))
    (requires fun _ -> True)
    (ensures fun _ _ h1 -> v_llist p null_t h1 == [])
  = SL.intro_llist_nil p

let elim_llist_nil (#opened:inames) (p: blob -> vprop) (ptr:t)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun _ -> ptr == null_t)
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    v_llist p ptr h1 == [])
  = SL.elim_llist_nil p ptr

let cons_is_not_null (#opened:inames) (p: blob -> vprop) (ptr:t)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun h -> Cons? (v_llist p ptr h))
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    ptr =!= null_t)
  = SL.cons_is_not_null p ptr

let cons_imp_not_null (#opened:inames) (p: blob -> vprop) (ptr:t)
  : SteelGhost unit opened
  (llist p ptr) (fun _ -> llist p ptr)
  (requires fun h -> True)
  (ensures fun h0 _ h1 ->
    v_llist p ptr h0 == v_llist p ptr h1 /\
    Cons? (v_llist p ptr h0) = not (is_null_t ptr))
  = SL.cons_imp_not_null p ptr

let pack_list
  (p: blob -> vprop)
  (ptr1 ptr2: t)
  (x: blob)
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
  = SL.pack_list p ptr1 ptr2 x

let unpack_list
  (p: blob -> vprop)
  (ptr:t)
  : Steel cell
  (llist p ptr)
  (fun n -> vptr ptr `star` llist p (get_next n) `star` p (get_data n))
  (requires fun _ -> ptr =!= null_t)
  (ensures fun h0 n h1 ->
    Cons? (v_llist p ptr h0) /\
    v_llist p ptr h0 ==
      (get_data (sel ptr h1)) :: (v_llist p (get_next n) h1) /\
     sel ptr h1 == n)
  = SL.unpack_list p ptr

let intro_singleton_llist_no_alloc
  (p: blob -> vprop)
  (r: t)
  (v: blob)
  : Steel unit
  (vptr r `star` p v)
  (fun r' -> llist p r)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 ->
    v_llist p r h1 == [v]
  )
  = SL.intro_singleton_llist_no_alloc p r v

(** A variant of lists with an additional indirection pointer to enable in-place operations **)

unfold
let ind_llist (p: blob -> vprop) (r:SR.ref t) = SL.ind_llist p r

[@@ __steel_reduce__]
let v_ind_llist (#p2:vprop) (p: blob -> vprop) (r:SR.ref t)
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic (can_be_split p2 (ind_llist p r) /\ True)}) : GTot (list blob)
  = h (ind_llist p r)

let unpack_ind (p: blob -> vprop) (r:SR.ref t)
  : Steel t
  (ind_llist p r)
  (fun r2 -> SR.vptr r `star` llist p r2)
  (requires fun _ -> True)
  (ensures fun h0 r2 h1 ->
    SR.sel r h1 == r2 /\
    v_llist p r2 h1 == v_ind_llist p r h0)
  = SL.unpack_ind p r

let pack_ind (#opened:inames) (p: blob -> vprop) (r:SR.ref t) (r2:t)
  : SteelGhost unit opened
  (SR.vptr r `star` llist p r2)
  (fun _ -> ind_llist p r)
  (requires fun h -> SR.sel r h == r2)
  (ensures fun h0 _ h1 -> v_llist p r2 h0 == v_ind_llist p r h1)
  = SL.pack_ind p r r2
