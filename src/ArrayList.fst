module ArrayList

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ArrayRef

module U32 = FStar.UInt32

module A = Steel.Array
module L = FStar.List.Tot
module US = FStar.SizeT
module FS = FStar.FiniteSet.Base
module AL = ArrayListGen

(** A monomorphized version of ArrayListGen, specialized for cells of statuses, i.e., 0ul, 1ul, or 2ul.
    We only expose the computationally relevant functions here, all the lemmas remain in ArrayListGen *)

inline_for_extraction noextract
let status = v:U32.t{U32.v v < 3}

let cell : Type0 = AL.cell status

inline_for_extraction noextract
let null = AL.null
inline_for_extraction noextract
let null_ptr = AL.null_ptr

unfold
let varraylist (pred1 pred2 pred3: status -> prop) (r:A.array cell) (hd1 hd2 hd3:nat) : vprop =
  AL.varraylist pred1 pred2 pred3 r hd1 hd2 hd3

[@@ __steel_reduce__]
let v_arraylist (#p2:vprop) (pred1 pred2 pred3: status -> prop) (r:A.array cell) (hd1 hd2 hd3:nat)
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic
    (can_be_split p2 (varraylist pred1 pred2 pred3 r hd1 hd2 hd3) /\ True)}) : GTot (Seq.seq cell)
  = h (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
let remove1
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd1:US.t)
  (hd2 hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3)
          (fun hd' -> varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)
          (requires fun h -> AL.mem (US.v idx) (US.v hd1) (h (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3)))
          (ensures fun h0 hd' h1 ->
            AL.ptrs_in (US.v hd') (h1 (varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)) ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd1) (h0 (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3))) /\
            AL.ptrs_in hd2 (h1 (varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)) ==
            AL.ptrs_in hd2 (h0 (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3)) /\
            AL.ptrs_in hd3 (h1 (varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3)) ==
            AL.ptrs_in hd3 (h0 (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3))
          )
  = AL.remove1 r hd1 hd2 hd3 idx

let remove2
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd1:Ghost.erased nat)
  (hd2:US.t)
  (hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3)
          (fun hd' -> varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)
          (requires fun h -> AL.mem (US.v idx) (US.v hd2) (h (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3)))
          (ensures fun h0 hd' h1 ->
            AL.ptrs_in (US.v hd') (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)) ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd2) (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3))) /\
            AL.ptrs_in hd1 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)) ==
            AL.ptrs_in hd1 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3)) /\
            AL.ptrs_in hd3 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3)) ==
            AL.ptrs_in hd3 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3))
          )
  = AL.remove2 r hd1 hd2 hd3 idx

let insert2
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd1 hd3:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)
          (requires fun h -> pred2 v /\
            (~ (AL.mem_all (US.v idx) hd1 (US.v hd) hd3 (h (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)))))
          (ensures fun h0 hd' h1 ->
            AL.ptrs_in (US.v idx) (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)) ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3))) /\
            AL.ptrs_in hd1 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)) ==
            AL.ptrs_in hd1 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)) /\
            AL.ptrs_in hd3 (h1 (varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)) ==
            AL.ptrs_in hd3 (h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3))
          )
  = AL.insert2 r hd hd1 hd3 idx v

let insert3
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd1 hd2:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))
          (requires fun h -> pred3 v /\
            (~ (AL.mem_all (US.v idx) hd1 hd2 (US.v hd) (h (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))))))
          (ensures fun h0 hd' h1 ->
            AL.ptrs_in (US.v idx) (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))) ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd)))) /\
            AL.ptrs_in hd1 (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))) ==
            AL.ptrs_in hd1 (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))) /\
            AL.ptrs_in hd2 (h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))) ==
            AL.ptrs_in hd2 (h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd)))
          )
  = AL.insert3 r hd  hd1 hd2 idx v
