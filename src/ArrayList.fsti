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

val read_in_place
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd1 hd2 hd3:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel status
          (varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 hd3)
          (requires fun _ -> True)
          (ensures fun h0 result h1 ->
            result == AL.get_data (Seq.index (v_arraylist pred1 pred2 pred3 r hd1 hd2 hd3 h0) (US.v idx)) /\
            h0 (varraylist pred1 pred2 pred3 r hd1 hd2 hd3) ==
            h1 (varraylist pred1 pred2 pred3 r hd1 hd2 hd3))

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
/// We provide three variants for simplicity of use, and perform the permutations
/// of the lists in the varraylist predicate internally to only expose one idiomatic
/// remove function
inline_for_extraction noextract
val remove1
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
            let gs0 = h0 (varraylist pred1 pred2 pred3 r (US.v hd1) hd2 hd3) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 r (US.v hd') hd2 hd3) in
            AL.ptrs_in (US.v hd') gs1 ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd1) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            (~ (AL.mem_all (US.v idx) (US.v hd') hd2 hd3 gs1)) /\
            AL.dataify gs1 == AL.dataify gs0
          )

inline_for_extraction noextract
val remove2
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
            let gs0 = h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd2) hd3) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 r hd1 (US.v hd') hd3) in
            AL.ptrs_in (US.v hd') gs1 ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd2) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            (~ (AL.mem_all (US.v idx) hd1 (US.v hd') hd3 gs1)) /\
            AL.dataify gs1 == AL.dataify gs0
          )

inline_for_extraction noextract
val remove3
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd1:Ghost.erased nat)
  (hd2:Ghost.erased nat)
  (hd3:US.t)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3))
          (fun hd' -> varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd'))
          (requires fun h -> AL.mem (US.v idx) (US.v hd3) (h (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3))))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd3)) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd')) in
            AL.ptrs_in (US.v hd') gs1 ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd3) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            (~ (AL.mem_all (US.v idx) hd1 hd2 (US.v hd') gs1)) /\
            AL.dataify gs1 == AL.dataify gs0
          )

inline_for_extraction noextract
val insert1
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd2 hd3:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r (US.v idx) hd2 hd3)
          (requires fun h -> pred1 v /\
            (~ (AL.mem_all (US.v idx) (US.v hd) hd2 hd3 (h (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3)))))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 r (US.v hd) hd2 hd3) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 r (US.v idx) hd2 hd3) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )

inline_for_extraction noextract
val insert2
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd3:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3)
          (requires fun h -> pred2 v /\
            (~ (AL.mem_all (US.v idx) hd1 (US.v hd) hd3 (h (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3)))))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 r hd1 (US.v hd) hd3) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 r hd1 (US.v idx) hd3) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )

inline_for_extraction noextract
val insert3
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd2:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))
          (fun _ -> varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx))
          (requires fun h -> pred3 v /\
            (~ (AL.mem_all (US.v idx) hd1 hd2 (US.v hd) (h (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd))))))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v hd)) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 r hd1 hd2 (US.v idx)) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )

inline_for_extraction noextract
val extend1
  (#pred1 #pred2 #pred3: status -> prop)
  (r:A.array cell)
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd2 hd3:Ghost.erased nat)
  (k:US.t{US.v k + 1 <= A.length r /\ US.fits (US.v k + 1)})
  (v: status)
  : Steel unit
          (AL.varraylist pred1 pred2 pred3 (A.split_l r k) (US.v hd) hd2 hd3 `star`
            A.varray (A.split_l (A.split_r r k) 1sz))
          (fun _ ->
            AL.varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3)
          (requires fun _ ->
            k <> null_ptr /\ pred1 v)
          (ensures fun h0 _ h1 ->
            A.length_fits r;
            let gs0 = h0 (varraylist pred1 pred2 pred3 (A.split_l r k) (US.v hd) hd2 hd3) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3) in
            AL.ptrs_in (US.v k) gs1 ==
            FS.insert (US.v k) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.dataify gs1 `Seq.equal` Seq.append (AL.dataify gs0) (Seq.create 1 v)
          )
