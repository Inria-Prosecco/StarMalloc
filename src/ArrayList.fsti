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
let status = v:U32.t{U32.v v < 5}

let cell : Type0 = AL.cell status

inline_for_extraction noextract
let null = AL.null
inline_for_extraction noextract
let null_ptr = AL.null_ptr

unfold
let varraylist
  (pred1 pred2 pred3 pred4 pred5: status -> prop)
  (r:A.array cell)
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  : vprop =
  AL.varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 hd5 tl5 sz5

[@@ __steel_reduce__]
let v_arraylist (#p2:vprop)
  (pred1 pred2 pred3 pred4 pred5: status -> prop)
  (r:A.array cell)
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic
    (can_be_split p2 (varraylist pred1 pred2 pred3 pred4 pred5 r hd1 hd2 hd3 hd4 hd5 tl5 sz5) /\ True)}) : GTot (Seq.seq cell)
  = h (varraylist pred1 pred2 pred3 pred4 pred5 r
  hd1 hd2 hd3 hd4 hd5 tl5 sz5)

val read_in_place
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel status
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun _ -> True)
  (ensures fun h0 result h1 ->
    let gs0 = v_arraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 hd5 tl5 sz5 h0 in
    result == AL.get_data (Seq.index gs0 (US.v idx)) /\
    h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 hd5 tl5 sz5) ==
    h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 hd5 tl5 sz5))

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
/// We provide three variants for simplicity of use, and perform the permutations
/// of the lists in the varraylist predicate internally to only expose one idiomatic
/// remove function
inline_for_extraction noextract
val remove1
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd1:US.t)
  (hd2 hd3 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel US.t
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    (US.v hd1) hd2 hd3 hd4 hd5 tl5 sz5)
  (fun hd' -> varraylist pred1 pred2 pred3 pred4 pred5 r
    (US.v hd') hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun h ->
    AL.mem (US.v idx) (US.v hd1)
      (h (varraylist pred1 pred2 pred3 pred4 pred5 r
        (US.v hd1) hd2 hd3 hd4 hd5 tl5 sz5)))
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v hd1) hd2 hd3 hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v hd') hd2 hd3 hd4 hd5 tl5 sz5) in
    AL.ptrs_in (US.v hd') gs1 ==
    FS.remove (US.v idx) (AL.ptrs_in (US.v hd1) gs0) /\
    AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    AL.ptrs_in hd5 gs1 == AL.ptrs_in hd5 gs0 /\
    (~ (AL.mem_all (US.v idx) (US.v hd') hd2 hd3 hd4 hd5 gs1)) /\
    AL.dataify gs1 == AL.dataify gs0
  )

inline_for_extraction noextract
val remove2
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd1:Ghost.erased nat)
  (hd2:US.t)
  (hd3 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel US.t
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 (US.v hd2) hd3 hd4 hd5 tl5 sz5)
  (fun hd' -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 (US.v hd') hd3 hd4 hd5 tl5 sz5)
  (requires fun h ->
    AL.mem (US.v idx) (US.v hd2)
      (h (varraylist pred1 pred2 pred3 pred4 pred5 r
        hd1 (US.v hd2) hd3 hd4 hd5 tl5 sz5)))
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 (US.v hd2) hd3 hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 (US.v hd') hd3 hd4 hd5 tl5 sz5) in
    AL.ptrs_in (US.v hd') gs1 ==
    FS.remove (US.v idx) (AL.ptrs_in (US.v hd2) gs0) /\
    AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    AL.ptrs_in hd5 gs1 == AL.ptrs_in hd5 gs0 /\
    (~ (AL.mem_all (US.v idx) hd1 (US.v hd') hd3 hd4 hd5 gs1)) /\
    AL.dataify gs1 == AL.dataify gs0
  )

inline_for_extraction noextract
val remove3
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd1 hd2:Ghost.erased nat)
  (hd3:US.t)
  (hd4 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel US.t
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 (US.v hd3) hd4 hd5 tl5 sz5)
  (fun hd' -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 (US.v hd') hd4 hd5 tl5 sz5)
  (requires fun h ->
    AL.mem (US.v idx) (US.v hd3)
      (h (varraylist pred1 pred2 pred3 pred4 pred5 r
        hd1 hd2 (US.v hd3) hd4 hd5 tl5 sz5)))
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 (US.v hd3) hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 (US.v hd') hd4 hd5 tl5 sz5) in
    AL.ptrs_in (US.v hd') gs1 ==
    FS.remove (US.v idx) (AL.ptrs_in (US.v hd3) gs0) /\
    AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    AL.ptrs_in hd5 gs1 == AL.ptrs_in hd5 gs0 /\
    (~ (AL.mem_all (US.v idx) hd1 hd2 (US.v hd') hd4 hd5 gs1)) /\
    AL.dataify gs1 == AL.dataify gs0
  )

inline_for_extraction noextract
val insert1
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd2 hd3 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    (US.v hd) hd2 hd3 hd4 hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5 r
    (US.v idx) hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun h -> pred1 v /\
    (~ (AL.mem_all (US.v idx) (US.v hd) hd2 hd3 hd4 hd5
      (h (varraylist pred1 pred2 pred3 pred4 pred5 r
        (US.v hd) hd2 hd3 hd4 hd5 tl5 sz5)))))
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v hd) hd2 hd3 hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v idx) hd2 hd3 hd4 hd5 tl5 sz5) in
    AL.ptrs_in (US.v idx) gs1 ==
    FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
    AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    AL.ptrs_in hd5 gs1 == AL.ptrs_in hd5 gs0 /\
    AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
  )

inline_for_extraction noextract
val insert2
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd3 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 (US.v hd) hd3 hd4 hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 (US.v idx) hd3 hd4 hd5 tl5 sz5)
  (requires fun h -> pred2 v /\
    (~ (AL.mem_all (US.v idx) hd1 (US.v hd) hd3 hd4 hd5
      (h (varraylist pred1 pred2 pred3 pred4 pred5 r
        hd1 (US.v hd) hd3 hd4 hd5 tl5 sz5)))))
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 (US.v hd) hd3 hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 (US.v idx) hd3 hd4 hd5 tl5 sz5) in
    AL.ptrs_in (US.v idx) gs1 ==
    FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
    AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    AL.ptrs_in hd5 gs1 == AL.ptrs_in hd5 gs0 /\
    AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
  )

inline_for_extraction noextract
val insert3
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd2 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 (US.v hd) hd4 hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 (US.v idx) hd4 hd5 tl5 sz5)
  (requires fun h -> pred3 v /\
    (~ (AL.mem_all (US.v idx) hd1 hd2 (US.v hd) hd4 hd5
      (h (varraylist pred1 pred2 pred3 pred4 pred5 r
        hd1 hd2 (US.v hd) hd4 hd5 tl5 sz5)))))
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 (US.v hd) hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 (US.v idx) hd4 hd5 tl5 sz5) in
    AL.ptrs_in (US.v idx) gs1 ==
    FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
    AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    AL.ptrs_in hd5 gs1 == AL.ptrs_in hd5 gs0 /\
    AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
  )

inline_for_extraction noextract
val insert4
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd2 hd3 hd5 tl5 sz5:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 (US.v hd) hd5 tl5 sz5)
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 (US.v idx) hd5 tl5 sz5)
  (requires fun h -> pred4 v /\
    (~ (AL.mem_all (US.v idx) hd1 hd2 hd3 (US.v hd) hd5
      (h (varraylist pred1 pred2 pred3 pred4 pred5 r
        hd1 hd2 hd3 (US.v hd) hd5 tl5 sz5)))))
  (ensures fun h0 hd' h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 (US.v hd) hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 (US.v idx) hd5 tl5 sz5) in
    AL.ptrs_in (US.v idx) gs1 ==
    FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
    AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd5 gs1 == AL.ptrs_in hd5 gs0 /\
    AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
  )

/// The dlist pointed to by [hd5] is used as a queue.
/// Dequeue an element from this dlist, that is, tl5.
inline_for_extraction noextract
val dequeue
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd5 tl5 sz5:US.t)
  (hd1 hd2 hd3 hd4:Ghost.erased nat)
  : Steel AL.tuple3
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5))
  (fun result -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 (US.v result.x) (US.v result.y) (US.v result.z))
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5)) in
    sz5 <> 0sz
  )
  (ensures fun h0 result h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5)) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 (US.v result.x) (US.v result.y) (US.v result.z)) in
    //Cons? (ptrs_in_list (US.v hd5) gs0) /\
    //ptrs_in_list (US.v (fst p)) gs1
    //== L.tl (ptrs_in_list (US.v hd5) gs0) /\
    AL.ptrs_in (US.v result.x) gs1
    == FS.remove (US.v tl5) (AL.ptrs_in (US.v hd5) gs0) /\
    AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    (~ (AL.mem_all (US.v tl5) hd1 hd2 hd3 hd4 (US.v result.x) gs1)) /\
    AL.dataify gs1 == AL.dataify gs0
  )

/// The dlist pointed to by [hd5] is used as a queue.
/// Enqueue an element into this dlist.
inline_for_extraction noextract
val enqueue
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (r:A.array cell)
  (hd5 tl5 sz5:US.t)
  (hd1 hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
  : Steel AL.tuple2
  (varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5))
  (fun result -> varraylist pred1 pred2 pred3 pred4 pred5 r
    hd1 hd2 hd3 hd4 (US.v idx) (US.v result.x) (US.v result.y))
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5)) in
    pred5 v /\ (~ (AL.mem_all (US.v idx) hd1 hd2 hd3 hd4 (US.v hd5) gs0)) /\
    US.v sz5 < US.v Config.quarantine_queue_length
  )
  (ensures fun h0 result h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 (US.v hd5) (US.v tl5) (US.v sz5)) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 (US.v idx) (US.v result.x) (US.v result.y)) in
    result.y <> 0sz /\
    //ptrs_in_list (US.v idx) gs1 ==
    //(ptrs_in_list (US.v hd5) gs0) @ [US.v idx] /\
    AL.ptrs_in (US.v idx) gs1 ==
    FS.insert (US.v idx) (AL.ptrs_in (US.v hd5) gs0) /\
    AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
    AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
  )

//TODO: hide function body
let extend_aux (#opened:_)
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (n: US.t)
  (r:A.array cell)
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:Ghost.erased nat)
  (k:US.t{US.v k + US.v n <= A.length r /\ US.fits (US.v k + US.v n)})
  (v:status)
  : SteelGhost unit opened
  (
    varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r k)
      hd1 hd2 hd3 hd4 hd5 tl5 sz5 `star`
    A.varray (A.split_l (A.split_r r k) n)
  )
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n))
    hd1 hd2 hd3 hd4 hd5 tl5 sz5)
  (requires fun _ -> k <> null_ptr /\ pred1 v)
  (ensures fun h0 _ h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r k)
      hd1 hd2 hd3 hd4 hd5 tl5 sz5) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n))
      hd1 hd2 hd3 hd4 hd5 tl5 sz5) in
    AL.ptrs_in hd1 (Seq.slice gs1 0 (US.v k)) == AL.ptrs_in hd1 gs0 /\
    AL.ptrs_in hd2 (Seq.slice gs1 0 (US.v k)) == AL.ptrs_in hd2 gs0 /\
    AL.ptrs_in hd3 (Seq.slice gs1 0 (US.v k)) == AL.ptrs_in hd3 gs0 /\
    AL.ptrs_in hd4 (Seq.slice gs1 0 (US.v k)) == AL.ptrs_in hd4 gs0 /\
    AL.ptrs_in hd5 (Seq.slice gs1 0 (US.v k)) == AL.ptrs_in hd5 gs0 /\
    (forall (j:nat{0 <= j /\ j < US.v n}).
      ~ (AL.mem_all (US.v k + j) hd1 hd2 hd3 hd4 hd5 gs1)
    ) /\
    Seq.slice gs1 0 (US.v k)
    ==
    gs0
  )
  =
  AL.extend_aux #status #_ #pred1 #pred2 #pred3 #pred4 #pred5
    n r hd1 hd2 hd3 hd4 hd5 tl5 sz5 k v

open Config

module G = FStar.Ghost

//TODO: hide function body
let extend_insert
  (#pred1 #pred2 #pred3 #pred4 #pred5: status -> prop)
  (n1: US.t{2 <= US.v n1})
  (n2: US.t{US.v n2 < US.v n1})
  (r: A.array cell)
  (hd2 hd3 hd4 hd5 tl5 sz5: US.t)
  (k: US.t{0 <= US.v k /\ US.v k + US.v n1 <= A.length r /\ US.fits (US.v k + US.v n1) /\ k <> null_ptr})
  (v1: status)
  : Steel unit
  (varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
  (fun _ -> varraylist pred1 pred2 pred3 pred4 pred5
    (A.split_l r (k `US.add` n1))
    (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5))
  (requires fun h0 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
    pred1 v1 /\
    A.length r <= US.v metadata_max /\
    (forall (j:nat{1 <= j /\ j < US.v n1}).
      ~ (AL.mem_all (US.v k + j) (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) gs0))
  )
  (ensures fun h0 _ h1 ->
    let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
    let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l r (k `US.add` n1))
      (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) (US.v tl5) (US.v sz5)) in
    AL.ptrs_in (US.v k + US.v n2) gs1
    == FS.union
      (AL.set (US.v k) (US.v k + US.v n2 + 1))
      (AL.ptrs_in (US.v k) gs0) /\
    AL.ptrs_in (US.v hd2) gs1 == AL.ptrs_in (US.v hd2) gs0 /\
    AL.ptrs_in (US.v hd3) gs1 == AL.ptrs_in (US.v hd3) gs0 /\
    AL.ptrs_in (US.v hd4) gs1 == AL.ptrs_in (US.v hd4) gs0 /\
    AL.ptrs_in (US.v hd5) gs1 == AL.ptrs_in (US.v hd5) gs0 /\
    Seq.slice (AL.dataify gs1) 0 (US.v k + US.v n2 + 1)
    == Seq.append
      (Seq.slice (G.reveal (AL.dataify gs0)) 0 (US.v k + 1))
      (Seq.create (US.v n2) v1) /\
    (forall (j:nat{US.v n2 + 1 <= j /\ j < US.v n1}).
      ~ (AL.mem_all (US.v k + j) (US.v k + US.v n2) (US.v hd2) (US.v hd3) (US.v hd4) (US.v hd5) gs1)) /\
    True
  )
  =
  AL.extend_insert #status #pred1 #pred2 #pred3 #pred4 #pred5
    n1 n2 r hd2 hd3 hd4 hd5 tl5 sz5 k v1
