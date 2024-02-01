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

let read_in_place
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
    result == AL.get_data (Seq.index
      (v_arraylist pred1 pred2 pred3 pred4 pred5 r
        hd1 hd2 hd3 hd4 hd5 tl5 sz5 h0)
      (US.v idx)) /\
    h0 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 hd5 tl5 sz5) ==
    h1 (varraylist pred1 pred2 pred3 pred4 pred5 r
      hd1 hd2 hd3 hd4 hd5 tl5 sz5))
  = AL.read_in_place r hd1 hd2 hd3 hd4 hd5 tl5 sz5 idx

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
let remove
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
  (requires fun h -> AL.mem (US.v idx) (US.v hd1)
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
  = AL.remove r hd1 hd2 hd3 hd4 hd5 tl5 sz5 idx

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
inline_for_extraction noextract
let remove1
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
  (requires fun h -> AL.mem (US.v idx) (US.v hd1)
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
  = remove r hd1 hd2 hd3 hd4 hd5 tl5 sz5 idx

inline_for_extraction noextract
let remove2
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
  (requires fun h -> AL.mem (US.v idx) (US.v hd2)
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
  = AL.permute12 pred1 pred2 pred3 pred4 pred5 r hd1 (US.v hd2) hd3 hd4 hd5 tl5 sz5;
    let v = remove r hd2 hd1 hd3 hd4 hd5 tl5 sz5 idx in
    AL.permute12 pred2 pred1 pred3 pred4 pred5 r (US.v v) hd1 hd3 hd4 hd5 tl5 sz5;
    return v

inline_for_extraction noextract
let remove3
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
  (requires fun h -> AL.mem (US.v idx) (US.v hd3)
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
  = AL.permute13 pred1 pred2 pred3 pred4 pred5 r hd1 hd2 (US.v hd3) hd4 hd5 tl5 sz5;
    let v = remove r hd3 hd2 hd1 hd4 hd5 tl5 sz5 idx in
    AL.permute13 pred3 pred2 pred1 pred4 pred5 r (US.v v) hd2 hd1 hd4 hd5 tl5 sz5;
    return v

let insert
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
  (ensures fun h0 _ h1 ->
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
  = AL.insert r hd hd2 hd3 hd4 hd5 tl5 sz5 idx v

let insert1
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
  (ensures fun h0 _ h1 ->
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
  = insert r hd hd2 hd3 hd4 hd5 tl5 sz5 idx v

let insert2
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
  (ensures fun h0 _ h1 ->
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
  = AL.permute12 pred1 pred2 pred3 pred4 pred5 r hd1 (US.v hd) hd3 hd4 hd5 tl5 sz5;
    insert r hd hd1 hd3 hd4 hd5 tl5 sz5 idx v;
    AL.permute12 pred2 pred1 pred3 pred4 pred5 r (US.v idx) hd1 hd3 hd4 hd5 tl5 sz5

let insert3
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
  (ensures fun h0 _ h1 ->
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
  = AL.permute13 pred1 pred2 pred3 pred4 pred5 r hd1 hd2 (US.v hd) hd4 hd5 tl5 sz5;
    insert r hd hd2 hd1 hd4 hd5 tl5 sz5 idx v;
    AL.permute13 pred3 pred2 pred1 pred4 pred5 r (US.v idx) hd2 hd1 hd4 hd5 tl5 sz5

let insert4
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
  (ensures fun h0 _ h1 ->
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
  =
  AL.permute14 pred1 pred2 pred3 pred4 pred5 r hd1 hd2 hd3 (US.v hd) hd5 tl5 sz5;
  insert r hd hd2 hd3 hd1 hd5 tl5 sz5 idx v;
  AL.permute14 pred4 pred2 pred3 pred1 pred5 r (US.v idx) hd2 hd3 hd1 hd5 tl5 sz5

let dequeue
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
  =
  AL.dequeue r hd5 tl5 sz5 hd1 hd2 hd3 hd4

let enqueue
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
  =
  AL.enqueue r hd5 tl5 sz5 hd1 hd2 hd3 hd4 idx v
