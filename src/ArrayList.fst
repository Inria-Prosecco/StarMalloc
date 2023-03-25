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
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd1 hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
  : Steel status
          (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
          (fun _ -> varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4)
          (requires fun _ -> True)
          (ensures fun h0 result h1 ->
            result == AL.get_data (Seq.index (v_arraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4 h0) (US.v idx)) /\
            h0 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4) ==
            h1 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 hd4))
  = AL.read_in_place r hd1 hd2 hd3 hd4 idx

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
let remove
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd1:US.t)
  (hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)
          (fun hd' -> varraylist pred1 pred2 pred3 pred4 r (US.v hd') hd2 hd3 hd4)
          (requires fun h -> AL.mem (US.v idx) (US.v hd1) (h (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r (US.v hd') hd2 hd3 hd4) in
            AL.ptrs_in (US.v hd') gs1 ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd1) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            (~ (AL.mem_all (US.v idx) (US.v hd') hd2 hd3 hd4 gs1)) /\
            AL.dataify gs1 == AL.dataify gs0
          )
  = AL.remove r hd1 hd2 hd3 hd4 idx

/// Removes the element at offset [idx] from the dlist pointed to by [hd1]
inline_for_extraction noextract
let remove1
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd1:US.t)
  (hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)
          (fun hd' -> varraylist pred1 pred2 pred3 pred4 r (US.v hd') hd2 hd3 hd4)
          (requires fun h -> AL.mem (US.v idx) (US.v hd1) (h (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4)))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd1) hd2 hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r (US.v hd') hd2 hd3 hd4) in
            AL.ptrs_in (US.v hd') gs1 ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd1) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            (~ (AL.mem_all (US.v idx) (US.v hd') hd2 hd3 hd4 gs1)) /\
            AL.dataify gs1 == AL.dataify gs0
          )
  = remove r hd1 hd2 hd3 hd4 idx

inline_for_extraction noextract
let remove2
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd1:Ghost.erased nat)
  (hd2:US.t)
  (hd3 hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd2) hd3 hd4)
          (fun hd' -> varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd') hd3 hd4)
          (requires fun h -> AL.mem (US.v idx) (US.v hd2) (h (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd2) hd3 hd4)))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd2) hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd') hd3 hd4) in
            AL.ptrs_in (US.v hd') gs1 ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd2) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            (~ (AL.mem_all (US.v idx) hd1 (US.v hd') hd3 hd4 gs1)) /\
            AL.dataify gs1 == AL.dataify gs0
          )
  = AL.permute12 pred1 pred2 pred3 pred4 r hd1 (US.v hd2) hd3 hd4;
    let v = remove r hd2 hd1 hd3 hd4 idx in
    AL.permute12 pred2 pred1 pred3 pred4 r (US.v v) hd1 hd3 hd4;
    return v

inline_for_extraction noextract
let remove3
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd1:Ghost.erased nat)
  (hd2:Ghost.erased nat)
  (hd3:US.t)
  (hd4:Ghost.erased nat)
  (idx:US.t{US.v idx < A.length r})
   : Steel US.t
          (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd3) hd4)
          (fun hd' -> varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd') hd4)
          (requires fun h -> AL.mem (US.v idx) (US.v hd3) (h (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd3) hd4)))
          (ensures fun h0 hd' h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd3) hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd') hd4) in
            AL.ptrs_in (US.v hd') gs1 ==
            FS.remove (US.v idx) (AL.ptrs_in (US.v hd3) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            (~ (AL.mem_all (US.v idx) hd1 hd2 (US.v hd') hd4 gs1)) /\
            AL.dataify gs1 == AL.dataify gs0
          )
  = AL.permute13 pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd3) hd4;
    let v = remove r hd3 hd2 hd1 hd4 idx in
    AL.permute13 pred3 pred2 pred1 pred4 r (US.v v) hd2 hd1 hd4;
    return v

let insert
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 pred4 r (US.v hd) hd2 hd3 hd4)
          (fun _ -> varraylist pred1 pred2 pred3 pred4 r (US.v idx) hd2 hd3 hd4)
          (requires fun h -> pred1 v /\
            (~ (AL.mem_all (US.v idx) (US.v hd) hd2 hd3 hd4 (h (varraylist pred1 pred2 pred3 pred4 r (US.v hd) hd2 hd3 hd4)))))
          (ensures fun h0 _ h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd) hd2 hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r (US.v idx) hd2 hd3 hd4) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )
  = AL.insert r hd hd2 hd3 hd4 idx v

let insert1
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd2 hd3 hd4:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 pred4 r (US.v hd) hd2 hd3 hd4)
          (fun _ -> varraylist pred1 pred2 pred3 pred4 r (US.v idx) hd2 hd3 hd4)
          (requires fun h -> pred1 v /\
            (~ (AL.mem_all (US.v idx) (US.v hd) hd2 hd3 hd4 (h (varraylist pred1 pred2 pred3 pred4 r (US.v hd) hd2 hd3 hd4)))))
          (ensures fun h0 _ h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r (US.v hd) hd2 hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r (US.v idx) hd2 hd3 hd4) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )
  = insert r hd hd2 hd3 hd4 idx v

let insert2
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd3 hd4:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd) hd3 hd4)
          (fun _ -> varraylist pred1 pred2 pred3 pred4 r hd1 (US.v idx) hd3 hd4)
          (requires fun h -> pred2 v /\
            (~ (AL.mem_all (US.v idx) hd1 (US.v hd) hd3 hd4 (h (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd) hd3 hd4)))))
          (ensures fun h0 _ h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v hd) hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r hd1 (US.v idx) hd3 hd4) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )
  = AL.permute12 pred1 pred2 pred3 pred4 r hd1 (US.v hd) hd3 hd4;
    insert r hd hd1 hd3 hd4 idx v;
    AL.permute12 pred2 pred1 pred3 pred4 r (US.v idx) hd1 hd3 hd4

let insert3
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd2 hd4:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd) hd4)
          (fun _ -> varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v idx) hd4)
          (requires fun h -> pred3 v /\
            (~ (AL.mem_all (US.v idx) hd1 hd2 (US.v hd) hd4 (h (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd) hd4)))))
          (ensures fun h0 _ h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd) hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 (US.v idx) hd4) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )
  = AL.permute13 pred1 pred2 pred3 pred4 r hd1 hd2 (US.v hd) hd4;
    insert r hd hd2 hd1 hd4 idx v;
    AL.permute13 pred3 pred2 pred1 pred4 r (US.v idx) hd2 hd1 hd4

let insert4
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd:US.t)
  (hd1 hd2 hd3:Ghost.erased nat)
  (idx:US.t{idx <> null_ptr /\ US.v idx < A.length r})
  (v: status)
   : Steel unit
          (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 (US.v hd))
          (fun _ -> varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 (US.v idx))
          (requires fun h -> pred4 v /\
            (~ (AL.mem_all (US.v idx) hd1 hd2 hd3 (US.v hd) (h (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 (US.v hd))))))
          (ensures fun h0 _ h1 ->
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 (US.v hd)) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 r hd1 hd2 hd3 (US.v idx)) in
            AL.ptrs_in (US.v idx) gs1 ==
            FS.insert (US.v idx) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd1 gs1 == AL.ptrs_in hd1 gs0 /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.dataify gs1 == Seq.upd (AL.dataify gs0) (US.v idx) v
          )
  =
  AL.permute14 pred1 pred2 pred3 pred4 r hd1 hd2 hd3 (US.v hd);
  insert r hd hd2 hd3 hd1 idx v;
  AL.permute14 pred4 pred2 pred3 pred1 r (US.v idx) hd2 hd3 hd1

(*)
let extend
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd2 hd3 hd4:Ghost.erased nat)
  (k:US.t{US.v k + 1 <= A.length r /\ US.fits (US.v k + 1)})
  (v: status)
  : Steel unit
          (AL.varraylist pred1 pred2 pred3 pred4 (A.split_l r k) (US.v hd) hd2 hd3 hd4 `star`
            A.varray (A.split_l (A.split_r r k) 1sz))
          (fun _ ->
            AL.varraylist pred1 pred2 pred3 pred4 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3 hd4)
          (requires fun _ ->
            k <> null_ptr /\ pred1 v)
          (ensures fun h0 _ h1 ->
            A.length_fits r;
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 (A.split_l r k) (US.v hd) hd2 hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3 hd4) in
            AL.ptrs_in (US.v k) gs1 ==
            FS.insert (US.v k) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            AL.dataify gs1 == Seq.append (AL.dataify gs0) (Seq.create 1 v)
          )
  = AL.extend r hd hd2 hd3 hd4 k v

inline_for_extraction noextract
let extend1
  (#pred1 #pred2 #pred3 #pred4: status -> prop)
  (r:A.array cell)
  (hd:US.t{hd == null_ptr \/ US.v hd < A.length r})
  (hd2 hd3 hd4:Ghost.erased nat)
  (k:US.t{US.v k + 1 <= A.length r /\ US.fits (US.v k + 1)})
  (v: status)
  : Steel unit
          (AL.varraylist pred1 pred2 pred3 pred4 (A.split_l r k) (US.v hd) hd2 hd3 hd4 `star`
            A.varray (A.split_l (A.split_r r k) 1sz))
          (fun _ ->
            AL.varraylist pred1 pred2 pred3 pred4 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3 hd4)
          (requires fun _ ->
            k <> null_ptr /\ pred1 v)
          (ensures fun h0 _ h1 ->
            A.length_fits r;
            let gs0 = h0 (varraylist pred1 pred2 pred3 pred4 (A.split_l r k) (US.v hd) hd2 hd3 hd4) in
            let gs1 = h1 (varraylist pred1 pred2 pred3 pred4 (A.split_l r (k `US.add` 1sz)) (US.v k) hd2 hd3 hd4) in
            AL.ptrs_in (US.v k) gs1 ==
            FS.insert (US.v k) (AL.ptrs_in (US.v hd) gs0) /\
            AL.ptrs_in hd2 gs1 == AL.ptrs_in hd2 gs0 /\
            AL.ptrs_in hd3 gs1 == AL.ptrs_in hd3 gs0 /\
            AL.ptrs_in hd4 gs1 == AL.ptrs_in hd4 gs0 /\
            AL.dataify gs1 `Seq.equal` Seq.append (AL.dataify gs0) (Seq.create 1 v)
          )
  = extend r hd hd2 hd3 hd4 k v
