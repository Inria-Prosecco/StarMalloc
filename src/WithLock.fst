module WithLock

open FStar.Mul
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module A = Steel.Array
module R = Steel.Reference
module L = Steel.SpinLock
module SM = Steel.Memory
module US = FStar.SizeT
module G = FStar.Ghost

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"

let f_aux (a b c: Type)
  (p_lock: a -> vprop)
  (prevp: b -> vprop)
  (postvp: b -> c -> vprop)
  (v0: a)
  (v1: b)
  (lock: L.lock (p_lock v0))
  (postcond1: t_of (prevp v1) -> (r:c) -> t_of (postvp v1 r) -> prop)
  : Type
  = unit -> Steel c
  (p_lock v0 `star` prevp v1)
  (fun r -> p_lock v0 `star` postvp v1 r)
  (requires fun
    (h0: rmem (p_lock v0 `star` prevp v1)) ->
    True
  )
  (ensures fun
    (h0: rmem (p_lock v0 `star` prevp v1))
    (r: c)
    (h1: rmem (p_lock v0 `star` postvp v1 r)) ->
    let x0 : t_of (prevp v1) = h0 (prevp v1) in
    let x1 : t_of (postvp v1 r) = h1 (postvp v1 r) in
    postcond1 x0 r x1
  )

inline_for_extraction noextract
let with_lock
  (a b c: Type)
  (p_lock: a -> vprop)
  (prevp: b -> vprop)
  (postvp: b -> c -> vprop)
  (v0: a)
  (v1: b)
  (lock: L.lock (p_lock v0))
  (postcond1: t_of (prevp v1) -> (r:c) -> t_of (postvp v1 r) -> prop)
  (f: f_aux a b c p_lock prevp postvp v0 v1 lock postcond1)
  : Steel c
  (prevp v1)
  (fun r -> postvp v1 r)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let x0 : t_of (prevp v1) = h0 (prevp v1) in
    let x1 : t_of (postvp v1 r) = h1 (postvp v1 r) in
    postcond1 x0 r x1
  )
  =
  L.acquire lock;
  let r = f () in
  L.release lock;
  return r

open ROArray

let f_aux_roarray (z a b c: Type)
  (r: A.array z)
  (s: Seq.lseq z (A.length r))
  (p_lock: a -> vprop)
  (proj1: z -> a)
  (proj2: (x:z) -> L.lock (p_lock (proj1 x)))
  (prevp: b -> vprop)
  (postvp: b -> c -> vprop)
  (idx: US.t{US.v idx < A.length r})
  (v1: b)
  (postcond1:
    (idx:US.t{US.v idx < A.length r}) ->
    t_of (prevp v1) ->
    (r:c) ->
    t_of (postvp v1 r) -> prop)
  : Type
  = (v0:a) -> Steel c
  (p_lock v0 `star` prevp v1)
  (fun r -> p_lock v0 `star` postvp v1 r)
  (requires fun
    (h0: rmem (p_lock v0 `star` prevp v1)) ->
    v0 == proj1 (Seq.index s (US.v idx))
    //True
  )
  (ensures fun
    (h0: rmem (p_lock v0 `star` prevp v1))
    (r: c)
    (h1: rmem (p_lock v0 `star` postvp v1 r)) ->
    let x0 : t_of (prevp v1) = h0 (prevp v1) in
    let x1 : t_of (postvp v1 r) = h1 (postvp v1 r) in
    v0 == proj1 (Seq.index s (US.v idx)) /\
    postcond1 idx x0 r x1
  )

inline_for_extraction noextract
let with_lock_roarray
  (a b c z: Type)
  (r: A.array z)
  (s: G.erased (Seq.lseq z (A.length r)))
  (ro_arr: ro_array r s)
  (p_lock: a -> vprop)
  (proj1: z -> a)
  (proj2: (x:z) -> L.lock (p_lock (proj1 x)))
  (prevp: b -> vprop)
  (postvp: b -> c -> vprop)
  (v0: US.t{US.v v0 < A.length r})
  (v1: b)
  (postcond1: (idx: US.t{US.v idx < A.length r}) -> t_of (prevp v1) -> (r:c) -> t_of (postvp v1 r) -> prop)
  (f: f_aux_roarray z a b c r s p_lock proj1 proj2 prevp postvp v0 v1 postcond1)
  : Steel c
  (prevp v1)
  (fun r -> postvp v1 r)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let x0 : t_of (prevp v1) = h0 (prevp v1) in
    let x1 : t_of (postvp v1 r) = h1 (postvp v1 r) in
    postcond1 v0 x0 r x1
  )
  =
  let x = ROArray.index ro_arr v0 in
  L.acquire (proj2 x);
  //change_equal_slprop
  //  (p_lock (proj1 x))
  //  (p_lock (proj1 (Seq.index s (US.v v0))));
  let r = f (proj1 x) in
  //change_equal_slprop
  //  (p_lock (proj1 (Seq.index s (US.v v0))))
  //  (p_lock (proj1 x));
  L.release (proj2 x);
  return r
