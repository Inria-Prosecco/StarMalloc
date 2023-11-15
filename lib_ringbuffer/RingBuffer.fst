module RingBuffer

module US = FStar.SizeT
open FStar.Mul

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array
module R = Steel.Reference

(*
This module is a rough implementation of a queue as a ring buffer,
which provides:
- constant-time enqueuing;
- constant-time dequeuing;
- constant-time access to the size of the queue's content;
- a maximum_size defined as below.
TODO: k_in and k_out names are really bad,
actually:
- k_out is the index where data can be enqueued;
- k_in is the index from which data can dequeued.
*)

let max_size = 32sz

noextract
let threshold (b: bool) (v: nat) : nat
  = if b then v else 0

noextract
let len
  (k_in k_out: (v:nat{v < US.v max_size}))
  : v:nat{v < US.v max_size}
  = k_out - k_in + threshold (k_out < k_in) (US.v max_size)

let ringbuffervprop_refine
  (data: (US.t & US.t) & US.t)
  : prop
  =
  //needed to distinguish between full case and empty case
  //(US.v (fst (fst data)) <> US.v (snd (fst data)) &&
  (
    let k_in = fst (fst data) in
    let k_out = snd (fst data) in
    let k_size = snd data in
    (US.v k_in < US.v max_size) &&
    (US.v k_out < US.v max_size) &&
    (US.v k_size = len (US.v k_in) (US.v k_out)) &&
    (US.v k_size < US.v max_size)
  )
  == true

// seq_nonrepeating
// nat instead of US.t
let ringbuffervprop
  (r: A.array US.t{A.length r == US.v max_size})
  (r_in r_out r_size: R.ref US.t)
  =
  A.varray r `star` (
    (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
    `vrefine`
    ringbuffervprop_refine
  )

noextract
let select
  (s: Seq.lseq US.t (US.v max_size))
  (k_in k_out: (v:nat{v < US.v max_size}))
  : Seq.lseq US.t (len k_in k_out)
  =
  if k_out >= k_in
  then Seq.slice s k_in k_out
  else (
    let s1 = Seq.slice s k_in (US.v max_size) in
    let s2 = Seq.slice s 0 k_out in
    Seq.append s1 s2
  )

let result' =
  (Seq.lseq US.t (US.v max_size) & Seq.seq US.t)
  &
  ((US.t & US.t) & US.t)

let result = v:result'{
  let idxs = snd v in
  let k_in = fst (fst idxs) in
  let k_out = snd (fst idxs) in
  let k_size = snd idxs in
  let s' = fst (fst v) in
  let s = snd (fst v) in
  ringbuffervprop_refine idxs /\
  Seq.length s == US.v k_size
}

[@@__steel_reduce__]
let v_rb
  (#vp: vprop)
  (r: A.array US.t{A.length r == US.v max_size})
  (r_in r_out r_size: R.ref US.t)
  (h:rmem vp{
    FStar.Tactics.with_tactic selector_tactic (can_be_split vp
      (ringbuffervprop r r_in r_out r_size)
    /\ True)
  })
  : GTot result
  =
  let packed
    : t_of (ringbuffervprop r r_in r_out r_size)
    = h (ringbuffervprop r r_in r_out r_size) in
  let s' : Seq.lseq US.t (US.v max_size) = fst packed in
  let idxs : (US.t & US.t) & US.t = snd packed in
  assert (ringbuffervprop_refine idxs);
  let k_in = fst (fst idxs) in
  let k_out = snd (fst idxs) in
  let k_size = snd idxs in
  let s = select s' (US.v k_in) (US.v k_out) in
  assert (Seq.length s = US.v k_size);
  ((s', s), idxs)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let select_enqueue_lemma
  (s0' s1': Seq.lseq US.t (US.v max_size))
  (k_in0 k_out0 k_in1 k_out1: (v:nat{v < US.v max_size}))
  (v: US.t)
  : Lemma
  (requires
    s1' == Seq.upd s0' k_out0 v /\
    k_in1 == k_in0 /\
    k_out1 == (k_out0 + 1) % (US.v max_size) /\
    len k_in0 k_out0 < US.v max_size - 1
  )
  (ensures
    select s1' k_in1 k_out1
    ==
    Seq.append
      (select s0' k_in0 k_out0)
      (Seq.create 1 v)
  )
  =
  let s0 = select s0' k_in0 k_out0 in
  let s1 = select s1' k_in1 k_out1 in
  if k_out0 >= k_in0
  then (
    assert (s0 == Seq.slice s0' k_in0 k_out0);
    if (k_out0 < US.v max_size - 1)
    then (
      assert (k_out1 == k_out0 + 1);
      Seq.lemma_split s1 (k_out0 - k_in0);
      Seq.lemma_eq_intro
        (Seq.slice s1' k_out0 (k_out0 + 1))
        (Seq.create 1 v)
    ) else (
      // size condition
      assert (k_out1 < k_in1);
      assert (s1 == Seq.append
        (Seq.slice s1' k_in1 (US.v max_size))
        (Seq.slice s1' 0 k_out1)
      );
      assert (Seq.slice s1' k_in1 (US.v max_size)
           == Seq.slice s1' k_in0 (k_out0 + 1));
      Seq.lemma_split (Seq.slice s1' k_in0 (k_out0 + 1)) (k_out0 - k_in0);
      Seq.lemma_eq_intro
        (Seq.slice s1' k_out0 (k_out0 + 1))
        (Seq.create 1 v);
      assert (Seq.slice s1' k_in1 (US.v max_size)
        == Seq.append
             (Seq.slice s0' k_in0 k_out0)
             (Seq.create 1 v));
      assert (k_out1 == 0);
      Seq.lemma_eq_intro
        (Seq.slice s1' 0 k_out1)
        (Seq.empty);
      Seq.append_empty_r (Seq.slice s1' k_in1 (US.v max_size))
    )
  ) else (
    // size condition
    assert (k_out1 < k_in1);
    let s01 = Seq.slice s0' k_in0 (US.v max_size) in
    let s11 = Seq.slice s1' k_in0 (US.v max_size) in
    let s02 = Seq.slice s0' 0 k_out0 in
    let s12 = Seq.slice s1' 0 k_out1 in
    assert (s0 == Seq.append s01 s02);
    assert (s1 == Seq.append s11 s12);
    Seq.lemma_split s12 k_out0;
    Seq.lemma_eq_intro
      (Seq.slice s1' k_out0 (k_out0 + 1))
      (Seq.create 1 v);
    Seq.append_assoc s01 s02 (Seq.create 1 v)
  )
#pop-options

module G = FStar.Ghost

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50 --split_queries no --query_stats"
let ring_bufferenqueue_aux
  (r: A.array US.t{A.length r == US.v max_size})
  (r_in r_out r_size: R.ref US.t)
  (v: US.t)
  : Steel unit
  (A.varray r `star`
    R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
  (fun _ -> A.varray r `star`
    R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
  (requires fun h0 ->
    let k_in = R.sel r_in h0 in
    let k_out = R.sel r_out h0 in
    let k_size = R.sel r_size h0 in
    US.v k_size < US.v max_size - 1 /\
    ringbuffervprop_refine ((k_in, k_out), k_size)
  )
  (ensures fun h0 _ h1 ->
    let k_in0 = R.sel r_in h0 in
    let k_out0 = R.sel r_out h0 in
    let k_size0 = R.sel r_size h0 in
    let s0' = A.asel r h0 in
    let k_in1 = R.sel r_in h1 in
    let k_out1 = R.sel r_out h1 in
    let k_size1 = R.sel r_size h1 in
    let s1' = A.asel r h1 in
    ringbuffervprop_refine ((k_in0, k_out0), k_size0) /\
    k_in0 = k_in1 /\
    k_out1 = US.rem (US.add k_out0 1sz) max_size /\
    k_size1 = US.add k_size0 1sz /\
    ringbuffervprop_refine ((k_in1, k_out1), k_size1) /\
    s1' == Seq.upd s0' (US.v k_out0) v /\
    select s1' (US.v k_in1) (US.v k_out1)
    == Seq.append (select s0' (US.v k_in0) (US.v k_out0))
                  (Seq.create 1 v)

  )
  =
  let k_out = R.read r_out in
  let k_size = R.read r_size in
  let h0 = get () in
  let s0 = G.hide (A.asel r h0) in
  let k_in0 = G.hide (R.sel r_in h0) in
  let k_out0 = G.hide (R.sel r_out h0) in
  A.upd r k_out v;
  R.write r_out (US.rem (US.add k_out 1sz) max_size);
  R.write r_size (US.add k_size 1sz);
  let h1 = get () in
  let s1 = G.hide (A.asel r h1) in
  let k_in1 = G.hide (R.sel r_in h1) in
  let k_out1 = G.hide (R.sel r_out h1) in
  select_enqueue_lemma
    s0 s1
    (US.v k_in0) (US.v k_out0)
    (US.v k_in1) (US.v k_out1)
    v;
  return ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
let ring_bufferenqueue
  (r: A.array US.t{A.length r == US.v max_size})
  (r_in r_out r_size: R.ref US.t)
  (v: US.t)
  : Steel unit
  (ringbuffervprop r r_in r_out r_size)
  (fun _ -> ringbuffervprop r r_in r_out r_size)
  (requires fun h0 ->
    let r : result = v_rb r r_in r_out r_size h0 in
    let k_size = snd (snd r) in
    US.v k_size < US.v max_size - 1
  )
  (ensures fun h0 _ h1 ->
    let r0 : result = v_rb r r_in r_out r_size h0 in
    let k_out0 = snd (fst (snd r0)) in
    let k_size0 = snd (snd r0) in
    let r1 : result = v_rb r r_in r_out r_size h1 in
    let k_out1 = snd (fst (snd r1)) in
    let k_size1 = snd (snd r1) in
    let s0' = fst (fst r0) in
    let s1' = fst (fst r1) in
    let s0 = snd (fst r0) in
    let s1 = snd (fst r1) in
    US.v k_size0 < US.v max_size /\
    US.v k_size1 <= US.v max_size /\
    US.v k_size1 == US.v k_size0 + 1 /\
    s1' = Seq.upd s0' (US.v k_out0) v /\
    s1 == Seq.append s0 (Seq.create 1 v)
  )
  =
  change_slprop_rel
    (ringbuffervprop r r_in r_out r_size)
    (A.varray r `star` (
      (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
      `vrefine`
      ringbuffervprop_refine
    ))
    (fun x y -> x == y)
    (fun _ -> admit ());
  elim_vrefine
    (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
    ringbuffervprop_refine;
  ring_bufferenqueue_aux r r_in r_out r_size v;
  intro_vrefine
    (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
    ringbuffervprop_refine;
  change_slprop_rel
    (A.varray r `star` (
      (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
      `vrefine`
      ringbuffervprop_refine
    ))
    (ringbuffervprop r r_in r_out r_size)
    (fun x y -> x == y)
    (fun _ -> admit ());
  return ()
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let select_dequeue_lemma
  (s0' s1': Seq.lseq US.t (US.v max_size))
  (k_in0 k_out0 k_in1 k_out1: (v:nat{v < US.v max_size}))
  //(v: US.t)
  : Lemma
  (requires
    s1' == s0' /\
    k_in1 == (k_in0 + 1) % (US.v max_size) /\
    k_out1 == k_out0 /\
    len k_in0 k_out0 > 0
  )
  (ensures (
    let v = Seq.index s1' k_in0 in
    Seq.append
      (Seq.create 1 v)
      (select s1' k_in1 k_out1)
    ==
    select s0' k_in0 k_out0
  ))
  =
  let s0 = select s0' k_in0 k_out0 in
  let s1 = select s1' k_in1 k_out1 in
  let v = Seq.index s0' k_in0 in
  if k_out0 >= k_in0
  then (
    assert (s0 == Seq.slice s0' k_in0 k_out0);
    assert (s1 == Seq.slice s0' k_in1 k_out0);
    assert (len k_in0 k_out0 == k_out0 - k_in0);
    Seq.lemma_split s0 1;
    Seq.lemma_eq_intro
      (Seq.slice s0 0 1)
      (Seq.create 1 v)
  ) else (
    admit ();
    let s01 = Seq.slice s0' k_in0 (US.v max_size) in
    let s02 = Seq.slice s0' 0 k_out0 in
    assert (s0 == Seq.append s01 s02);
    if (k_in0 < US.v max_size - 1) then (
      let s11 = Seq.slice s0' k_in1 (US.v max_size) in
      let s12 = Seq.slice s0' 0 k_out0 in
      assert (s1 == Seq.append s11 s12);
      Seq.slice_slice s0' k_in0 (US.v max_size) 1 (US.v max_size - k_in0);
      Seq.lemma_eq_intro s1 (Seq.slice s0 1 (Seq.length s0))
    ) else (
      assert (k_in0 == US.v max_size - 1);
      assert (k_in1 == 0);
      assert (s1 == s02);
      assert (Seq.length s01 = 1);
      Seq.lemma_eq_intro s1 (Seq.slice s0 1 (Seq.length s0))
    )
  )

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50 --split_queries no --query_stats"
let ring_bufferdequeue_aux
  (r: A.array US.t{A.length r == US.v max_size})
  (r_in r_out r_size: R.ref US.t)
  : Steel US.t
  (A.varray r `star`
    R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
  (fun _ -> A.varray r `star`
    R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
  (requires fun h0 ->
    let k_in = R.sel r_in h0 in
    let k_out = R.sel r_out h0 in
    let k_size = R.sel r_size h0 in
    US.v k_size > 0 /\
    ringbuffervprop_refine ((k_in, k_out), k_size)
  )
  (ensures fun h0 v h1 ->
    let k_in0 = R.sel r_in h0 in
    let k_out0 = R.sel r_out h0 in
    let k_size0 = R.sel r_size h0 in
    let s0' = A.asel r h0 in
    let k_in1 = R.sel r_in h1 in
    let k_out1 = R.sel r_out h1 in
    let k_size1 = R.sel r_size h1 in
    let s1' = A.asel r h1 in
    US.v k_size0 > 0 /\
    ringbuffervprop_refine ((k_in0, k_out0), k_size0) /\
    k_in1 = US.rem (US.add k_in0 1sz) max_size /\
    k_out1 = k_out0 /\
    k_size1 = US.sub k_size0 1sz /\
    ringbuffervprop_refine ((k_in1, k_out1), k_size1) /\
    // no need to overwrite value
    s1' == s0' /\
    // key part of the spec
    Seq.append
      (Seq.create 1 v)
      (select s1' (US.v k_in1) (US.v k_out1))
    ==
    select s0' (US.v k_in0) (US.v k_out0)
  )
  =
  let k_in = R.read r_in in
  let k_size = R.read r_size in
  let h0 = get () in
  let s0 = G.hide (A.asel r h0) in
  let k_in0 = G.hide (R.sel r_in h0) in
  let k_out0 = G.hide (R.sel r_out h0) in
  let v = A.index r k_in in
  R.write r_in (US.rem (US.add k_in 1sz) max_size);
  R.write r_size (US.sub k_size 1sz);
  let h1 = get () in
  let s1 = G.hide (A.asel r h1) in
  let k_in1 = G.hide (R.sel r_in h1) in
  let k_out1 = G.hide (R.sel r_out h1) in
  select_dequeue_lemma
    s0 s1
    (US.v k_in0) (US.v k_out0)
    (US.v k_in1) (US.v k_out1);
  return v
#pop-options

#push-options "--fuel 1 --ifuel 1"
let ring_bufferdequeue
  (r: A.array US.t{A.length r == US.v max_size})
  (r_in r_out r_size: R.ref US.t)
  : Steel US.t
  (ringbuffervprop r r_in r_out r_size)
  (fun _ -> ringbuffervprop r r_in r_out r_size)
  (requires fun h0 ->
    let r : result = v_rb r r_in r_out r_size h0 in
    let k_size = snd (snd r) in
    US.v k_size > 0
  )
  (ensures fun h0 v h1 ->
    let r0 : result = v_rb r r_in r_out r_size h0 in
    let k_in0 = fst (fst (snd r0)) in
    let k_size0 = snd (snd r0) in
    let r1 : result = v_rb r r_in r_out r_size h1 in
    let k_in1 = fst (fst (snd r1)) in
    let k_size1 = snd (snd r1) in
    let s0' = fst (fst r0) in
    let s1' = fst (fst r1) in
    let s0 = snd (fst r0) in
    let s1 = snd (fst r1) in
    US.v k_size0 > 0 /\
    US.v k_size1 >= 0 /\
    US.v k_size1 == US.v k_size0 - 1 /\
    s1' == s0' /\
    Seq.append (Seq.create 1 v) s1 == s0
  )
  =
  change_slprop_rel
    (ringbuffervprop r r_in r_out r_size)
    (A.varray r `star` (
      (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
      `vrefine`
      ringbuffervprop_refine
    ))
    (fun x y -> x == y)
    (fun _ -> admit ());
  elim_vrefine
    (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
    ringbuffervprop_refine;
  let v = ring_bufferdequeue_aux r r_in r_out r_size in
  intro_vrefine
    (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
    ringbuffervprop_refine;
  change_slprop_rel
    (A.varray r `star` (
      (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
      `vrefine`
      ringbuffervprop_refine
    ))
    (ringbuffervprop r r_in r_out r_size)
    (fun x y -> x == y)
    (fun _ -> admit ());
  return v
#pop-options

let ring_getsize
  (r_ringbuffer: A.array US.t{A.length r_ringbuffer == US.v max_size})
  (r_in r_out r_size: R.ref US.t)
  : Steel US.t
  (ringbuffervprop r_ringbuffer r_in r_out r_size)
  (fun _ -> ringbuffervprop r_ringbuffer r_in r_out r_size)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    let s : result = v_rb r_ringbuffer r_in r_out r_size h0 in
    h1 (ringbuffervprop r_ringbuffer r_in r_out r_size)
    ==
    h0 (ringbuffervprop r_ringbuffer r_in r_out r_size)
    /\
    r == snd (snd s) /\
    US.v r <= US.v max_size - 1
  )
  =
  change_slprop_rel
    (ringbuffervprop r_ringbuffer r_in r_out r_size)
    (A.varray r_ringbuffer `star` (
      (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
      `vrefine`
      ringbuffervprop_refine
    ))
    (fun x y -> x == y)
    (fun _ -> admit ());
  elim_vrefine
    (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
    ringbuffervprop_refine;
  let r = R.read r_size in
  intro_vrefine
    (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
    ringbuffervprop_refine;
  change_slprop_rel
    (A.varray r_ringbuffer `star` (
      (R.vptr r_in `star` R.vptr r_out `star` R.vptr r_size)
      `vrefine`
      ringbuffervprop_refine
    ))
    (ringbuffervprop r_ringbuffer r_in r_out r_size)
    (fun x y -> x == y)
    (fun _ -> admit ());
  return r
