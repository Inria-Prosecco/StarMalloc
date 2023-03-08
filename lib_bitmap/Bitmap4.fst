module Bitmap4

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Seq = FStar.Seq
module FBV = FStar.BitVector

open FStar.UInt
open FStar.Mul

noextract
let rec array_to_bv_aux
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (k: nat{k <= n})
  : FBV.bv_t (U64.n * k)
  = match k with
  | 0 -> Seq.empty
  | _ ->
      assert (k > 0);
      let idx = n - k in
      assert (0 <= idx /\ idx < n);
      let x = Seq.index s idx in
      let x : FBV.bv_t U64.n = to_vec #U64.n (U64.v x) in
      let s : FBV.bv_t (U64.n * (k - 1)) = array_to_bv_aux s (k - 1) in
      Seq.append x s

noextract
let array_to_bv
  (#n: nat)
  (s: Seq.lseq U64.t n)
  : FBV.bv_t (U64.n * n)
  = array_to_bv_aux #n s n

#push-options "--z3rlimit 50"
let rec array_to_bv_aux_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (k: nat{k <= n})
  (i:nat)
  : Lemma
  (requires i < U64.n * k)
  (ensures
    Seq.index (array_to_bv_aux s k) i
    =
    nth (U64.v (Seq.index s ((n-k)+i/U64.n))) (i%U64.n)
  )
  = match k with
  | 0 -> ()
  | _ ->
      assert (k > 0);
      let idx = n - k in
      assert (0 <= idx /\ idx < n);
      let x = Seq.index s idx in
      let s1 = to_vec #U64.n (U64.v x) in
      let s2 = array_to_bv_aux s (k - 1) in
      let r = Seq.append s1 s2 in
      Seq.lemma_split r U64.n;
      let idx1 = i/64*U64.n in
      let idx2 = (i/64+1)*U64.n in
      let idx3 = i%U64.n in
      assert (i = idx1 + idx3);
      Seq.lemma_index_slice r idx1 idx2 idx3;
      if i < U64.n
      then ()
      else begin
        array_to_bv_aux_lemma #n s (k-1) (i-U64.n);
        Seq.lemma_index_slice r U64.n (U64.n * k) (i-U64.n)
      end
#pop-options

let array_to_bv_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i:nat)
  : Lemma
  (requires i < U64.n * n)
  (ensures
    Seq.index (array_to_bv s) i
    =
    nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n)
  )
  = array_to_bv_aux_lemma #n s n i

//TODO: remove in favor of SeqUtils
noextract
let init_nat (len: nat)
  : Seq.lseq (k:nat{k < len}) len
  = Seq.init len (fun k -> k)

let init_nat_index (len: nat) (i:nat{i < len})
  : Lemma
  (Seq.index (init_nat len) i = i)
  = ()

noextract
let array_to_bv2
  (#n: nat)
  (s: Seq.lseq U64.t n)
  : Seq.lseq bool (n*U64.n)
  =
  let f = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let s0 = init_nat (U64.n * n) in
  Seq.map_seq_len f s0;
  let r = Seq.map_seq f s0 in
  r

let array_to_bv2_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  : Lemma
  (array_to_bv2 s == array_to_bv s)
  =
  let f = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let s0 = init_nat (U64.n * n) in
  Classical.forall_intro (
    init_nat_index (U64.n * n)
  );
  Classical.forall_intro (
    Classical.move_requires (
      fun (i:nat{i < U64.n * n}) -> array_to_bv_lemma #n s i
    )
  );
  Classical.forall_intro (Seq.map_seq_index f s0);
  Seq.lemma_eq_intro (array_to_bv2 s) (array_to_bv s)

let array_to_bv2_index
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: nat{i < n*U64.n})
  : Lemma
  (Seq.index (array_to_bv2 s) i
  == nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n))
  =
  let f = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let s0 = init_nat (U64.n * n) in
  Seq.map_seq_len f s0;
  init_nat_index (U64.n * n) i;
  Seq.map_seq_index f s0 i

noextract
unfold
let f_aux (k: nat{k < U64.n})
  : r:nat{r < U64.n}
  = U64.n - k - 1

noextract
unfold
let f (#n:nat)
  (k:nat{k < n * U64.n})
  : r:nat{r < n * U64.n}
  =
  let k1 = k/U64.n in
  let k2 = k%U64.n in
  k1*U64.n + (f_aux k2)

let f_lemma (#n: nat) (k:nat{k < n * U64.n})
  : Lemma
  (k / U64.n = (f #n k ) / U64.n)
  = ()

let lemma_index_slice (#a:Type) (s:Seq.seq a)
  (i:nat) (j:nat{i <= j /\ j <= Seq.length s}) (k:nat{k < j - i})
  : Lemma
  (Seq.index (Seq.slice s i j) k == Seq.index s (k + i))
  = Seq.lemma_index_slice s i j k

let array_to_bv_lemma_upd_set_aux1
  (#n: nat)
  (s0 s1: Seq.lseq U64.t n)
  (op: U64.t -> (m:U32.t{U32.v m < U64.n}) -> U64.t)
  (i: nat)
  : Lemma
  (requires
    i < U64.n * n /\
    s1 == Seq.upd s0 (i/64) (op (Seq.index s0 (i/64)) (U32.uint_to_t (i%64)))
  )
  (ensures (
    let bm0 = array_to_bv2 s0 in
    let bm1 = array_to_bv2 s1 in
    forall (j:nat{j < n * U64.n /\ j/64 <> i/64}).
      Seq.index bm0 j = Seq.index bm1 j
  ))
  =
  assert (forall (j:nat{j < n /\ j <> i/64}). Seq.index s0 j = Seq.index s1 j);
  let s_init = init_nat (U64.n * n) in
  Classical.forall_intro (
    init_nat_index (U64.n * n)
  );
  let f0 = fun (i:nat{i < U64.n*n})
        -> nth (U64.v (Seq.index s0 (i/U64.n))) (i%U64.n) in
  let f1 = fun (i:nat{i < U64.n*n})
        -> nth (U64.v (Seq.index s1 (i/U64.n))) (i%U64.n) in
  Seq.map_seq_len f0 s_init;
  Seq.map_seq_len f1 s_init;
  Classical.forall_intro (Seq.map_seq_index f0 s_init);
  Classical.forall_intro (Seq.map_seq_index f1 s_init)

let array_to_bv_lemma_upd_set_aux2
  (#n: nat)
  (s0 s1: Seq.lseq U64.t n)
  (op: U64.t -> (m:U32.t{U32.v m < U64.n}) -> U64.t)
  (i: nat)
  : Lemma
  (requires
    i < U64.n * n /\
    s1 == Seq.upd s0 (i/64) (op (Seq.index s0 (i/64)) (U32.uint_to_t (i%64)))
  )
  (ensures (
    let bm0 = array_to_bv2 s0 in
    let bm1 = array_to_bv2 s1 in
    Seq.slice bm0 0 (i/64*64)
    =
    Seq.slice bm1 0 (i/64*64)
  ))
  =
  array_to_bv_lemma_upd_set_aux1 #n s0 s1 op i;
  let bm0 = array_to_bv2 s0 in
  let bm1 = array_to_bv2 s1 in
  assert (forall (j:nat{j < n * U64.n /\ j/64 <> i/64}).
    Seq.index bm0 j = Seq.index bm1 j
  );
  Classical.forall_intro (
      lemma_index_slice bm0 0 (i/64*64)
  );
  Classical.forall_intro (
      lemma_index_slice bm1 0 (i/64*64)
  );
  Seq.lemma_eq_intro
    (Seq.slice bm0 0 (i/64*64))
    (Seq.slice bm1 0 (i/64*64))

let array_to_bv_lemma_upd_set_aux3
  (#n: nat)
  (s0 s1: Seq.lseq U64.t n)
  (op: U64.t -> (m:U32.t{U32.v m < U64.n}) -> U64.t)
  (i: nat)
  : Lemma
  (requires
    i < U64.n * (n - 1) /\
    s1 == Seq.upd s0 (i/64) (op (Seq.index s0 (i/64)) (U32.uint_to_t (i%64)))
  )
  (ensures (
    let bm0 = array_to_bv2 s0 in
    let bm1 = array_to_bv2 s1 in
    Seq.slice bm0 ((i/64+1)*64) (n*64)
    =
    Seq.slice bm1 ((i/64+1)*64) (n*64)
  ))
  =
  array_to_bv_lemma_upd_set_aux1 #n s0 s1 op i;
  let bm0 = array_to_bv2 s0 in
  let bm1 = array_to_bv2 s1 in
  assert (forall (j:nat{j < n * U64.n /\ j/64 <> i/64}).
    Seq.index bm0 j = Seq.index bm1 j
  );
  Classical.forall_intro (
      lemma_index_slice bm0 ((i/64+1)*64) (n*64)
  );
  Classical.forall_intro (
      lemma_index_slice bm1 ((i/64+1)*64) (n*64)
  );
  Seq.lemma_eq_intro
    (Seq.slice bm0 ((i/64+1)*64) (n*64))
    (Seq.slice bm1 ((i/64+1)*64) (n*64))

#push-options "--z3rlimit 30"
let array_to_bv_lemma_upd_set_aux4
  (#n: nat)
  (s0: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires
    i < U64.n * n
  )
  (ensures (
    let bm0 = array_to_bv2 s0 in
    let x = Seq.index s0 (i/64) in
    Seq.slice bm0 (i/64*64) ((i/64+1)*64)
    =
    to_vec #64 (U64.v x)))
  =
  let bm0 = array_to_bv2 s0 in
  let s_init = init_nat (U64.n * n) in
  Classical.forall_intro (
    init_nat_index (U64.n * n)
  );
  let f0 = fun (i:nat{i < U64.n*n})
        -> nth (U64.v (Seq.index s0 (i/U64.n))) (i%U64.n) in
  let x = Seq.index s0 (i/64) in
  Classical.forall_intro (Seq.map_seq_index f0 s_init);
  Classical.forall_intro (lemma_index_slice bm0 (i/64*64) ((i/64+1)*64));
  Seq.lemma_eq_intro
    (Seq.slice bm0 (i/64*64) ((i/64+1)*64))
    (to_vec #64 (U64.v x))
#pop-options

let array_to_bv2_singleton_index
  (s: Seq.lseq U64.t 1)
  (i: nat{i < U64.n})
  : Lemma
  (Seq.index (array_to_bv2 s) i
  == nth (U64.v (Seq.index s 0)) i)
  =
  assert (i / U64.n == 0);
  assert (i % U64.n == i);
  array_to_bv2_index #1 s i

let array_to_bv2_singleton_index2
  (s: Seq.lseq U64.t 1)
  : Lemma
  (array_to_bv2 s
  == to_vec #64 (U64.v (Seq.index s 0)))
  =
  Classical.forall_intro (array_to_bv2_singleton_index s);
  Seq.lemma_eq_intro
    (array_to_bv2 s)
    (to_vec #64 (U64.v (Seq.index s 0)))

let array_to_bv2_slice
  (#n: nat)
  (s0: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires
    i < n
  )
  (ensures (
    let bm0 = array_to_bv2 s0 in
    let x = Seq.index s0 i in
    Seq.slice bm0 (i*64) ((i+1)*64)
    =
    to_vec #64 (U64.v x)))
  =
  array_to_bv_lemma_upd_set_aux4 s0 (i*64)

#push-options "--print_implicits"

let array_to_bv2_append_aux1 (#n1 #n2: nat)
  (s1: Seq.lseq U64.t n1)
  (s2: Seq.lseq U64.t n2)
  (i: nat{i < U64.n * n1})
  : Lemma
  (let n = n1 + n2 in
  let s = Seq.append s1 s2 in
  let f0 = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let w0 = init_nat (U64.n * n) in
  let w01 = Seq.slice w0 0 (U64.n * n1) in
  f0 (Seq.index w01 i)
  ==
  Seq.index (array_to_bv2 #n1 s1) i)
  =
  let n = n1 + n2 in
  let s = Seq.append s1 s2 in
  let f0 = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let w0 = init_nat (U64.n * n) in
  let f1 = fun (i:nat{i < U64.n*n1})
       -> nth (U64.v (Seq.index s1 (i/U64.n))) (i%U64.n) in
  let w1 = init_nat (U64.n * n1) in
  assert_norm (array_to_bv2 #n1 s1 == Seq.map_seq f1 w1);
  Seq.map_seq_index f1 w1 i;
  assert (Seq.index (array_to_bv2 #n1 s1) i == f1 (Seq.index w1 i));
  init_nat_index (U64.n * n) i;
  init_nat_index (U64.n * n1) i;
  lemma_index_slice w0 0 (U64.n * n1) i;
  lemma_index_slice s 0 n1 (i/U64.n)

let array_to_bv2_append_aux2 (#n1 #n2: nat)
  (s1: Seq.lseq U64.t n1)
  (s2: Seq.lseq U64.t n2)
  (i: nat{i < U64.n * n2})
  : Lemma
  (let n = n1 + n2 in
  let s = Seq.append s1 s2 in
  let f0 = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let w0 = init_nat (U64.n * n) in
  let w02 = Seq.slice w0 (U64.n * n1) (U64.n * n) in
  f0 (Seq.index w02 i)
  ==
  Seq.index (array_to_bv2 #n2 s2) i)
  =
  let n = n1 + n2 in
  let s = Seq.append s1 s2 in
  let f0 = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let w0 = init_nat (U64.n * n) in
  let f2 = fun (i:nat{i < U64.n*n2})
       -> nth (U64.v (Seq.index s2 (i/U64.n))) (i%U64.n) in
  let w2 = init_nat (U64.n * n2) in
  assert_norm (array_to_bv2 #n2 s2 == Seq.map_seq f2 w2);
  Seq.map_seq_index f2 w2 i;
  assert (Seq.index (array_to_bv2 #n2 s2) i == f2 (Seq.index w2 i));
  init_nat_index (U64.n * n) (U64.n * n1 + i);
  init_nat_index (U64.n * n2) i;
  lemma_index_slice w0 (U64.n * n1) (U64.n * n) i;
  lemma_index_slice s n1 n (i/U64.n)

let array_to_bv2_append (#n1 #n2: nat)
  (s1: Seq.lseq U64.t n1)
  (s2: Seq.lseq U64.t n2)
  : Lemma
  (array_to_bv2 #(n1+n2) (Seq.append s1 s2)
  ==
  Seq.append (array_to_bv2 #n1 s1) (array_to_bv2 #n2 s2))
  =
  let n = n1 + n2 in
  let s = Seq.append s1 s2 in
  assert (Seq.length s == n);
  let f0 = fun (i:nat{i < U64.n*n})
       -> nth (U64.v (Seq.index s (i/U64.n))) (i%U64.n) in
  let w0 = init_nat (U64.n * n) in
  let r0 = Seq.map_seq f0 w0 in
  assert_norm (r0 == array_to_bv2 #n s);
  let f1 = fun (i:nat{i < U64.n*n1})
       -> nth (U64.v (Seq.index s1 (i/U64.n))) (i%U64.n) in
  let w1 = init_nat (U64.n * n1) in
  let r1 = Seq.map_seq f1 w1 in
  assert_norm (r1 == array_to_bv2 #n1 s1);
  let f2 = fun (i:nat{i < U64.n*n2})
       -> nth (U64.v (Seq.index s2 (i/U64.n))) (i%U64.n) in
  let w2 = init_nat (U64.n * n2) in
  let r2 = Seq.map_seq f2 w2 in
  assert_norm (r2 == array_to_bv2 #n2 s2);
  Seq.lemma_split w0 (U64.n * n1);
  let w01 = Seq.slice w0 0 (U64.n * n1) in
  let w02 = Seq.slice w0 (U64.n * n1) (U64.n * n) in
  Classical.forall_intro (array_to_bv2_append_aux1 #n1 #n2 s1 s2);
  Seq.map_seq_len f0 w01;
  Classical.forall_intro (Seq.map_seq_index f0 w01);
  Seq.lemma_eq_intro (array_to_bv2 #n1 s1) (Seq.map_seq f0 w01);
  assert (r1 == Seq.map_seq f0 w01);

  Classical.forall_intro (array_to_bv2_append_aux2 #n1 #n2 s1 s2);
  Seq.map_seq_len f0 w02;
  Classical.forall_intro (Seq.map_seq_index f0 w02);
  Seq.lemma_eq_intro (array_to_bv2 #n2 s2) (Seq.map_seq f0 w02);

  assert (r2 == Seq.map_seq f0 w02);
  Seq.map_seq_append f0 w01 w02

let rec array_to_bv2_slice2 (#n: nat)
  (s: Seq.lseq U64.t n)
  (i j:nat)
  : Lemma
  (requires
    0 <= i /\ i < j /\ j <= n)
  (ensures
    array_to_bv2 #(j-i) (Seq.slice s i j)
    ==
    Seq.slice (array_to_bv2 s) (i*64) (j*64))
  (decreases (j-i))
  =
  match (j - i) with
  | 0 -> Seq.lemma_empty (array_to_bv2 #(j-i) (Seq.slice s i j))
  | 1 ->
    array_to_bv2_slice #n s i;
    assert (Seq.slice (array_to_bv2 s) (i*64) ((i+1)*64)
    == to_vec #64 (U64.v (Seq.index s i)));
    array_to_bv2_singleton_index2 (Seq.slice s i j)
  | _ ->
    let s11 = array_to_bv2 #(j-1-i) (Seq.slice s i (j-1)) in
    let s12 = Seq.slice (array_to_bv2 s) (i*64) ((j-1)*64) in
    let s21 = array_to_bv2 #1 (Seq.slice s (j-1) j) in
    let s22 = Seq.slice (array_to_bv2 s) ((j-1)*64) (j*64) in
    array_to_bv2_slice2 #n s i (j-1);
    array_to_bv2_slice2 #n s (j-1) j;
    assert (s11 == s12);
    assert (s21 == s22);
    let s1 = array_to_bv2 #(j-i) (Seq.slice s i j) in
    let s2 = Seq.slice (array_to_bv2 s) (i*64) (j*64) in
    // 1
    Seq.lemma_split (Seq.slice s i j) (j-1-i);
    array_to_bv2_append #(j-1-i) #1
      (Seq.slice s i (j-1))
      (Seq.slice s (j-1) j);
    assert (s1 == Seq.append s11 s21);
    // 2
    Seq.lemma_split s2 ((j-1-i)*64);
    assert (s2 == Seq.append s12 s22)

let rec array_to_bv2_inj (#n: nat)
  (s1 s2: Seq.lseq U64.t n)
  : Lemma
  (requires array_to_bv2 s1 == array_to_bv2 s2)
  (ensures s1 == s2)
  (decreases n)
  = match n with
  | 0 -> Seq.lemma_empty s1; Seq.lemma_empty s2
  | 1 ->
    let bm1 = array_to_bv2 s1 in
    let bm2 = array_to_bv2 s2 in
    let x1 = Seq.index s1 0 in
    let x2 = Seq.index s2 0 in
    Classical.forall_intro (array_to_bv2_singleton_index s1);
    Classical.forall_intro (array_to_bv2_singleton_index s2);
    assert (forall (i:nat{i < U64.n}).
      Seq.index bm1 i == nth (U64.v x1) i
    );
    assert (forall (i:nat{i < U64.n}).
      Seq.index bm2 i == nth (U64.v x2) i
    );
    assert (forall (i:nat{i < U64.n}).
      Seq.index bm1 i == Seq.index (to_vec #64 (U64.v x1)) i
    );
    assert (forall (i:nat{i < U64.n}).
      Seq.index bm2 i == Seq.index (to_vec #64 (U64.v x2)) i
    );
    Seq.lemma_eq_intro
      (to_vec #64 (U64.v x1))
      (to_vec #64 (U64.v x2));
    to_vec_lemma_2 (U64.v x1) (U64.v x2);
    assert (x1 == x2);
    Seq.lemma_eq_intro s1 s2
  | n ->
    let s11,s12 = Seq.split s1 1 in
    let s21,s22 = Seq.split s2 1 in
    Seq.lemma_split s1 1;
    Seq.lemma_split s2 1;
    array_to_bv2_slice2 #n s1 0 1;
    array_to_bv2_slice2 #n s2 0 1;
    array_to_bv2_slice2 #n s1 1 n;
    array_to_bv2_slice2 #n s2 1 n;
    array_to_bv2_inj #1 s11 s21;
    array_to_bv2_inj #(n-1) s12 s22

#push-options "--z3rlimit 80"
let array_to_bv_lemma_upd_set
  (#n: nat)
  (s0 s1: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires
    i < U64.n * n /\
    Seq.index (array_to_bv2 s0) (f #n i) = false /\
    s1 == Seq.upd s0 (i/64) (Bitmap3.set (Seq.index s0 (i/64)) (U32.uint_to_t (i%64)))
  )
  (ensures
    array_to_bv2 s1
    ==
    Seq.upd (array_to_bv2 s0) (f #n i) true
  )
  =
  let bm0 = array_to_bv2 s0 in
  let bm1 = array_to_bv2 s1 in
  let s_init = init_nat (U64.n * n) in
  Classical.forall_intro (
    init_nat_index (U64.n * n)
  );
  let f0 = fun (i:nat{i < U64.n*n})
        -> nth (U64.v (Seq.index s0 (i/U64.n))) (i%U64.n) in
  let f1 = fun (i:nat{i < U64.n*n})
        -> nth (U64.v (Seq.index s1 (i/U64.n))) (i%U64.n) in
  (* i/64*64 - (i/64+1)*64 *)
  let x = Seq.index s0 (i/64) in
  let x' = Bitmap3.set x (U32.uint_to_t (i%64)) in
  f_lemma #n i;
  assert (Seq.index bm0 (f #n i) = false);
  Seq.map_seq_index f0 s_init (f #n i);
  assert (nth (U64.v x) (f_aux (i%64)) = false);
  Bitmap3.bv_set_lemma x (U32.uint_to_t (i%64));
  assert (nth (U64.v (Seq.index s1 (i/64))) (f_aux (i%64)) = true);
  Seq.map_seq_index f1 s_init (f #n i);
  assert (Seq.index bm1 (f #n i) = true);

  let bm0_1 = Seq.slice bm0 0 (i/64*64) in
  let bm0_2 = Seq.slice bm0 (i/64*64) ((i/64+1)*64) in
  let bm0_12 = Seq.slice bm0 0 ((i/64+1)*64) in
  let bm1_1 = Seq.slice bm1 0 (i/64*64) in
  let bm1_2 = Seq.slice bm1 (i/64*64) ((i/64+1)*64) in
  let bm1_12 = Seq.slice bm1 0 ((i/64+1)*64) in
  array_to_bv_lemma_upd_set_aux4 #n s0 i;
  array_to_bv_lemma_upd_set_aux4 #n s1 i;
  assert (bm0_2 == to_vec #64 (U64.v x));
  assert (bm1_2 == to_vec #64 (U64.v x'));

  assert (
    to_vec #64 (U64.v x')
  = Seq.upd (to_vec #64 (U64.v x)) (f_aux (i%64)) true);

  assert (bm1_2 == Seq.upd bm0_2 (f_aux (i%64)) true);

  Seq.lemma_split bm0_12 (i/64*64);
  Seq.lemma_eq_intro (Seq.append bm0_1 bm0_2) bm0_12;
  Seq.lemma_split bm1_12 (i/64*64);
  Seq.lemma_eq_intro (Seq.append bm1_1 bm1_2) bm1_12;

  Seq2.append_upd1 bm0_1 bm0_2 (f_aux (i%64)) true;
  array_to_bv_lemma_upd_set_aux2 #n s0 s1 Bitmap3.set i;
  assert (bm0_1 == bm1_1);
  assert (
    bm1_12
    ==
    Seq.upd bm0_12 (f #n i) true
  );
  assert (i/64 <= n-1);
  if (i/64 = n-1)
  then begin
    Seq.lemma_eq_intro bm1_12 bm1;
    Seq.lemma_eq_intro bm0_12 bm0
  end else begin
    let bm0_3 = Seq.slice bm0 ((i/64+1)*64) (n*64) in
    let bm1_3 = Seq.slice bm1 ((i/64+1)*64) (n*64) in
    array_to_bv_lemma_upd_set_aux3 #n s0 s1 Bitmap3.set i;
    assert (bm0_3 == bm1_3);

    Seq.lemma_split bm0 ((i/64+1)*64);
    Seq.lemma_eq_intro (Seq.append bm0_12 bm0_3) bm0;
    Seq.lemma_split bm1 ((i/64+1)*64);
    Seq.lemma_eq_intro (Seq.append bm1_12 bm1_3) bm1;
    Seq2.append_upd2 bm0_12 bm0_3 (f #n i) true
  end
#pop-options

#push-options "--z3rlimit 80"
let array_to_bv_lemma_upd_unset
  (#n: nat)
  (s0 s1: Seq.lseq U64.t n)
  (i: nat)
  : Lemma
  (requires
    i < U64.n * n /\
    Seq.index (array_to_bv2 s0) (f #n i) = true /\
    s1 == Seq.upd s0 (i/64) (Bitmap3.unset (Seq.index s0 (i/64)) (U32.uint_to_t (i%64)))
  )
  (ensures
    array_to_bv2 s1
    ==
    Seq.upd (array_to_bv2 s0) (f #n i) false
  )
  =
  let bm0 = array_to_bv2 s0 in
  let bm1 = array_to_bv2 s1 in
  let s_init = init_nat (U64.n * n) in
  Classical.forall_intro (
    init_nat_index (U64.n * n)
  );
  let f0 = fun (i:nat{i < U64.n*n})
        -> nth (U64.v (Seq.index s0 (i/U64.n))) (i%U64.n) in
  let f1 = fun (i:nat{i < U64.n*n})
        -> nth (U64.v (Seq.index s1 (i/U64.n))) (i%U64.n) in
  (* i/64*64 - (i/64+1)*64 *)
  let x = Seq.index s0 (i/64) in
  let x' = Bitmap3.unset x (U32.uint_to_t (i%64)) in
  f_lemma #n i;
  assert (Seq.index bm0 (f #n i) = true);
  Seq.map_seq_index f0 s_init (f #n i);
  assert (nth (U64.v x) (f_aux (i%64)) = true);
  Bitmap3.bv_unset_lemma x (U32.uint_to_t (i%64));
  assert (nth (U64.v (Seq.index s1 (i/64))) (f_aux (i%64)) = false);
  Seq.map_seq_index f1 s_init (f #n i);
  assert (Seq.index bm1 (f #n i) = false);

  let bm0_1 = Seq.slice bm0 0 (i/64*64) in
  let bm0_2 = Seq.slice bm0 (i/64*64) ((i/64+1)*64) in
  let bm0_12 = Seq.slice bm0 0 ((i/64+1)*64) in
  let bm1_1 = Seq.slice bm1 0 (i/64*64) in
  let bm1_2 = Seq.slice bm1 (i/64*64) ((i/64+1)*64) in
  let bm1_12 = Seq.slice bm1 0 ((i/64+1)*64) in
  array_to_bv_lemma_upd_set_aux4 #n s0 i;
  array_to_bv_lemma_upd_set_aux4 #n s1 i;
  assert (bm0_2 == to_vec #64 (U64.v x));
  assert (bm1_2 == to_vec #64 (U64.v x'));

  assert (
    to_vec #64 (U64.v x')
  = Seq.upd (to_vec #64 (U64.v x)) (f_aux (i%64)) false);

  assert (bm1_2 == Seq.upd bm0_2 (f_aux (i%64)) false);

  Seq.lemma_split bm0_12 (i/64*64);
  Seq.lemma_eq_intro (Seq.append bm0_1 bm0_2) bm0_12;
  Seq.lemma_split bm1_12 (i/64*64);
  Seq.lemma_eq_intro (Seq.append bm1_1 bm1_2) bm1_12;

  Seq2.append_upd1 bm0_1 bm0_2 (f_aux (i%64)) false;
  array_to_bv_lemma_upd_set_aux2 #n s0 s1 Bitmap3.unset i;
  assert (bm0_1 == bm1_1);
  assert (
    bm1_12
    ==
    Seq.upd bm0_12 (f #n i) false
  );
  assert (i/64 <= n-1);
  if (i/64 = n-1)
  then begin
    Seq.lemma_eq_intro bm1_12 bm1;
    Seq.lemma_eq_intro bm0_12 bm0
  end else begin
    let bm0_3 = Seq.slice bm0 ((i/64+1)*64) (n*64) in
    let bm1_3 = Seq.slice bm1 ((i/64+1)*64) (n*64) in
    array_to_bv_lemma_upd_set_aux3 #n s0 s1 Bitmap3.unset i;
    assert (bm0_3 == bm1_3);

    Seq.lemma_split bm0 ((i/64+1)*64);
    Seq.lemma_eq_intro (Seq.append bm0_12 bm0_3) bm0;
    Seq.lemma_split bm1 ((i/64+1)*64);
    Seq.lemma_eq_intro (Seq.append bm1_12 bm1_3) bm1;
    Seq2.append_upd2 bm0_12 bm0_3 (f #n i) false
  end
#pop-options

noextract
let get
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : bool
  =
  let i1 = U32.div i 64ul in
  let i2 = U32.rem i 64ul in
  let x = Seq.index s (U32.v i1) in
  Bitmap3.get x i2

let get_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (get s i = nth
    (U64.v (Seq.index s (U32.v i / U64.n)))
    (U64.n - (U32.v i % U64.n) - 1))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  Bitmap3.bv_get_lemma x i2

module FU = FStar.UInt

#push-options "--z3rlimit 50"
let get_lemma2
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (let bm = array_to_bv2 s in
  let idx = f #n (U32.v i) in
  let r = get s i in
  r = Seq.index bm idx
  )
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  let r = Bitmap3.get x i2 in
  Bitmap3.bv_get_lemma x i2;
  assert (r == FU.nth (U64.v (Seq.index s (U32.v i1))) (f_aux (U32.v i2)));
  let i' = f #n (U32.v i) in
  array_to_bv_lemma s i';
  assert (r == Seq.index (array_to_bv s) i');
  array_to_bv2_lemma s


noextract
let set
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Seq.lseq U64.t n
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  let x' = Bitmap3.set x i2 in
  Seq.upd s (U32.v i1) x'

let set_lemma2
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (requires (
    let idx = f #n (U32.v i) in
    let bm0 = array_to_bv2 s in
    Seq.index bm0 idx = false))
  (ensures (
    let idx = f #n (U32.v i) in
    let s' = set s i in
    let bm1 = array_to_bv2 s in
    let bm2 = array_to_bv2 s' in
    Seq.index bm2 idx = true /\
    bm2 == Seq.upd bm1 idx true))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  let x' = Bitmap3.set x i2 in
  let s' = Seq.upd s (U32.v i1) x' in
  let i' = f #n (U32.v i) in
  let bm0 = array_to_bv #n s in
  let bm1 = array_to_bv #n s' in
  array_to_bv2_lemma s;
  array_to_bv_lemma s i';
  assert (Seq.index bm0 i' = false);
  f_lemma #n (U32.v i);
  assert (i' / U64.n = U32.v i1);
  Bitmap3.bv_set_lemma x i2;
  array_to_bv_lemma #n s' i';
  array_to_bv2_lemma #n s';
  assert (Seq.index bm1 i' = true);
  array_to_bv_lemma_upd_set s s' (U32.v i);
  Seq.lemma_eq_intro bm1 (Seq.upd bm0 i' true)

let set_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (requires
    nth (U64.v (Seq.index s (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = false)
  (ensures (
    let s' = set s i in
    nth (U64.v (Seq.index s' (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = true))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  Bitmap3.bv_set_lemma x i2

noextract
let unset
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Seq.lseq U64.t n
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  let x' = Bitmap3.unset x i2 in
  Seq.upd s (U32.v i1) x'

let unset_lemma2
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (requires (
    let idx = f #n (U32.v i) in
    let bm0 = array_to_bv2 s in
    Seq.index bm0 idx = true))
  (ensures (
    let idx = f #n (U32.v i) in
    let s' = unset s i in
    let bm1 = array_to_bv2 s in
    let bm2 = array_to_bv2 s' in
    Seq.index bm2 idx = false /\
    bm2 == Seq.upd bm1 idx false))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  let x' = Bitmap3.unset x i2 in
  let s' = Seq.upd s (U32.v i1) x' in
  let i' = f #n (U32.v i) in
  let bm0 = array_to_bv #n s in
  let bm1 = array_to_bv #n s' in
  array_to_bv2_lemma s;
  array_to_bv_lemma s i';
  assert (Seq.index bm0 i' = true);
  f_lemma #n (U32.v i);
  assert (i' / U64.n = U32.v i1);
  Bitmap3.bv_unset_lemma x i2;
  array_to_bv_lemma #n s' i';
  array_to_bv2_lemma #n s';
  assert (Seq.index bm1 i' = false);
  array_to_bv_lemma_upd_unset s s' (U32.v i);
  Seq.lemma_eq_intro bm1 (Seq.upd bm0 i' false)

let unset_lemma
  (#n: nat)
  (s: Seq.lseq U64.t n)
  (i: U32.t{U32.v i < U64.n * n})
  : Lemma
  (requires
    nth (U64.v (Seq.index s (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = true)
  (ensures (
    let s' = unset s i in
    nth (U64.v (Seq.index s' (U32.v i / U64.n)))
        (U64.n - (U32.v i % U64.n) - 1) = false))
  =
  let i1 = U32.div i 64ul in
  assert (U32.v i1 = U32.v i / U64.n);
  let i2 = U32.rem i 64ul in
  assert (U32.v i2 = U32.v i % U64.n);
  let x = Seq.index s (U32.v i1) in
  Bitmap3.bv_unset_lemma x i2
