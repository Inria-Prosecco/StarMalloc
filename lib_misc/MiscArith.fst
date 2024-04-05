module MiscArith

#push-options "--fuel 0 --ifuel 0"

open FStar.Mul

module FML = FStar.Math.Lemmas

let lemma_mod_add_inv (k: int) (n: pos)
  : Lemma
  (requires
    k % n == 0
  )
  (ensures
    (-k) % n == 0
  )
  =
  FML.div_exact_r k n;
  let i = k/n in
  assert (i * n == k);
  FML.lemma_mod_sub k n (2*i);
  ()

let lemma_mod_plus2 (a k: int) (n: pos)
  : Lemma
  (requires
    k % n == 0
  )
  (ensures
    (a + k) % n == a % n
  )
  =
  assert (k == k/n*n);
  let k' = k/n in
  FML.lemma_mod_plus a k' n

let lemma_mod_mul2 (a k: int) (n: pos)
  : Lemma
  (requires
    k % n == 0
  )
  (ensures
    (a * k) % n == 0
  )
  =
  FML.lemma_mod_mul_distr_r a k n

let lemma_mul_le (a b c c':nat)
  : Lemma
  (requires c <= c')
  (ensures a * b * c <= a * b * c')
  = ()

let lemma_div_lt (a:pos) (b c k:nat)
  : Lemma
  (requires k < a * b * c)
  (ensures k / a < b * c)
  = ()

#push-options "--fuel 1 --ifuel 1"

noextract
let rec decompose (n: pos)
  : v:(nat & nat){(snd v) % 2 = 1}
  = match n % 2 with
  | 0 -> let (k1, k2) = decompose (n/2) in (k1+1, k2)
  | 1 -> (0, n)

open FStar.Mul
let rec decompose_eq (n: pos)
  : Lemma
  (let (x,y) = decompose n in
  n = (pow2 x) * y)
  = match n % 2 with
  | 0 -> decompose_eq (n/2)
  | 1 -> ()

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50 --split_queries always"
let decompose_unicity_aux (i1 j1 i2 j2: nat)
  : Lemma
  (requires
    (pow2 i1) * j1 == (pow2 i2) * j2 /\
    j1 % 2 = 1 /\
    j2 % 2 = 1 /\
    j1 > 0 /\
    j2 > 0 /\
    i1 <= i2)
  (ensures
    i1 == i2
  )
  =
  let t = j2 * (pow2 (i2 - i1)) in
  calc (==) {
    j1;
    == { FML.cancel_mul_div j1 (pow2 i1) }
    j1 * (pow2 i1) / (pow2 i1);
    == { FML.swap_mul j1 (pow2 i1) }
    (pow2 i2) * j2 / (pow2 i1);
    == { FML.swap_mul (pow2 i2) j2 }
    j2 * (pow2 i2) / (pow2 i1);
    == { FML.pow2_plus (i2 - i1) i1 }
    j2 * ((pow2 (i2 - i1)) * (pow2 i1)) / (pow2 i1);
    == { FML.paren_mul_right j2 (pow2 (i2 - i1)) (pow2 i1) }
    t * (pow2 i1) / (pow2 i1);
    == { FML.cancel_mul_div t (pow2 i1) }
    t;
  };
  if (i2 > i1) then (
    let k = pow2 (i2 - i1) in
    assert (j1 == j2 * k);
    assert_norm (k % 2 = 0);
    lemma_mod_mul2 j2 k 2;
    assert ((k * j2) % 2 = 0);
    assert (j1 % 2 = 0);
    assert (j1 % 2 = 1)
  )
#pop-options

let decompose_unicity (n: pos) (i1 j1 i2 j2:nat)
  : Lemma
  (requires
    n = (pow2 i1) * j1 /\
    n = (pow2 i2) * j2 /\
    j1 % 2 = 1 /\
    j2 % 2 = 1 /\
    i1 >= 0 /\
    i2 >= 0 /\
    j1 > 0 /\
    j2 > 0
  )
  (ensures
    i1 = i2 /\ j1 = j2
  )
  (decreases n)
  =
  if (i1 = i2) then () else (
    assert ((pow2 i1) * j1 == (pow2 i2) * j2);
    if (i1 < i2)
    then decompose_unicity_aux i1 j1 i2 j2
    else decompose_unicity_aux i2 j2 i1 j1
  )

let mul_abcd_acbd (a b c d: nat)
  : Lemma
  ((a * b) * (c * d) == (a * c) * (b * d))
  = ()

let mul_odd_odd_is_odd (a b: nat)
  : Lemma
  (requires a % 2 = 1 /\ b % 2 = 1)
  (ensures (a * b) % 2 = 1)
  =
  FML.lemma_mod_mul_distr_l a b 2

let decompose_mul (n1 n2: pos)
  : Lemma
  (let i0, j0 = decompose (n1 * n2) in
  let i1, j1 = decompose n1 in
  let i2, j2 = decompose n2 in
  (i0 = i1 + i2) /\
  (j0 = j1 * j2))
  =
  let i0, j0 = decompose (n1 * n2) in
  decompose_eq (n1 * n2);
  let i1, j1 = decompose n1 in
  let i2, j2 = decompose n2 in
  calc (==) {
    n1 * n2;
    == { decompose_eq n1 }
    ((pow2 i1) * j1) * n2;
    == { decompose_eq n2 }
    ((pow2 i1) * j1) * ((pow2 i2) * j2);
    == { mul_abcd_acbd (pow2 i1) j1 (pow2 i2) j2 }
    ((pow2 i1) * (pow2 i2)) * (j1 * j2);
    == { FML.pow2_plus i1 i2 }
    (pow2 (i1 + i2)) * (j1 * j2);
  };
  assert (n1 * n2 = (pow2 (i1 + i2)) * (j1 * j2));
  mul_odd_odd_is_odd j1 j2;
  decompose_unicity (n1 * n2) i0 j0 (i1+i2) (j1*j2)

let decompose_pow2 (k: nat)
  : Lemma
  (decompose (pow2 k) = (k, 1))
  =
  let (x,y) = decompose (pow2 k) in
  decompose_eq (pow2 k);
  decompose_unicity (pow2 k) k 1 x y

let rec mod_thm (k: nat) (n: pos)
  : Lemma
  (requires
    n <= pow2 k /\
    (pow2 k) % n = 0
  )
  (ensures (
    let (x,y) = decompose n in
    y = 1
  ))
  = match (decompose n) with
  | (0, y) ->
      let z = pow2 k in
      FML.euclidean_division_definition z n;
      assert (z = z/n * n);
      (* LHS decomposition *)
      decompose_pow2 k;
      assert (decompose (pow2 k) = (k, 1));
      (* RHS decomposition *)
      let i1, j1 = decompose (z/n) in
      decompose_mul (z/n) n;
      assert (decompose (z/n * n) == (i1 + 0, j1 * y));
      (* eq *)
      assert (k = i1 + 0 /\ 1 = j1 * y)
  | (x, y) ->
      let a = pow2 (k-1) in
      let b = 2 in
      let c = n/2 in
      calc (==) {
        (pow2 k) % n;
        == { FML.pow2_plus (k-1) 1 }
        (a * b) % n;
        == { () }
        (a * b) % (b * c);
        == { FML.modulo_scale_lemma a b c }
        (a % c) * b;
      };
      mod_thm (k-1) (n/2)

let rec pow2_mod (k1 k2: nat)
  : Lemma
  (requires k1 <= k2)
  (ensures (pow2 k2) % (pow2 k1) == 0)
  (decreases k1)
  = match k1 with
  | 0 -> ()
  | _ ->
      FML.pow2_plus (k2 - 1) 1;
      FML.pow2_plus 1 (k1 - 1);
      FML.modulo_scale_lemma (pow2 (k2 - 1)) 2 (pow2 (k1 - 1));
      assert ((pow2 k2) % (pow2 k1) == ((pow2 (k2 - 1)) % (pow2 (k1 - 1))) * 2);
      pow2_mod (k1 - 1) (k2 - 1)

let pow2_is_increasing (x y: nat)
  : Lemma
  (requires pow2 x <= pow2 y)
  (ensures x <= y)
  =
  if x > y then
  FML.pow2_lt_compat x y

let alignment_lemma (v:nat) (n: nat) (x y: pos)
  : Lemma
  (requires
    v = pow2 n /\
    v % x == 0 /\
    v % y == 0 /\
    x <= v /\
    y <= v /\
    x <= y)
  (ensures
    y % x == 0
  )
  =
  let (i1, j1) = decompose x in
  let (i2, j2) = decompose y in
  mod_thm n x;
  mod_thm n y;
  assert (j1 == 1 /\ j2 == 1);
  decompose_eq x;
  decompose_eq y;
  pow2_is_increasing i1 i2;
  assert (i1 <= i2);
  pow2_mod i1 i2
