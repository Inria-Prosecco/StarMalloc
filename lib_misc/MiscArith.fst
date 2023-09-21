module MiscArith

#push-options "--fuel 0 --ifuel 0"

open FStar.Mul

//TODO: to be removed
//let mod_arith_lemma
//  (n: nat) (k1 k2: pos)
//  : Lemma
//  (requires
//    k1 % k2 == 0 /\
//    k2 <= k1
//  )
//  (ensures
//    (n % k1) % k2 == n % k2
//  )
//  =
//  calc (==) {
//    ((n / k1) * k1) % k2;
//    == { Math.Lemmas.lemma_mod_mul_distr_r (n / k1) k1 k2 }
//    ((n / k1) * (k1 % k2)) % k2;
//    == { () }
//    0;
//  };
//  assert (((n / k1) * k1) % k2 == 0);
//  calc (==) {
//    (n % k1) % k2;
//    == { FStar.Math.Lemmas.euclidean_division_definition n k1 }
//    (n - (n / k1) * k1) % k2;
//    == { FStar.Math.Lemmas.lemma_mod_sub_distr n ((n / k1) * k1) k2 }
//    (n - ((n / k1) * k1) % k2) % k2;
//    == { () }
//    n % k2;
//  }

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
  Math.Lemmas.lemma_mod_plus a k' n

let lemma_mod_mul2 (a k: int) (n: pos)
  : Lemma
  (requires
    k % n == 0
  )
  (ensures
    (a * k) % n == 0
  )
  =
  Math.Lemmas.lemma_mod_mul_distr_r a k n

let lemma_mul_le (a b c c':nat) : Lemma (requires c <= c') (ensures a * b * c <= a * b * c')
  = ()
