module ROArray

open Steel.Effect.Common
open Steel.Effect.Atomic

/// We need to name all lambdas to ensure that the SMT will be able to
/// prove equalities for h_exists
let ro_array_contents (#a:Type) (s1 s2:Seq.seq a) : prop = s1 == s2

let ro_array_exists (#a:Type) (r:array a) (s:Seq.seq a) (p: perm) : vprop
  = varrayp r p `vrefine` (ro_array_contents s)

let ro_array_vprop (#a:Type) (r:array a) (s:Seq.seq a) : vprop =
  h_exists (ro_array_exists r s)

let ro_array r s = inv (ro_array_vprop r s)

let create_ro_array #a #p r s =
  intro_vrefine (varrayp r p) (ro_array_contents s);
  intro_exists p (ro_array_exists r s);
  new_invariant (ro_array_vprop r s)

/// Creates a readable permission on the array if we have a ro_array token in the context
inline_for_extraction noextract
val intro_ro_array (#a:Type)
  (r:array a)
  (s:Ghost.erased (Seq.lseq a (length r)))
  (i: ro_array r s)
  : SteelAtomic (Ghost.erased perm) Set.empty
                emp
                (fun p -> varrayp r p)
                (requires fun _ -> True)
                (ensures fun _ p h1 -> aselp r p h1 == Ghost.reveal s)

let intro_ro_array #a r s i =
  let body (_:unit)
    : SteelGhostT perm
                  (add_inv Set.empty i)
                  (ro_array_vprop r s `star` emp)
                  (fun p -> ro_array_vprop r s `star` (varrayp r p `vrefine` ro_array_contents s))
  =
    let p = witness_exists () in
    elim_vrefine (varrayp r p) (ro_array_contents s);
    share r p (half_perm p) (half_perm p);
    intro_vrefine (varrayp r (half_perm p)) (ro_array_contents s);
    intro_vrefine (varrayp r (half_perm p)) (ro_array_contents s);
    intro_exists (half_perm p) (ro_array_exists r s);
    (half_perm p)
  in
  let p = with_invariant_g i body in
  elim_vrefine (varrayp r p) (ro_array_contents s);
  return p

let index #a #r #s ro i =
  let p = intro_ro_array r s ro in
  let v = index r i in
  drop (varrayp r p);
  return v
