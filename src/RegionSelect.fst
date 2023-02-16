module RegionSelect

open Steel.FractionalPermission
open Steel.Memory
open Steel.Effect.Common
open Steel.Effect.Atomic

let ro_array_vprop (#a:Type) (r:array a) : vprop = h_exists (varrayp r)

let ro_array (#a:Type) (r:array a) = inv (ro_array_vprop r)

/// Creates a readable permission on the array if we have a ro_array token in the context
inline_for_extraction noextract
val intro_ro_array (#a:Type)
  (r:array a)
  (i: ro_array r)
  : SteelAtomicT (Ghost.erased perm) Set.empty
                emp
                (fun p -> varrayp r p)

let intro_ro_array #a r i =
  let body (_:unit)
    : SteelGhostT perm
                  (add_inv Set.empty i)
                  (ro_array_vprop r `star` emp)
                  (fun p -> ro_array_vprop r `star` varrayp r p)
  =
    let p = witness_exists () in
    share r p (half_perm p) (half_perm p);
    intro_exists (half_perm p) (varrayp r);
    (half_perm p)
  in
  with_invariant_g i body

let create_ro_array #a #p r =
  intro_exists p (varrayp r);
  new_invariant (ro_array_vprop r)

let within_bounds_intro arr1 p arr2 ro1 ro2 =
  let p1 = intro_ro_array arr1 ro1 in
  let p2 = intro_ro_array arr2 ro2 in
  let b = within_bounds_intro arr1 p arr2 in
  drop (varrayp arr1 _);
  drop (varrayp arr2 _);
  return b
