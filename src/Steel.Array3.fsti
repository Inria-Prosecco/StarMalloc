module Steel.Array3
open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open FStar.Ghost
open Steel.FractionalPermission

module U32 = FStar.UInt32

#set-options "--ide_id_info_off"

(*
Manipulation d'arrays de manière pratique.
On veut pouvoir split/merge de manière correcte.
- pour split :
addr -> n -> addr, ptr_add addr n
- pour merge :
addr -> addr -> addr
En préservant les contenus correspondant,
en respectant les propriétés d'adjacence,
sans malloc/upd ou autre.

Le tout de manière correcte, sans fuite de mémoire.
Plusieurs remarques.

1) Un petit exemple.
On part de arr1 de longueur 16.
On split arr1 à 8, on obtient arr2 arr3 : arr 8.
free arr2 doit être interdit (standard C).
On a donc besoin de garder l'information sur l'arborescence.

2) Cette information sur l'arborescence doit être dans le
contexte de logique de séparation,
car elle ne doit pas être effacée ou altérée de manière incorrecte,
par exemple lors du passage d'une fonction à une autre.
Explicitement ou implicitement ?
Autre méthode ?
Sous la forme de permissions plus fines ?
Rust ?
Localement ? ça a l'air pas mal
ajouter adjacent

*)

(* permission de free ou pas *)
let perm: Type = bool

// Contents of an array of type t
let contents (t: Type0) (n:nat) = FStar.Seq.lseq t n

val array (t: Type0) : Type0

val length (#t: Type0) (arr: array t) : GTot nat

val is_array (#t: Type0) (arr: array t) (p:perm): slprop u#1

val array_sel (#t: Type0) (arr: array t) (p:perm)
  : selector (contents t (length arr)) (is_array arr p)

[@@ __steel_reduce__]
let varray' (#t: Type0) (arr: array t) (p:perm) : vprop' = {
  hp = is_array arr p;
  t = contents t (length arr);
  sel = array_sel arr p;
}

[@@ __steel_reduce__]
unfold
let varray (#t: Type0) (arr: array t) (p:perm) : vprop
  = VUnit (varray' arr p)

[@@ __steel_reduce__]
let asel (#t: Type0) (#p: vprop) (arr: array t) (perm:perm)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic
    (can_be_split p (varray arr perm) /\ True)
  })
  : GTot (contents t (length arr))
  = h (varray arr perm)

val adjacent (#t: Type0) (arr1 arr2: array t) : prop

val destruct (#t: Type0) (arr: array t) : SteelT unit
  (varray arr true) (fun _ -> emp)

val varray_m (#t: Type) (arr: array t)
  (p: perm)
  (prev next: option (array t))
  (root: array t)
  : vprop

[@@ __steel_reduce__]
val amsel (#t: Type0) (#p: vprop) (arr: array t) (perm:perm)
  (prev next: option (array t)) (root: array t)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic
    (can_be_split p (varray_m arr perm prev next root) /\ True)
  })
  : GTot (contents t (length arr))
  //= h (varray_m arr perm prev next root)

val intro_varray_m_root (#t: Type0) (#opened:inames) (arr: array t)
  : SteelGhostT (array t)
  opened
  (varray arr true)
  (fun _ -> varray_m arr true None None arr)

val elim_varray_m_root (#t: Type0) (#opened:inames) (arr: array t)
  : SteelGhostT (array t)
  opened
  (varray_m arr true None None arr)
  (fun _ -> varray arr true)

//val varray_m_get_prev (#t: Type) (#opened:inames)


val intro_varray_m_not_root (#t: Type0) (#opened:inames)
  (arr: array t)
  (p1 p2 p3: perm)
  (prev0 next1: option (array t))
  (prev next root: array t)
  : SteelGhostT (array t)
  opened
  (varray_m prev p1 prev0 (Some arr) root `star`
  varray arr p2 `star`
  varray_m next p3 (Some arr) next1 root)
  (fun _ ->
  varray_m prev p1 prev0 (Some arr) root `star`
  varray_m arr p2 (Some prev) (Some next) root `star`
  varray_m next p3 (Some arr) next1 root)

val elim_varray_m_not_root (#t: Type0) (#opened:inames)
  (arr: array t)
  (p1 p2 p3: perm)
  (prev0 next1: option (array t))
  (prev next root: array t)
  : SteelGhostT (array t)
  opened
  (varray_m prev p1 prev0 (Some arr) root `star`
  varray_m arr p2 (Some prev) (Some next) root `star`
  varray_m next p3 (Some arr) next1 root)
  (fun _ ->
  varray_m prev p1 prev0 (Some arr) root `star`
  varray arr p2 `star`
  varray_m next p3 (Some arr) next1 root)

val split_root (#t: Type0) (#opened:inames)
  (arr: array t)
  (n: nat)
  (prev next: array t)
  : SteelGhostT (array t & array t)
  opened
  (varray_m arr true None None arr)
  (fun (arr1, arr2) ->
  varray_m arr1 false None (Some arr2) arr `star`
  varray_m arr2 false (Some arr1) None arr
  )

val split (#t: Type0) (#opened:inames)
  (arr: array t)
  (p1 p2 p3: perm)
  (prev0 next1: option (array t))
  (prev next root1 root2 root3: array t)
  : SteelGhost (array t & array t)
  opened
  (varray_m prev p1 prev0 (Some arr) root1 `star`
  varray_m arr p2 (Some prev) (Some next) root2 `star`
  varray_m next p3 (Some arr) next1 root3)
  (fun r ->
  varray_m prev p1 prev0 (Some (fst r)) root1 `star`
  varray_m (fst r) false (Some prev) (Some (snd r)) root2 `star`
  varray_m (snd r) false (Some (fst r)) (Some next) root2 `star`
  varray_m next p3 (Some (snd r)) next1 root3
  )
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    Seq.append
      (amsel (fst r) false (Some prev) (Some (snd r)) root2 h1)
      (amsel (snd r) false (Some (fst r)) (Some next) root2 h1)
    == amsel arr p2 (Some prev) (Some next) root2 h0
  )

val merge (#t: Type0) (#opened:inames)
  (arr1 arr2 arr: array t)
  (p1 p2 p3: perm)
  (prev0 next1: option (array t))
  (prev next root1 root2 root3: array t)
  : SteelGhost (array t)
  opened
  (varray_m prev p1 prev0 (Some arr1) root1 `star`
  varray_m arr1 false (Some prev) (Some arr2) root2 `star`
  varray_m arr2 false (Some arr1) (Some next) root2 `star`
  varray_m next p3 (Some arr2) next1 root3)
  (fun arr -> varray_m prev p1 prev0 (Some arr) root1 `star`
  varray_m arr p2 (Some prev) (Some next) root2 `star`
  varray_m next p3 (Some arr) next1 root3)
  (requires fun _ -> True)
  (ensures fun h0 arr h1 ->
    Seq.append
      (amsel arr1 false (Some prev) (Some arr2) root2 h0)
      (amsel arr2 false (Some arr1) (Some next) root2 h0)
    == amsel arr p2 (Some prev) (Some next) root2 h1
  )
