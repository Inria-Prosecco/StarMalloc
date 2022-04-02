module Steel.Array4
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

//val intro (#t: Type0) : S

val destruct (#t: Type0) (arr: array t) : SteelT unit
  (varray arr true) (fun _ -> emp)

val get_prev (#t: Type0) (arr: array t) : option (array t)
val get_succ (#t: Type0) (arr: array t) : option (array t)
val get_root (#t: Type0) (arr: array t) : array t
//val get_perm (#t: Type0) (arr: array t) : perm

val split_root (#t: Type0) (#opened:inames)
  (arr: array t)
  (prev next: array t)
  : SteelGhost (array t & array t)
  opened
  (varray arr true)
  (fun (arr1, arr2) ->
  varray arr1 false `star`
  varray arr2 false
  )
  (requires fun _ ->
    get_prev arr == None /\
    get_succ arr == None
  )
  (ensures fun _ (arr1, arr2) _ ->
    adjacent arr1 arr2 /\
    get_prev arr1 == None /\
    get_succ arr2 == None
  )

val split (#t: Type0) (#opened:inames)
  (arr: array t)
  (prev succ: array t)
  (p1 p2 p3: perm)
  : SteelGhost (array t & array t)
  opened
  (varray prev p1 `star`
  varray arr p2 `star`
  varray succ p3)
  (fun r ->
  varray prev p1 `star`
  varray (fst r) false `star`
  varray (snd r) false `star`
  varray succ p3
  )
  (requires fun _ ->
    adjacent prev arr /\
    adjacent arr succ
  )
  (ensures fun h0 r h1 ->
    // there could be a wrapper to express
    // in a more concise manner the following
    // adjacence prop
    adjacent prev (fst r) /\
    adjacent (fst r) (snd r) /\
    adjacent (snd r) succ /\

    Seq.append
      (asel (fst r) false h1)
      (asel (snd r) false h1)
    == asel arr p2 h0
  )

val merge (#t: Type0) (#opened:inames)
  (arr1 arr2 prev succ: array t)
  (p1 p3: perm)
  : SteelGhost (array t)
  opened
  (varray prev p1 `star`
  varray arr1 false `star`
  varray arr2 false `star`
  varray succ p3
  )
  (fun arr ->
  varray prev p1 `star`
  varray arr false `star`
  varray succ p3)
  (requires fun _ ->
    adjacent prev arr1 /\
    adjacent arr1 arr2 /\
    adjacent arr2 succ
  )
  (ensures fun h0 arr h1 ->
    adjacent prev arr /\
    adjacent arr succ /\
    Seq.append
      (asel arr1 false h0)
      (asel arr2 false h0)
    === asel arr false h1
  )
