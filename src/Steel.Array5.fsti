module Steel.Array5
open FStar.Ghost
open Steel.FractionalPermission
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U32 = FStar.UInt32
module Mem = Steel.Memory

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

//val array (t: Type0) : Type0
let array (t: Type0) = FStar.Seq.seq t

//val length (#t: Type0) (arr: array t) : GTot nat
let length (#t: Type0) (arr: array t) : GTot nat
  = hide (Seq.length arr)

val is_array (#t: Type0) (arr: array t) : Mem.slprop u#1

val array_sel (#t: Type0) (arr: array t)
  //: selector (contents t (length arr)) (is_array arr)
  : selector (Seq.seq t) (is_array arr)

[@@ __steel_reduce__]
let varray' (#t: Type0) (arr: array t) : vprop' = {
  hp = is_array arr;
  //t = contents t (length arr);
  t = Seq.seq t;
  sel = array_sel arr;
}

[@@ __steel_reduce__]
unfold
let varray (#t: Type0) (arr: array t) : vprop
  = VUnit (varray' arr)

[@@ __steel_reduce__]
let asel (#t: Type0) (#p: vprop) (arr: array t)
  (h: rmem p{FStar.Tactics.with_tactic selector_tactic
    (can_be_split p (varray arr) /\ True)
  })
  //: GTot (contents t (length arr))
  : GTot (Seq.seq t)
  //: GTot (x:(Seq.seq t){x == arr})
  = h (varray arr)

val adjacent (#t: Type0) (arr1 arr2: array t) : prop

val get_prev (#t: Type0) (arr: array t) : option (array t)
val get_succ (#t: Type0) (arr: array t) : option (array t)
val get_root (#t: Type0) (arr: array t) : array t
val get_perm (#t: Type0) (arr: array t) : bool

//val intro (#t: Type0) : S

val destruct (#t: Type0) (arr: array t) : Steel unit
  (varray arr) (fun _ -> emp)
  (requires fun _ -> get_perm arr)
  (ensures fun _ _ _ -> True)

//let isolated (#t: Type0) (arr: array t)
//  = get_prev arr == None /\ get_succ arr == None

let _fst (#t1 #t2 #t3 #t4: Type0) (data: t1 & t2 & t3 & t4) : t1 =
  let a, b, c, d = data in a
let _snd (#t1 #t2 #t3 #t4: Type0) (data: t1 & t2 & t3 & t4) : t2 =
  let a, b, c, d = data in b
let _thd (#t1 #t2 #t3 #t4: Type0) (data: t1 & t2 & t3 & t4) : t3 =
  let a, b, c, d = data in c
let _fth (#t1 #t2 #t3 #t4: Type0) (data: t1 & t2 & t3 & t4) : t4 =
  let a, b, c, d = data in d

val split_root (#t: Type0)
  (arr: array t) (ptr: ref (array t)) (size: U32.t)
  : Steel (array t & array t & ref (array t) & ref (array t))
  (varray arr `star` vptr ptr)
  (fun r ->
  varray (_fst r) `star`
  varray (_snd r) `star`
  vptr (_thd r) `star`
  vptr (_fth r)
  )
  (requires fun h0 ->
    U32.v size < length arr /\
    get_prev arr == None /\
    get_succ arr == None /\
    sel ptr h0 == arr
  )
  (ensures fun h0 r h1 ->
    U32.v size < length arr /\
    adjacent (_fst r) (_snd r) /\
    get_prev (_fst r) == None /\
    get_succ (_snd r) == None /\
    sel (_thd r) h1 == _fst r /\
    sel (_fth r) h1 == _snd r /\
    length (_fst r) = U32.v size /\
    length (_fst r) + length (_snd r) == length arr /\
    Seq.append (_fst r) (_snd r) == arr /\
      //(reveal (asel (_fst r) h1))
      //(reveal (asel (_snd r) h1))
    //== asel arr h0 /\
    //reveal (asel (_fst r) h1)
    _fst r
    //== fst (Seq.split (asel arr h0) (U32.v size)) /\
    == fst (Seq.split arr (U32.v size)) /\
    //reveal (asel (_snd r) h1)
    _snd r
    //== snd (Seq.split (asel arr h0) (U32.v size)) /\
    == snd (Seq.split arr (U32.v size)) /\
    //length (fst r) == U32.v size /\
    //length (fst r) + length (snd r) == length arr /\
    True
  )

(*)
val split (#t: Type0) (#opened:inames)
  (arr prev succ: array t)
  : SteelGhost (array t & array t)
  opened
  (varray prev `star`
  varray arr `star`
  varray succ)
  (fun r ->
  varray prev `star`
  varray (fst r) `star`
  varray (snd r) `star`
  varray succ
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
      (asel (fst r) h1)
      (asel (snd r) h1)
    == asel arr h0
  )

val merge (#t: Type0) (#opened:inames)
  (arr1 arr2 prev succ: array t)
  : SteelGhost (array t)
  opened
  (varray prev `star`
  varray arr1 `star`
  varray arr2 `star`
  varray succ
  )
  (fun arr ->
  varray prev `star`
  varray arr `star`
  varray succ)
  (requires fun _ ->
    adjacent prev arr1 /\
    adjacent arr1 arr2 /\
    adjacent arr2 succ
  )
  (ensures fun h0 arr h1 ->
    adjacent prev arr /\
    adjacent arr succ /\
    Seq.append
      (asel arr1 h0)
      (asel arr2 h0)
    === asel arr h1
  )

// add merge_to_root
