module Selectors.LList

open FStar.Ghost
open Steel.FractionalPermission
module Mem = Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
//open Impl.Core

//#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  next: ref (cell a);
  data: a;
}
//#pop-options

let get_next #a (c:cell a) : t a = c.next
let get_data #a (c:cell a) : a = c.data
let mk_cell #a (n: t a) (d:a) = {
  next = n;
  data = d
}

let null_t #a = null
let is_null_t #a ptr = is_null ptr

let rec llist_sl' (#a:Type) (p: a -> vprop) (ptr: t a) (l: list (cell a))
  : Tot slprop (decreases l)
  =
  match l with
  | [] -> Mem.pure (ptr == null_t)
  | hd :: tl ->
    pts_to_sl ptr full_perm hd `Mem.star`
    llist_sl' p (get_next hd) tl `Mem.star`
    hp_of (p (get_data hd))

let llist_sl p ptr = Mem.h_exists (llist_sl' p ptr)

// BETA
let ind_llist_sl' (#a: Type0) (r: ref (t a)) (p: t a) : slprop u#1
  =
  llist_sl #a (fun _ -> to_vprop (pts_to_sl r full_perm p)) p
let ind_llist_sl (#a: Type0) (r: ref (t a))
  = Mem.h_exists (ind_llist_sl' r)

let normal_llist_sl (#a: Type0) (ptr : t a) : slprop u#1
  = llist_sl #a (fun _ -> emp) ptr

let tree_llist_sl (#a: Type0) (ptr : t (Impl.Core.t a)) : slprop u#1
  = llist_sl #(Impl.Core.t a)
    (fun elem -> to_vprop (Impl.Core.tree_sl #a elem)) ptr

let llist_llist_sl (#a: Type0) (ptr : t (t a)) : slprop u#1
  = llist_sl #(t a)
    (fun elem -> to_vprop (llist_sl #a (fun _ -> emp) elem)) ptr

let rec llist_view (#a:Type) (l:list (cell a)) : list a =
  match l with
  | [] -> []
  | hd::tl -> get_data hd :: llist_view tl

val llist_sel_cell' (#a:Type0) (p: a -> vprop) (ptr:t a) : selector' (list (cell a)) (llist_sl p ptr)

let llist_sel_cell' #a p ptr =
  fun h -> id_elim_exists (llist_sl' p ptr) h

let llist_sl'_witinv (#a:Type) (p: a -> vprop) (ptr:t a) :
  Lemma (is_witness_invariant (llist_sl' p ptr))
  = let rec aux (ptr:t a) (x y:list (cell a)) (m:mem) : Lemma
        (requires
          interp (llist_sl' p ptr x) m /\
          interp (llist_sl' p ptr y) m)
        (ensures x == y)
        (decreases x)
    =
    match x with
    | [] -> begin match y with
      | [] -> ()
      | hd::tl ->
        Mem.pure_interp (ptr == null_t) m;
        //let p1 = pts_to_sl ptr full_perm hd in
        //let p2 = llist_sl' p (get_next hd) tl in
        //let p3 = hp_of (p (get_data hd)) in
        //Mem.affine_star (p1 `Mem.star` p2) p3 m;
        //Mem.affine_star p1 p2 m;
        pts_to_not_null ptr full_perm hd m
    end
    | hd1::tl1 -> begin match y with
      | [] ->
        Mem.pure_interp (ptr == null_t) m;
        //let p1 = pts_to_sl ptr full_perm hd1 in
        //let p2 = llist_sl' p (get_next hd1) tl1 in
        //let p3 = hp_of (p (get_data hd1)) in
        //Mem.affine_star (p1 `Mem.star` p2) p3 m;
        //Mem.affine_star p1 p2 m;
        pts_to_not_null ptr full_perm hd1 m
     | hd2::tl2 ->
        pts_to_witinv ptr full_perm;
        aux (get_next hd1) tl1 tl2 m
    end
    in Classical.forall_intro_3 (Classical.move_requires_3 (aux ptr))

let llist_sel_depends_only_on (#a:Type0) (p : a -> vprop) (ptr:t a)
  (m0:Mem.hmem (llist_sl p ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (llist_sel_cell' p ptr m0 == llist_sel_cell' p ptr (Mem.join m0 m1))
  = let m':Mem.hmem (llist_sl p ptr) = Mem.join m0 m1 in
    let l1 = Ghost.reveal (id_elim_exists (llist_sl' p ptr) m0) in
    let l2 = Ghost.reveal (id_elim_exists (llist_sl' p ptr) m') in

    llist_sl'_witinv p ptr;
    Mem.elim_wi (llist_sl' p ptr) l1 l2 m'

let llist_sel_depends_only_on_core (#a:Type0) (p : a -> vprop) (ptr:t a)
  (m0:Mem.hmem (llist_sl p ptr))
  : Lemma (llist_sel_cell' p ptr m0 == llist_sel_cell' p ptr (core_mem m0))
  = let l1 = Ghost.reveal (id_elim_exists (llist_sl' p ptr) m0) in
    let l2 = Ghost.reveal (id_elim_exists (llist_sl' p ptr) (core_mem m0)) in
    llist_sl'_witinv p ptr;
    Mem.elim_wi (llist_sl' p ptr) l1 l2 (core_mem m0)

val llist_sel_cell (#a:Type0) (p : a -> vprop) (r:t a) : selector (list (cell a)) (llist_sl p r)

let llist_sel_cell #a p ptr =
  Classical.forall_intro_2 (llist_sel_depends_only_on p ptr);
  Classical.forall_intro (llist_sel_depends_only_on_core p ptr);
  llist_sel_cell' p ptr

let llist_sel #a p ptr =
  fun h -> llist_view (llist_sel_cell p ptr h)

let llist_sel_interp (#a:Type0) (p : a -> vprop) (ptr:t a) (l:list (cell a)) (m:mem) : Lemma
  (requires interp (llist_sl' p ptr l) m)
  (ensures interp (llist_sl p ptr) m /\ llist_sel_cell' p ptr m == l)
  = intro_h_exists l (llist_sl' p ptr) m;
    llist_sl'_witinv p ptr

let intro_nil_lemma (a:Type0) (p : a -> vprop) (m:mem) : Lemma
    (requires interp (hp_of emp) m)
    (ensures interp (llist_sl p (null_t #a)) m /\ llist_sel p (null_t #a) m == [])
    = let ptr:t a = null_t in
      pure_interp (ptr == null_t) m;
      let open FStar.Tactics in
      assert (llist_sl' p ptr [] == Mem.pure (ptr == null_t)) by (norm [delta; zeta; iota]);
      llist_sel_interp p ptr [] m

let intro_llist_nil a p =
    change_slprop_2 emp (llist p (null_t #a)) ([] <: list a) (intro_nil_lemma a p)

let elim_nil_lemma (#a:Type0) (p : a -> vprop) (ptr:t a) (m:mem) : Lemma
    (requires interp (llist_sl p ptr) m /\ ptr == null_t)
    (ensures interp (llist_sl p ptr) m /\ llist_sel p ptr m == [])
    = let l' = id_elim_exists (llist_sl' p ptr) m in
      pure_interp (ptr == null_t) m;
      llist_sel_interp p ptr [] m

let elim_llist_nil #a p ptr =
  change_slprop_rel (llist p ptr) (llist p ptr)
    (fun x y -> x == y /\ y == [])
    (fun m -> elim_nil_lemma p ptr m)

//#set-options "--z3rlimit 20"

let lemma_cons_not_null (#a:Type) (p : a -> vprop) (ptr:t a) (l:list a) (m:mem) : Lemma
  (requires interp (llist_sl p ptr) m /\ llist_sel p ptr m == l /\ Cons? l)
  (ensures ptr =!= null_t)
  = let l' = id_elim_exists (llist_sl' p ptr) m in
    assert (interp (llist_sl' p ptr l') m);
    llist_sel_interp p ptr l' m;
    match reveal l' with
    | hd::tl -> pts_to_not_null ptr full_perm hd m

let cons_is_not_null #a p ptr =
  let h = get () in
  let l = hide (v_llist p ptr h) in
  extract_info (llist p ptr) l (ptr =!= null_t) (lemma_cons_not_null p ptr l)

let intro_cons_lemma_aux (#a:Type0) (p : a -> vprop) (ptr1 ptr2:t a)
  (x: cell a) (l:list (cell a)) (m:mem) : Lemma
  (requires
    interp (
      pts_to_sl ptr1 full_perm x `Mem.star`
      llist_sl' p ptr2 l `Mem.star`
      hp_of (p (get_data x))) m /\
    get_next x == ptr2)
  (ensures (let new_l = x::l in
    interp (llist_sl' p ptr1 new_l) m))
  =
  ()

let intro_cons_lemma (#a:Type0) (p : a -> vprop) (ptr1 ptr2:t a)
  (x: cell a) (l:list a) (m:mem) : Lemma
  (requires
    interp (
      ptr ptr1 `Mem.star`
      llist_sl p ptr2 `Mem.star`
      hp_of (p (get_data x))
    ) m /\
    get_next x == ptr2 /\
    sel_of (vptr ptr1) m == x /\
    sel_of (llist p ptr2) m == l)
  (ensures interp (llist_sl p ptr1) m /\ llist_sel p ptr1 m == get_data x :: l)
  =
  let l' = id_elim_exists (llist_sl' p ptr2) m in
  //let p1 = pts_to_sl ptr full_perm hd in
  let p1 = ptr ptr1 in
  //let p2 = llist_sl' p (get_next hd) tl in
  let p2 = llist_sl p ptr2 in
  //let p3 = hp_of (p (get_data hd)) in
  let p3 = hp_of (p (get_data x)) in
  let m12, m3 = id_elim_star (p1 `Mem.star` p2) p3 m in
  let m1, m2 = id_elim_star p1 p2  m12 in
  // #1
  ptr_sel_interp ptr1 m1;
  // #2
  let l2 = id_elim_exists (llist_sl' p ptr2) m in
  join_commutative m1 m2;
  assert (interp (llist_sl' p ptr2 l2) m);
  llist_sl'_witinv p ptr2;
  assert (l2 == l');
  assert (interp (llist_sl' p ptr2 l') m2);
  // #3

  intro_star
    (pts_to_sl ptr1 full_perm x)
    (llist_sl' p ptr2 l')
    m1 m2;
  intro_star
    (pts_to_sl ptr1 full_perm x `Mem.star`
    llist_sl' p ptr2 l')
    (hp_of (p (get_data x)))
    m12 m3;

  intro_cons_lemma_aux p ptr1 ptr2 x l' m;
  intro_h_exists (x::l') (llist_sl' p ptr1) m;
  llist_sel_interp p ptr1 (x::l') m;
  ()


//val intro_llist_cons (#a:Type0) (p : a -> vprop)
//  (ptr1 ptr2:t a)
//  //(x: a)
//  //(y: t_of (p (get_data x)))
//  : Steel unit
//  (vptr ptr1 `star`
//  llist p ptr2)
//  //`star` p x)
//  (fun _ -> llist p ptr1)
//  (requires fun h ->
//    get_next (sel ptr1 h) == ptr2
//    ///\x == get_data (sel ptr1 h)
//    ///\
//    //y == sel (sel_of (p (get_data x))) h
//  )
//  (ensures fun h0 _ h1 ->
//  v_llist p ptr1 h1 == (get_data (sel ptr1 h0)) :: v_llist p ptr2 h0)


//val intro_llist_cons (#a:Type0) (p : a -> vprop) (ptr1 ptr2:t a)
//  : Steel unit (vptr ptr1 `star` llist p ptr2)
//                  (fun _ -> llist p ptr1)
//                  (requires fun h -> get_next (sel ptr1 h) == ptr2)
//                  (ensures fun h0 _ h1 -> v_llist p ptr1 h1 == (get_data (sel ptr1 h0)) :: v_llist p ptr2 h0)

let intro_llist_cons p ptr1 ptr2 x =
  let h = get () in
  let x' = hide (sel ptr1 h) in
  assert (get_data (reveal x') == x);
  let l = hide (v_llist p ptr2 h) in
  //let m = rmem (p (get_data x)) in
  //let vp = p (get_data x) in

  change_slprop_rel
  (p x)
  (p (get_data x'))
  (fun x y -> x == y) (fun _ -> ());

  //let the_p =
  let m = gget
    (vptr ptr1 `star`
    llist p ptr2 `star`
    p (get_data x')) in
  //slassert the_p;
  //let m =
  //let m = gget vp in

  //let z = gget vp in

  //let sp = sel_of vp in
  //let hp = rmem vp in
  //let z = (sel_of vp) (hmem vp) in
  //let z = fun m -> sel_of vp m in


  //let z = hide (sel_of (p (get_data x)) m) in
  //let z : Ghost.erased (t_of)
  //reveal_star (vptr ptr1) (llist p ptr2);
  change_slprop
    (vptr ptr1 `star`
    llist p ptr2 `star`
    p (get_data x'))
    (llist p ptr1)
    m
    //((reveal x, reveal l),
    //  ())
      //fun m -> sel_of vp m)

      //fun  -> ())
      //get_data x)
      //(reveal h) (p (get_data x)))
      //sel_of (p (get_data x)))
      //z)
      //normal (sel_of (p (get_data x))))
      //reveal (get_data x))
    (get_data x' :: l)
  (fun m -> intro_cons_lemma p ptr1 ptr2 x' l m)

//val intro_llist_cons2 (#a:Type0) (p : a -> vprop)
//  (ptr1 ptr2:t a)
//  //(y: t_of (p (get_data x)))
//  : Steel unit
//  (let h = get () in
//  vptr ptr1 `star`
//  llist p ptr2 `star`
//  p (sel ptr1 h))
//  (fun _ -> llist p ptr1)
//  (requires fun h ->
//    get_next (sel ptr1 h) == ptr2
//    //x == sel ptr1 h
//    ///\
//    //y == sel (sel_of (p (get_data x))) h
//  )
//  (ensures fun h0 _ h1 ->
//  v_llist p ptr1 h1 == (get_data (sel ptr1 h0)) :: v_llist p ptr2 h0)




let reveal_non_empty_lemma (#a:Type) (p : a -> vprop) (ptr:t a) (l:list (cell a)) (m:mem) : Lemma
    (requires interp (llist_sl p  ptr) m /\ llist_sel_cell p ptr m == l /\ ptr =!= null_t)
    (ensures Cons? l)
= let l' = id_elim_exists (llist_sl' p ptr) m in
  llist_sel_interp p  ptr l' m;
  pure_interp (ptr == null_t) m

let is_cons (#a:Type) (l:list a) : prop = match l with
  | [] -> False
  | _ -> True

[@@__steel_reduce__]
let llist_cell' #a p r : vprop' =
  {hp = llist_sl p r;
   t = list (cell a);
   sel = llist_sel_cell p r}
unfold
let llist_cell (#a:Type0) p (r:t a) = VUnit (llist_cell' p r)

[@@ __steel_reduce__]
let v_cell (#a:Type0) (#p2:vprop) (p : a -> vprop) (r:t a)
  (h:rmem p2{FStar.Tactics.with_tactic selector_tactic (can_be_split p2 (llist_cell p r) /\ True)}) : GTot (list (cell a))
  = h (llist_cell p r)

val reveal_non_empty_cell (#a:Type0) (p : a -> vprop) (ptr:t a)
  : Steel unit (llist_cell p ptr) (fun _ -> llist_cell p ptr)
             (requires fun _ -> ptr =!= null_t)
             (ensures fun h0 _ h1 -> v_cell p ptr h0 == v_cell p ptr h1 /\ Cons? (v_cell p ptr h0))

let reveal_non_empty_cell #a p ptr =
  let h = get () in
  let l = hide (v_cell p ptr h) in
  extract_info (llist_cell p ptr) l (is_cons l) (reveal_non_empty_lemma p ptr l)

let tail_cell_lemma (#a:Type0) (p : a -> vprop) (r:t a) (l:list (cell a)) (m:mem) : Lemma
  (requires Cons? l /\ interp (llist_sl p r) m /\ llist_sel_cell p r m == l)
  (ensures (let x = L.hd l in
    interp (
      ptr r `Mem.star`
      llist_sl p (get_next x) `Mem.star`
      hp_of (p (get_data x))
    ) m /\
    sel_of (vptr r) m == x /\
    //sel_of (llist_cell p (get_next x)) m == L.tl l))
    sel_of (p (get_data x)) m == sel_of (p (get_data x)) m /\
    llist_sel_cell p (get_next x) m == L.tl l))
  =
  let x = L.hd l in
  let tl = L.tl l in
  llist_sel_interp p r l m;

  let p1 = pts_to_sl r full_perm x in
  let p2 = llist_sl' p (get_next x) tl in
  let p3 = hp_of (p (get_data x)) in
  let sl = p1 `Mem.star` p2 `Mem.star` p3 in
  assert (interp sl m);

  let m12, m3 = id_elim_star
    (p1 `Mem.star` p2) p3 m in
  assert (join m12 m3 == m);
  let m1, m2 = id_elim_star
    p1 p2 m12 in
  assert (reveal m12 == join m1 m2);

  // #1
  intro_ptr_interp r (hide x) m1;
  ptr_sel_interp r m1;
  pts_to_witinv r full_perm;
  // #2
  llist_sel_interp p (get_next x) tl m2;
  llist_sl'_witinv p (get_next x);
  intro_star
    (ptr r)
    (llist_sl p (get_next x)) m1 m2;
  assert (reveal m12 == join m1 m2);
  // #3
  intro_star
    (ptr r `Mem.star` llist_sl p (get_next x))
    (hp_of (p (get_data x)))
    m12 m3;
  assert (m == join m12 m3);
  ()

val tail_cell (#a:Type0) (p : a -> vprop) (ptr:t a)
  : Steel (cell a)
  (llist_cell p ptr)
  (fun n ->
    vptr ptr `star`
    llist_cell p (get_next n) `star`
    p (get_data n))
  (requires fun _ -> ptr =!= null_t)
  (ensures fun h0 n h1 ->
    Cons? (v_cell p ptr h0) /\
    sel ptr h1 == n /\
    v_cell p ptr h0 ==
      (sel ptr h1) :: (v_cell p (get_next n) h1))

let tail_cell_lemma2 (#a:Type0) (p : a -> vprop) (r:t a) (l:list (cell a)) (m:mem) (x : cell a) (tl : list (cell a)) : Lemma
  (requires interp (llist_sl p r) m /\ llist_sel_cell p r m == l /\ l == x :: tl)
  (ensures
    interp (
      ptr r `Mem.star`
      llist_sl p (get_next x) `Mem.star`
      hp_of (p (get_data x))
    ) m /\
    sel_of (vptr r) m == x /\
    llist_sel_cell p (get_next x) m == tl)
   = tail_cell_lemma p r l m

let change_slprop_rel_with_cond (#opened:inames)
  (p q:vprop)
  (cond: normal (t_of p) -> prop)
  (rel : normal (t_of p) -> normal (t_of q) -> prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ cond (sel_of p m))
    (ensures interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : SteelGhost unit opened p (fun _ -> q) (fun h0 -> cond (h0 p)) (fun h0 _ h1 -> rel (h0 p) (h1 q))
  = change_slprop_rel_with_cond #opened p q cond rel l

let tail_cell #a p ptr
  =
  reveal_non_empty_cell p ptr;
  let h = get () in
  let l = hide (v_cell p ptr h) in

  let x = hide (L.hd l) in
  let tl = hide (L.tl l) in

  change_slprop_rel_with_cond
    (llist_cell p ptr)
    (vptr ptr `star`
    llist_cell p (get_next x) `star`
    p (get_data x))
    (fun tp -> hide tp == l)
    (fun a ((fs, sn), _) -> hide fs == x /\ hide sn == tl)
    (fun m -> tail_cell_lemma2 p ptr l m x tl);
  let n = read ptr in
  change_slprop_rel (llist_cell p (get_next x)) (llist_cell p (get_next n)) (fun x y -> x == y) (fun _ -> ());
  change_slprop_rel (p (get_data x)) (p (get_data n)) (fun x y -> x == y) (fun _ -> ());
  return n

val to_list_cell (#a:Type0) (p : a -> vprop) (ptr:t a)
  : Steel unit (llist p ptr) (fun _ -> llist_cell p ptr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> v_llist p ptr h0 == llist_view (v_cell p ptr h1))

let to_list_cell p ptr =
  change_slprop_rel (llist p ptr) (llist_cell p ptr)
  (fun x y -> x == llist_view y) (fun _ -> ())

val from_list_cell (#a:Type0) (p : a -> vprop) (ptr:t a)
  : Steel unit (llist_cell p ptr) (fun _ -> llist p ptr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> v_llist p ptr h1 == llist_view (v_cell p ptr h0))

let from_list_cell p ptr =
  change_slprop_rel (llist_cell p  ptr) (llist p ptr)
  (fun x y -> llist_view x == y) (fun _ -> ())


//val tail (#a:Type0) (p : a -> vprop) (ptr:t a)
//  : Steel (cell a) (llist p ptr)
//                   (fun n -> vptr ptr `star` llist p (get_next n) `star` p (get_data n))
//                   (requires fun _ -> ptr =!= null_t)
//                   (ensures fun h0 n h1 ->
//                     Cons? (v_llist p ptr h0) /\
//                     v_llist p ptr h0 ==
//                       (get_data (sel ptr h1)) :: (v_llist p (get_next n) h1))

//#push-options "--fuel 2"
let tail #a p ptr =
  to_list_cell p ptr;
  let n = tail_cell #a p ptr in
  from_list_cell p (get_next n);
  return n
//#pop-options


(*)
let ind_llist_sl' (#a:Type0) (r:ref (t a)) (p:t a) : slprop u#1 =
  pts_to_sl r full_perm p `Mem.star` llist_sl p
let ind_llist_sl (#a:Type0) (r:ref (t a)) = Mem.h_exists (ind_llist_sl' r)

let ind_llist_sel_full' (#a:Type0) (r:ref (t a)) : selector' (t a * list a) (ind_llist_sl r) =
  fun h ->
    let p = id_elim_exists (ind_llist_sl' r) h in
    (reveal p, llist_sel p h)

let ind_llist_sel_depends_only_on (#a:Type0) (ptr:ref (t a))
  (m0:Mem.hmem (ind_llist_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (ind_llist_sel_full' ptr m0 == ind_llist_sel_full' ptr (Mem.join m0 m1))
  = let m' = Mem.join m0 m1 in
    let p1 = reveal (id_elim_exists (ind_llist_sl' ptr) m0) in
    let p2 = reveal (id_elim_exists (ind_llist_sl' ptr) m') in

    pts_to_witinv ptr full_perm;
    Mem.elim_wi (ind_llist_sl' ptr) p1 p2 m'

let ind_llist_sel_depends_only_on_core (#a:Type0) (ptr:ref (t a))
  (m0:Mem.hmem (ind_llist_sl ptr))
  : Lemma (ind_llist_sel_full' ptr m0 == ind_llist_sel_full' ptr (core_mem m0))
  = let p1 = reveal (id_elim_exists (ind_llist_sl' ptr) m0) in
    let p2 = reveal (id_elim_exists (ind_llist_sl' ptr) (core_mem m0)) in

    pts_to_witinv ptr full_perm;
    Mem.elim_wi (ind_llist_sl' ptr) p1 p2 (core_mem m0)

let ind_llist_sel_full (#a:Type0) (r:ref (t a)) : selector (t a * list a) (ind_llist_sl r) =
  Classical.forall_intro_2 (ind_llist_sel_depends_only_on r);
  Classical.forall_intro (ind_llist_sel_depends_only_on_core r);
  ind_llist_sel_full' r

let ind_llist_sel r = fun h -> snd (ind_llist_sel_full r h)

[@@__steel_reduce__]
let ind_llist_full' #a r : vprop' =
  {hp = ind_llist_sl r;
   t = t a * list a;
   sel = ind_llist_sel_full r}
unfold
let ind_llist_full (#a:Type0) (r:ref (t a)) = VUnit (ind_llist_full' r)

[@@ __steel_reduce__]
let v_full (#a:Type0) (#p:vprop) (r:ref (t a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (ind_llist_full r) /\ True)})
  = h (ind_llist_full r)

let intro_ptr_frame_lemma (#a:Type0) (r:ref a) (x:a) (frame:slprop) (m:mem)
  : Lemma (requires interp (pts_to_sl r full_perm x `Mem.star` frame) m)
          (ensures interp (ptr r `Mem.star` frame) m /\ sel_of (vptr r) m == x)
  = let aux (m:mem) (ml mr:mem) : Lemma
      (requires disjoint ml mr /\ m == join ml mr /\
        interp (pts_to_sl r full_perm x) ml /\ interp frame mr)
      (ensures interp (ptr r `Mem.star` frame) m /\
        sel_of (vptr r) m == x)
      = intro_ptr_interp r (hide x) ml;
        intro_star (ptr r) frame ml mr;
        ptr_sel_interp r ml;
        pts_to_witinv r full_perm
    in
    elim_star (pts_to_sl r full_perm x) frame m;
    Classical.forall_intro_2 (Classical.move_requires_2 (aux m))

let intro_pts_to_frame_lemma (#a:Type0) (r:ref a) (x:a) (frame:slprop) (m:mem)
  : Lemma (requires interp (ptr r `Mem.star` frame) m /\ sel_of (vptr r) m == x)
          (ensures interp (pts_to_sl r full_perm x `Mem.star` frame) m)
  = let aux (m:mem) (ml mr:mem) : Lemma
      (requires disjoint ml mr /\ m == join ml mr /\
        interp (ptr r) ml /\ interp frame mr /\ sel_of (vptr r) ml == x)
      (ensures interp (pts_to_sl r full_perm x `Mem.star` frame) m)
      = ptr_sel_interp r ml;
        intro_star (pts_to_sl r full_perm x) frame ml mr
    in
    elim_star (ptr r) frame m;
    Classical.forall_intro_2 (Classical.move_requires_2 (aux m))


let unpack_ind_lemma (#a:Type0) (r:ref (t a)) (p:t a) (l:list a) (m:mem) : Lemma
  (requires interp (ind_llist_sl r) m /\ ind_llist_sel_full r m == (p, l))
  (ensures
    interp (ptr r `Mem.star` llist_sl p) m /\
    sel_of (vptr r) m == p /\
    sel_of (llist p) m == l)
  = intro_ptr_frame_lemma r p (llist_sl p) m

val unpack_ind_full (#a:Type0) (r:ref (t a))
  : Steel (t a)
             (ind_llist_full r)
             (fun p -> vptr r `star` llist p)
             (requires fun _ -> True)
             (ensures fun h0 p h1 ->
               sel r h1 == p /\
               p == fst (v_full r h0) /\
               v_llist p h1 == snd (v_full r h0))

let unpack_ind_full r =
    let h = get () in
    let s = hide (v_full r h) in
    let gp = hide (fst (reveal s)) in
    let gl = hide (snd (reveal s)) in
    change_slprop
      (ind_llist_full r)
      (vptr r `star` llist (reveal gp))
      s
      (reveal gp, reveal gl)
      (fun m -> unpack_ind_lemma r gp gl m);
    reveal_star (vptr r) (llist (reveal gp));
    let p = read r in
    change_slprop_rel (llist (reveal gp)) (llist p) (fun x y -> x == y) (fun _ -> ());
    return p

let unpack_ind r =
  change_slprop_rel (ind_llist r) (ind_llist_full r) (fun x y -> x == snd y) (fun _ -> ());
  let p = unpack_ind_full r in
  p

let pack_ind_lemma (#a:Type0) (r:ref (t a)) (p:t a) (l:list a) (m:mem)
  : Lemma
    (requires
      interp (ptr r `Mem.star` llist_sl p) m /\
      sel_of (vptr r) m == p /\
      sel_of (llist p) m == l)
    (ensures interp (ind_llist_sl r) m /\ sel_of (ind_llist r) m == l)
  = intro_pts_to_frame_lemma r p (llist_sl p) m;
    intro_h_exists p (ind_llist_sl' r) m;
    let (p', l') = ind_llist_sel_full r m in
    unpack_ind_lemma r p' l' m;
    pts_to_witinv r full_perm

let pack_ind r p =
  let h = get () in
  reveal_star (vptr r) (llist p);
  let gl = hide (v_llist p h) in
  change_slprop (vptr r `star` llist p) (ind_llist r) (p, reveal gl) gl (fun m -> pack_ind_lemma r p gl m)
