module Selectors.LList3

open Steel.FractionalPermission
module Mem = Steel.Memory

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  tail_fuel: Ghost.erased nat;
  next: ref (cell a);
  data: a;
}
#pop-options

let get_next #a (c:cell a) : t a = c.next
let get_data #a (c:cell a) : a = c.data
let mk_cell #a (n: t a) (d:a) = {
  tail_fuel = Ghost.hide 0;
  next = n;
  data = d
}

let null_t #a = null
let is_null_t #a ptr = is_null ptr

let v_null_rewrite
  (a: Type0)
  (_: t_of emp)
: GTot (list a)
= []

let v_c
  (n: Ghost.erased nat)
  (#a: Type0)
  (r: t a)
  (c: normal (t_of (vptr r)))
: GTot prop
= (Ghost.reveal c.tail_fuel < Ghost.reveal n) == true // to ensure vprop termination

let v_c_dep
  (n: Ghost.erased nat)
  (#a: Type0)
  (p: a -> vprop)
  (r: t a)
  (nllist: (n': Ghost.erased nat) -> (r: t a  { Ghost.reveal n' < Ghost.reveal n }) -> Pure vprop (requires True) (ensures (fun y -> t_of y == list a)))
  (c: normal (t_of (vrefine (vptr r) (v_c n r))))
: Tot vprop
= nllist c.tail_fuel c.next `star` p c.data

let v_c_l_rewrite
  (n: Ghost.erased nat)
  (#a: Type0)
  (p: a -> vprop)
  (r: t a)
  (nllist: (n': Ghost.erased nat) -> (r: t a { Ghost.reveal n' < Ghost.reveal n }) -> Pure vprop (requires True) (ensures (fun y -> t_of y == list a)))
  (res: normal (t_of ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n p r nllist)))
: Tot (list a)
= let (| c, (l, _) |) = res in
  c.data :: l

let rec nllist
  (a: Type0)
  (p: a -> vprop)
  (n: Ghost.erased nat)
  (r: t a)
: Pure vprop
  (requires True)
  (ensures (fun y -> t_of y == list a))
  (decreases (Ghost.reveal n))
= if is_null_t r
  then emp `vrewrite` v_null_rewrite a
  else ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n p r (nllist a p)) `vrewrite` v_c_l_rewrite n p r (nllist a p)

let nllist_eq_not_null
  (a: Type0)
  (p: a -> vprop)
  (n: Ghost.erased nat)
  (r: t a)
: Lemma
  (requires (is_null r == false))
  (ensures (
    nllist a p n r == ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n p r (nllist a p)) `vrewrite` v_c_l_rewrite n p r (nllist a p)
  ))
= assert_norm (nllist a p n r ==
    begin if is_null r
    then emp `vrewrite` v_null_rewrite a
    else ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n p r (nllist a p)) `vrewrite` v_c_l_rewrite n p r (nllist a p)
    end
  )

let llist_vdep
  (#a: Type0)
  (p: a -> vprop)
  (r: t a)
  (c: normal (t_of (vptr r)))
: Tot vprop
= nllist a p c.tail_fuel c.next `star` p c.data

let llist_vrewrite
  (#a: Type0)
  (p: a -> vprop)
  (r: t a)
  (cl: normal (t_of (vptr r `vdep` llist_vdep p r)))
: GTot (list a)
= (dfst cl).data :: fst (dsnd cl)

let llist0
  (#a: Type0)
  (p: a -> vprop)
  (r: t a)
: Pure vprop
  (requires True)
  (ensures (fun y -> t_of y == list a))
= if is_null r
  then emp `vrewrite` v_null_rewrite a
  else (vptr r `vdep` llist_vdep p r) `vrewrite` llist_vrewrite p r

let nllist_of_llist0
  (#opened: _)
  (#a: Type0)
  (p: a -> vprop)
  (r: t a)
: SteelGhost (Ghost.erased nat) opened
    (llist0 p r)
    (fun res -> nllist a p res r)
    (fun _ -> True)
    (fun h0 res h1 ->
      h0 (llist0 p r) == h1 (nllist a p res r)
    )
=
  if is_null r
  then begin
    let res = Ghost.hide 0 in
    change_equal_slprop
      (llist0 p r)
      (nllist a p res r);
    res
  end else begin
    change_equal_slprop
      (llist0 p r)
      ((vptr r `vdep` llist_vdep p r) `vrewrite` llist_vrewrite p r);
    elim_vrewrite (vptr r `vdep` llist_vdep p r) (llist_vrewrite p r);
    let gk : normal (Ghost.erased (t_of (vptr r))) = elim_vdep (vptr r) (llist_vdep p r) in
    let res = Ghost.hide (Ghost.reveal (Ghost.reveal gk).tail_fuel + 1) in
    intro_vrefine (vptr r) (v_c res r);
    intro_vdep
      (vptr r `vrefine` v_c res r)
      (llist_vdep p r (Ghost.reveal gk))
      (v_c_dep res p r (nllist a p));
    intro_vrewrite ((vptr r `vrefine` v_c res r) `vdep` v_c_dep res p r (nllist a p)) (v_c_l_rewrite res p r (nllist a p));
    nllist_eq_not_null a p res r;
    change_equal_slprop
      (((vptr r `vrefine` v_c res r) `vdep` v_c_dep res p r (nllist a p)) `vrewrite` v_c_l_rewrite res p r (nllist a p))
      (nllist a p res r);
    res
  end

let llist0_of_nllist
  (#opened: _)
  (#a: Type0)
  (p: a -> vprop)
  (n: Ghost.erased nat)
  (r: t a)
: SteelGhost unit opened
    (nllist a p n r)
    (fun _ -> llist0 p r)
    (fun _ -> True)
    (fun h0 res h1 ->
      h1 (llist0 p r) == h0 (nllist a p n r)
    )
=
  if is_null r
  then begin
    change_equal_slprop
      (nllist a p n r)
      (llist0 p r);
    ()
  end else begin
    nllist_eq_not_null a p n r;
    change_equal_slprop
      (nllist a p n r)
      (((vptr r `vrefine` v_c n r) `vdep` v_c_dep n p r (nllist a p)) `vrewrite` v_c_l_rewrite n p r (nllist a p));
    elim_vrewrite ((vptr r `vrefine` v_c n r) `vdep` v_c_dep n p r (nllist a p)) (v_c_l_rewrite n p r (nllist a p));
    let gk = elim_vdep (vptr r `vrefine` v_c n r) (v_c_dep n p r (nllist a p)) in
    elim_vrefine (vptr r) (v_c n r);
    intro_vdep
      (vptr r)
      (v_c_dep n p r (nllist a p) (Ghost.reveal gk))
      (llist_vdep p r);
    intro_vrewrite (vptr r `vdep` llist_vdep p r) (llist_vrewrite p r);
    change_equal_slprop
      ((vptr r `vdep` llist_vdep p r) `vrewrite` llist_vrewrite p r)
      (llist0 p r)
  end

let llist_sl
  #a p r
= hp_of (llist0 p r)

let llist_sel
  #a p r
= fun m -> sel_of (llist0 p r) m // eta necessary because sel_of is GTot

let llist_of_llist0
  (#opened: _)
  (#a: Type)
  (p: a -> vprop)
  (r: t a)
: SteelGhost unit opened
    (llist0 p r)
    (fun _ -> llist p r)
    (fun _ -> True)
    (fun h0 _ h1 -> h1 (llist p r) == h0 (llist0 p r))
=
  change_slprop_rel
    (llist0 p r)
    (llist p r)
    (fun x y -> x == y)
    (fun _ -> ())

let llist0_of_llist
  (#opened: _)
  (#a: Type)
  (p: a -> vprop)
  (r: t a)
: SteelGhost unit opened
    (llist p r)
    (fun _ -> llist0 p r)
    (fun _ -> True)
    (fun h0 _ h1 -> h1 (llist0 p r) == h0 (llist p r))
=
  change_slprop_rel
    (llist p r)
    (llist0 p r)
    (fun x y -> x == y)
    (fun _ -> ())

let intro_llist_nil #opened #a p =
  intro_vrewrite emp (v_null_rewrite a);
  change_equal_slprop
    (emp `vrewrite` v_null_rewrite a)
    (llist0 p (null_t #a));
  llist_of_llist0 p (null_t #a)

let is_nil' (#opened: _) (#a:Type0) (ptr:t a)
  : SteelGhost unit opened (llist ptr) (fun _ -> llist ptr)
          (requires fun _ -> True)
          (ensures fun h0 _ h1 ->
            let res = is_null ptr in
            (res == true <==> ptr == null_llist #a) /\
            v_llist ptr h0 == v_llist ptr h1 /\
            res == Nil? (v_llist ptr h1))
=
  let res = is_null ptr in
  llist0_of_llist ptr;
  if res
  then begin
    change_equal_slprop
      (llist0 ptr)
      (emp `vrewrite` v_null_rewrite a);
    elim_vrewrite emp (v_null_rewrite a);
    intro_vrewrite emp (v_null_rewrite a);
    change_equal_slprop
      (emp `vrewrite` v_null_rewrite a)
      (llist0 ptr)
  end else begin
    change_equal_slprop
      (llist0 ptr)
      ((vptr ptr `vdep` llist_vdep ptr) `vrewrite` llist_vrewrite ptr);
      elim_vrewrite (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr);
      intro_vrewrite (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr);
    change_equal_slprop
      ((vptr ptr `vdep` llist_vdep ptr) `vrewrite` llist_vrewrite ptr)
      (llist0 ptr)
  end;
  llist_of_llist0 ptr

let is_nil
  #a ptr
= is_nil' ptr;
  return (is_null ptr)

let intro_llist_cons
  #a ptr1 ptr2
=
  llist0_of_llist ptr2;
  let n = nllist_of_llist0 ptr2 in
  (* set the fuel of the new cons cell *)
  let c = read ptr1 in
  let c' = {c with tail_fuel = n} in
  write ptr1 c' ;
  (* actually cons the cell *)
  vptr_not_null ptr1;
  intro_vdep
    (vptr ptr1)
    (nllist a n ptr2)
    (llist_vdep ptr1);
  intro_vrewrite
    (vptr ptr1 `vdep` llist_vdep ptr1)
    (llist_vrewrite ptr1);
  change_equal_slprop
    ((vptr ptr1 `vdep` llist_vdep ptr1) `vrewrite` llist_vrewrite ptr1)
    (llist0 ptr1);
  llist_of_llist0 ptr1

let tail
  #a ptr
=
  llist0_of_llist ptr;
  change_equal_slprop
    (llist0 ptr)
    ((vptr ptr `vdep` llist_vdep ptr) `vrewrite` llist_vrewrite ptr);
  elim_vrewrite (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr);
  let gc = elim_vdep (vptr ptr) (llist_vdep ptr) in
  (* reset tail fuel to match mk_cell *)
  let c = read ptr in
  let c' = {c with tail_fuel = Ghost.hide 0} in
  write ptr c' ;
  (* actually destruct the list *)
  change_equal_slprop
    (llist_vdep ptr (Ghost.reveal gc))
    (nllist a c.tail_fuel c.next);
  llist0_of_nllist c.tail_fuel c.next;
  llist_of_llist0 c.next;
  return c.next
