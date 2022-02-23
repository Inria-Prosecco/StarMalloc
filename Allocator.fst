module Allocator

open FStar.List.Tot
open Some_lemmas

let size_header = 0

noeq
type block = {
  size: nat;
  is_free: bool;
  content: nat;
}

type lblock = list block

let get_content (b: block) = b.content
let get_is_free (b: block) = b.is_free
let get_size (b: block) = b.size

let mk_block size is_free content = {
  size;
  is_free;
  content;
}

let is_free (b: block) : bool
  = get_is_free b

let f (x y: block)
  = not (is_free x && is_free y)

let comm (x y: block)
: Lemma (f x y = f y x)
 = ()

let rec is_coalesced (l: lblock)
: bool
= match l with
| [] -> true
| x::[] -> true
| x::y::l' ->
    let b = not (is_free x && is_free y) in
    b && is_coalesced (y::l')

let is_coalesced_old (l: lblock)
: bool
= fold_f f l

let rec ic_eq (l: lblock)
: Lemma (is_coalesced l = is_coalesced_old l)
= match l with
| [] -> ()
| [x] -> ()
| x::y::l' -> ic_eq l'

let ic_rev (l: lblock)
: Lemma (is_coalesced l = is_coalesced (rev l))
=
ic_eq l;
ic_eq (rev l);
rev_foldf f l

let rec coalesce_aux (acc l: lblock)
: Tot lblock (decreases length l)
= match l with
| [] -> rev acc
| [x] -> coalesce_aux (x::acc) []
| x::y::l' ->
    if is_free x && is_free y then
      let size_x = get_size x in
      let size_y = get_size y in
      let new_size = size_x + size_y - size_header in
      let new_is_free = true in
      let new_content = 0 in
      let new_block = mk_block new_size new_is_free new_content in
      coalesce_aux acc (new_block::l')
    else if not (is_free y) then
      coalesce_aux (y::x::acc) l'
    else begin
      assert (not (is_free x));
      coalesce_aux (x::acc) (y::l')
    end

let rec coalesce_aux_proof (acc l: lblock)
: Lemma
(requires
  is_coalesced acc /\
  (Cons? acc /\ Cons? l ==> not (is_free (hd acc)))
)
(ensures
  is_coalesced (coalesce_aux acc l)
)
(decreases length l)
= match l with
| [] -> ic_rev acc
| [x] ->
    if Cons? acc then begin
      assert (is_coalesced (x::acc)
      = not (is_free x && is_free (hd acc)) && is_coalesced acc);
      assert (not (is_free (hd acc)));
      assert (is_coalesced (x::acc))
    end else begin
      assert (is_coalesced (x::[]))
    end;
    coalesce_aux_proof (x::acc) []
| x::y::l' ->
    assert (is_coalesced acc);
    if is_free x && is_free y then begin
      let size_x = get_size x in
      let size_y = get_size y in
      let new_size = size_x + size_y - size_header in
      let new_is_free = true in
      let new_content = 0 in
      let new_block = mk_block new_size new_is_free new_content in
      coalesce_aux_proof acc (new_block::l')
    end else if not (is_free y) then begin
      let new_acc = y::x::acc in
      assert (is_coalesced new_acc);
      assert (hd new_acc == y);
      assert (not (is_free (hd new_acc)));
      coalesce_aux_proof new_acc l'
    end else begin
      assert (not (is_free x));
      assert (is_coalesced (x::acc));
      assert (hd (x::acc) == x);
      assert (not (is_free (hd (x::acc))));
      coalesce_aux_proof (x::acc) (y::l')
    end

let coalesce = coalesce_aux []

let coalesce_proof l
: Lemma (is_coalesced (coalesce l))
= coalesce_aux_proof [] l
