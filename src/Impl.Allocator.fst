module Impl.Allocator

open FStar.Ghost
open Steel.FractionalPermission
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

open Selectors.LList

module Mem = Steel.Memory
module U = FStar.UInt32
module Seq = FStar.Seq
module Spec = Allocator

// TODO
// M-. does not work (Doom Emacs ?)
// frame_equalities plutôt que des propriétés fastidieuses
// -> définir un effet custom devrait être trivial
// tout ajouter avec des pointeurs

open Steel.Array5
//open Array

#set-options "--ide_id_info_off"

//type bytes (s: U.t) = Seq.lseq FStar.UInt8.byte (U.v s)

//unfold
//type bytes = array FStar.UInt8.byte
//type bytes = array FStar.UInt8.byte

noeq
type block = {
  //size: ref U.t;
  //size: y:U.t{y = U.zero};
  size: U.t;
  //is_free: x:bool{x = true};
  is_free: bool;
  ptr: ref (array FStar.UInt8.byte);
  //ptr2: ref (ref (bytes size));
  content: array FStar.UInt8.byte;
  //pos: erased U.t;
}
let t = ref block

//let get_size2 (blk: t) =



let get_size blk = blk.size
let is_free blk = blk.is_free
let get_ptr blk : ref (array FStar.UInt8.byte) = blk.ptr
//let get_ptr2 blk = blk.ptr2
let get_content blk : array FStar.UInt8.byte = blk.content
//let get_pos blk = blk.pos

let block_sl' (ptr: t) (blk: block) : Tot Mem.slprop
  //= match blk with
  //| { size; is_free; content } ->
  =
  pts_to_sl ptr full_perm blk `Mem.star`
  pts_to_sl (get_ptr blk) full_perm (get_content blk) `Mem.star`
  is_array #(FStar.UInt8.byte) (get_content blk)

  //pts_to_sl (get_size blk) full_perm (U.uint_to_t size)
  //pts_to_sl ptr full_perm blk `Mem.star`
  //pts_to_sl (get_size blk) full_perm

let block_sl ptr : Mem.slprop u#1
  = Mem.h_exists (block_sl' ptr)

assume
val convert (size : U.t) (content: array FStar.UInt8.byte)
  //: (Spec.bytes (U.v size))
  : Spec.bytes

let convert_eq (size1 size2 : U.t)
  (content1 content2: array FStar.UInt8.byte)
  : Lemma
  (requires
    size1 == size2 /\
    content1 == content2
  )
  (ensures
    convert size1 content1 == convert size2 content2
  )
  = ()

let block_view (blk: block) : Tot Spec.block
  =
  //let content : bytes (size) = get_content blk in
  //let content2 : Spec.bytes (U.v size) = content in
  Spec.mk_block
    (U.v blk.size)
    (is_free blk)
    (convert blk.size (get_content blk))

let block_sl'_witinv (ptr: t)
  : Lemma (Mem.is_witness_invariant (block_sl' ptr))
  = admit ()

let block_sel_ll' (ptr: t)
  : selector' block (block_sl ptr)
  = fun h -> Mem.id_elim_exists (block_sl' ptr) h

let block_sel_depends_only_on (ptr: t)
  (m0: Mem.hmem (block_sl ptr))
  (m1: Mem.mem{Mem.disjoint m0 m1})
  : Lemma (
  block_sel_ll' ptr m0 == block_sel_ll' ptr (Mem.join m0 m1)
  )
  = admit ()

let block_sel_depends_only_on_core (ptr: t)
  (m0: Mem.hmem (block_sl ptr))
  : Lemma (
  block_sel_ll' ptr m0 == block_sel_ll' ptr (Mem.core_mem m0)
  )
  = admit ()

let block_sel_ll (ptr: t)
  : selector block (block_sl ptr)
  =
  Classical.forall_intro_2 (block_sel_depends_only_on ptr);
  Classical.forall_intro (block_sel_depends_only_on_core ptr);
  block_sel_ll' ptr

let block_sel (ptr: t)
  : selector Spec.block (block_sl ptr)
  =
  fun h -> block_view (block_sel_ll ptr h)

[@@ __steel_reduce__]
let vblockll' (ptr: t) : vprop' = {
  hp = block_sl ptr;
  t = block;
  sel = block_sel_ll ptr
}

[@@ __steel_reduce__]
let vblock' (ptr: t) : vprop' = {
  hp = block_sl ptr;
  t = Spec.block;
  sel = block_sel ptr
}


unfold
let vblockll (ptr: t) : vprop
  = VUnit (vblockll' ptr)

unfold
let vblock (ptr: t) : vprop
  = VUnit (vblock' ptr)

let blk_hl2ll (ptr: t) : SteelT unit
  (vblock ptr) (fun _ -> vblockll ptr)
  = rewrite_slprop (vblock ptr) (vblockll ptr) (fun _ -> ())

let blk_ll2hl (ptr: t) : SteelT unit
  (vblockll ptr) (fun _ -> vblock ptr)
  = rewrite_slprop (vblockll ptr) (vblock ptr) (fun _ -> ())

let block_to_sl (blk: block) : vprop
  = to_vprop (pts_to_sl (get_ptr blk) full_perm (get_content blk))

let lblock (ptr: Selectors.LList.t t) : Mem.slprop u#1
  = llist_sl #(t)
  (fun elem -> vblock elem) ptr

(*
//type lblock = llist #block (fun blk -> to_vprop (
type lblock = llist #block (fun blk ->
  //ptr_to_content (get_size blk) (get_ptr blk) (get_content blk)
  //block_to_sl blk
  block_sl
)
*)

[@@ __steel_reduce__]
let v_block_ll (#p:vprop) (ptr: t)
  (h: rmem p{FStar.Tactics.with_tactic
    selector_tactic
    (can_be_split p (vblockll ptr) /\ True)
  })
  : GTot block
  = h (vblockll ptr)



[@@ __steel_reduce__]
let v_block (#p:vprop) (ptr: t)
  (h: rmem p{FStar.Tactics.with_tactic
    selector_tactic
    (can_be_split p (vblock ptr) /\ True)
  })
  : GTot Spec.block
  = h (vblock ptr)

(*)
  Spec.mk_block
  (U.v (get_size blk))
  (is_free blk)
  (convert (get_size blk) (asel (get_content blk) h))
  //(h (i))
*)

assume
val pack_block (ptr: t) (blk: block)
  : Steel unit
  (vptr ptr `star`
  vptr (get_ptr blk) `star`
  varray (get_content blk))
  (fun _ -> vblock ptr)
  (requires (fun h0 ->
    sel ptr h0 == blk /\
    sel (get_ptr blk) h0 == get_content blk /\
    U.v (get_size blk) == length (get_content blk)
  ))
  (ensures fun h0 _ h1 ->
    True
  )
    //v_block ptr h1 =


assume
val unpack_block (ptr: t)
  : Steel block
  (vblock ptr)
  (fun blk ->
  vptr ptr `star`
  vptr (get_ptr blk) `star`
  varray (get_content blk))
  (requires fun _ -> True)
  (ensures (fun _ blk h1 ->
    sel ptr h1 == blk /\
    sel (get_ptr blk) h1 == get_content blk /\
    U.v (get_size blk) == length (get_content blk)
  ))

let test (#opened:Mem.inames) (ptr: t)
  : SteelGhostT Spec.block opened
  (vblock ptr) (fun _ -> vblock ptr)
  =
  let h = get () in
  let b = v_block ptr h in
  b

//#set-options "--fuel 2 --ifuel 2"
let get_size2 (ptr: t)
  : Steel U.t
  (vblockll ptr) (fun _ -> vblockll ptr)
  (requires fun _ -> True)
  (ensures fun h0 s h1 ->
    let b1 = v_block_ll ptr h1 in
    let b0 = v_block_ll ptr h0 in
    b0.is_free == b1.is_free /\
    b0.size == b1.size /\
    b0.content == b1.content /\
    True
  )
  =
  blk_ll2hl ptr;
  let blk = unpack_block ptr in
  let s = get_size blk in
  pack_block ptr blk;
  blk_hl2ll ptr;
  return s


let _get_size (ptr: t)
  : Steel (U.t)
  (vblock ptr) (fun _ -> vblock ptr)
  (requires fun _ -> True)
  (ensures fun h0 s h1 ->
    let b1 = v_block ptr h1 in
    let b0 = v_block ptr h0 in
    b0.is_free == b1.is_free /\
    b0.size == b1.size /\
    b0.content == b1.content /\

    //v_block ptr h1 == v_block ptr h0 /\
    //frame_equalities (vblock ptr) h0 h1
    True
    //U.v s == Spec.get_size (v_block ptr h0)
  )
  =
  let blk = unpack_block ptr in
  let s = get_size blk in
  pack_block ptr blk;
  return s



let split_block (ptr: t) (size: U.t)
  : Steel (t & t)
  (vblock ptr)
  (fun r -> vblock (fst r) `star` vblock (snd r))
  (fun h0 ->
    U.v size <= Spec.get_size (v_block ptr h0)
  )
  (fun h0 r h1 ->
    // TODO: pre/post cond
    U.v size <= Spec.get_size (v_block ptr h0) /\
    (let spec_r = Spec.split_block (v_block ptr h0) (U.v size) in
    v_block (fst r) h1 == fst spec_r /\
    v_block (snd r) h1 == snd spec_r
    )
  )
  =
  let blk = unpack_block ptr in
  let blk_size = get_size blk in
  let new_size1 = size in
  assert (U.v size <= U.v blk_size);
  let new_size2 = U.sub blk_size size in
  assert (U.v new_size1 + U.v new_size2 = U.v blk_size);

  pack_block ptr blk;
  //let blk
  admit (); sladmit ();
  return (ptr, ptr)

//let merge_block

(*)
let split_block (blk: block) (size: U.t)
  : Steel (block & block)
  (block_to_sl blk)
  (fun r -> block_to_sl (fst r) `star` block_to_sl (snd r))
  (fun _ ->
    U.v size <= U.v (get_size blk))
  (fun _ r _ ->
    U.v size <= U.v (get_size blk) /\
    (let spec_r = Spec.split_block (v_block blk) (U.v size) in
    v_block (fst r) == fst spec_r /\
    v_block (snd r) == snd spec_r))
  =
  //let h = get () in
  let initial_bytes = split (get_ptr blk) in

  admit (); sladmit ();
  return (blk, blk)






// blocs bien formés : `Star` block_to_sl blk
