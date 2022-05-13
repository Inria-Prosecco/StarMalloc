module Impl.Allocator2

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
// addr_of en Steel : ok pour les structures dans le tas ?
// procéder par un lemme à part pour l'égalité des arrays
// (Spec.split ~= SA5.split)

open Steel.Array5
//open Array

#set-options "--ide_id_info_off"

noeq
type block = {
  size: U.t;
  size_ptr: ref U.t;
  is_free: bool;
  is_free_ptr: ref bool;
  content: x:array FStar.UInt8.byte{length x == U.v size};
  content_ptr: ref (array FStar.UInt8.byte);
}

let mk_block size size_ptr is_free is_free_ptr content content_ptr
: block
= {
  size;
  size_ptr;
  is_free;
  is_free_ptr;
  content;
  content_ptr;
}

let t = ref block

//[@@ __steel_reduce__]
let get_size_ptr blk : ref U.t = blk.size_ptr
//[@@ __steel_reduce__]
let get_status_ptr blk : ref bool = blk.is_free_ptr
//[@@ __steel_reduce__]
let get_content_ptr blk : ref (array FStar.UInt8.byte) = blk.content_ptr

//[@@ __steel_reduce__]
let get_size blk : U.t = blk.size
//[@@ __steel_reduce__]
let get_status blk : bool = blk.is_free
//[@@ __steel_reduce__]
let get_content blk : array FStar.UInt8.byte = blk.content

let block_sl' (ptr: t) (blk: block) : Tot Mem.slprop
  =
  pts_to_sl ptr full_perm blk `Mem.star`
  pts_to_sl (get_size_ptr blk) full_perm (get_size blk) `Mem.star`
  pts_to_sl (get_status_ptr blk) full_perm (get_status blk) `Mem.star`
  pts_to_sl (get_content_ptr blk) full_perm (get_content blk) `Mem.star`
  is_array #(FStar.UInt8.byte) (get_content blk)

  //pts_to_sl (get_size blk) full_perm (U.uint_to_t size)
  //pts_to_sl ptr full_perm blk `Mem.star`
  //pts_to_sl (get_size blk) full_perm

let block_sl ptr : Mem.slprop u#1
  = Mem.h_exists (block_sl' ptr)

//assume
let convert (size : U.t) (content: array FStar.UInt8.byte)
  //: (Spec.bytes (U.v size))
  : Spec.bytes (U.v size)
  =
  content

(*)
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
*)

let block_view (blk: block) : Tot Spec.block
  =
  //let content : bytes (size) = get_content blk in
  //let content2 : Spec.bytes (U.v size) = content in
  Spec.mk_block
    (U.v (get_size blk))
    (get_status blk)
    (get_content blk)

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

(*)
[@@ __steel_reduce__]
let vblockll' (ptr: t) : vprop' = {
  hp = block_sl ptr;
  t = block;
  sel = block_sel_ll ptr
}
*)

[@@ __steel_reduce__]
let vblock' (ptr: t) : vprop' = {
  hp = block_sl ptr;
  t = Spec.block;
  sel = block_sel ptr
}


//unfold
//let vblockll (ptr: t) : vprop
//  = VUnit (vblockll' ptr)

unfold
let vblock (ptr: t) : vprop
  = VUnit (vblock' ptr)

//let blk_hl2ll (ptr: t) : SteelT unit
//  (vblock ptr) (fun _ -> vblockll ptr)
//  = rewrite_slprop (vblock ptr) (vblockll ptr) (fun _ -> ())
//
//let blk_ll2hl (ptr: t) : SteelT unit
//  (vblockll ptr) (fun _ -> vblock ptr)
//  = rewrite_slprop (vblockll ptr) (vblock ptr) (fun _ -> ())

let lblock (ptr: Selectors.LList.t t) : Mem.slprop u#1
  = llist_sl #(t)
  (fun elem -> vblock elem) ptr

//[@@ __steel_reduce__]
//let v_block_ll (#p:vprop) (ptr: t)
//  (h: rmem p{FStar.Tactics.with_tactic
//    selector_tactic
//    (can_be_split p (vblockll ptr) /\ True)
//  })
//  : GTot block
//  = h (vblockll ptr)

[@@ __steel_reduce__]
let v_block (#p:vprop) (ptr: t)
  (h: rmem p{FStar.Tactics.with_tactic
    selector_tactic
    (can_be_split p (vblock ptr) /\ True)
  })
  : GTot Spec.block
  = h (vblock ptr)

assume
val _pack_block (ptr: t) (blk: block)
  //(size_r: ref U.t)
  //(status_r: ref bool)
  //(content_r: ref (array FStar.UInt8.byte))
  : Steel unit
  (vptr ptr `star`
  //vptr size_r `star`
  //vptr status_r `star`
  //vptr content_r `star`
  vptr (get_size_ptr blk) `star`
  vptr (get_status_ptr blk) `star`
  vptr (get_content_ptr blk) `star`
  varray (get_content blk))
  (fun _ -> vblock ptr)
  (requires (fun h0 ->
    //get_size_ptr blk == size_r /\
    //get_status_ptr blk == status_r /\
    //get_content_ptr blk == content_r /\
    sel ptr h0 == blk /\
    sel (get_size_ptr blk) h0 == get_size blk /\
    sel (get_status_ptr blk) h0 == get_status blk /\
    sel (get_content_ptr blk) h0 == get_content blk /\
    U.v (get_size blk) == length (get_content blk)
  ))
  (ensures fun h0 _ h1 ->
    let size = U.v (get_size blk) in
    let status = get_status blk in
    //let content = convert (get_size blk) (get_content blk) in
    let content = get_content blk in
    v_block ptr h1 == Spec.mk_block size status content
  )



assume
val pack_block (ptr: t)
//(blk: block)
  (size_r: ref U.t)
  (status_r: ref bool)
  (content_r: ref (array FStar.UInt8.byte))
  (content: array FStar.UInt8.byte)
  : Steel unit
  (vptr ptr `star`
  vptr size_r `star`
  vptr status_r `star`
  vptr content_r `star`
  //vptr (get_size_ptr blk) `star`
  //vptr (get_status_ptr blk) `star`
  //vptr (get_content_ptr blk) `star`
  varray content)
  (fun _ -> vblock ptr)
  (requires (fun h0 ->
    let blk = sel ptr h0 in
    get_size_ptr blk == size_r /\
    get_status_ptr blk == status_r /\
    get_content_ptr blk == content_r /\
    //sel ptr h0 == blk /\
    //sel size_r h0 == get_size blk /\
    //sel status_r h0 == get_status blk /\
    //sel content_r h0 == get_content blk /\
    U.v (get_size blk) == length (get_content blk)
  ))
  (ensures fun h0 _ h1 ->
    let blk = sel ptr h0 in
    let size = U.v (get_size blk) in
    let status = get_status blk in
    //let content = convert (get_size blk) (get_content blk) in
    let content = get_content blk in
    v_block ptr h1 == Spec.mk_block size status content
  )

assume
val unpack_block (ptr: t)
  : Steel block
  (vblock ptr)
  (fun blk ->
  vptr ptr `star`
  vptr (get_size_ptr blk) `star`
  vptr (get_status_ptr blk) `star`
  vptr (get_content_ptr blk) `star`
  varray (get_content blk))
  (requires fun _ -> True)
  (ensures (fun h0 blk h1 ->
    sel ptr h1 == blk /\
    sel (get_size_ptr blk) h1 == get_size blk /\
    sel (get_status_ptr blk) h1 == get_status blk /\
    sel (get_content_ptr blk) h1 == get_content blk /\
    U.v (get_size blk) == length (get_content blk) /\
    v_block ptr h0 == Spec.mk_block
      (U.v (get_size blk))
      (get_status blk)
      //(convert (get_size blk) (get_content blk))
      (get_content blk)

  ))

let split_block_lemma (blk: block) (size: U.t)
  : Lemma
  (requires
    U.v size <= Spec.get_size (block_view blk) /\
    Spec.get_size (block_view blk)
    == Seq.length (Spec.get_content (block_view blk))
  )
  (ensures
    (let b1, b2 = Spec.split_block (block_view blk) (U.v size) in
    let bytes = Spec.get_content b1, Spec.get_content b2 in
    bytes = Seq.split (Spec.get_content (block_view blk)) (U.v size)))
  = ()

let append_split_lemma (#t: Type0) (s1 s2 s: Seq.seq t) (l: nat)
  : Lemma
  (requires
    Seq.equal (Seq.append s1 s2) s /\
    Seq.length s1 = l
  )
  (ensures
    (s1, s2) == Seq.split s l
  )
  =
  let s3, s4 = Seq.split s l in
  Seq.lemma_append_inj s1 s2 s3 s4

let split_root_lemma (#t: Type0) (arr: array t) (ptr: ref (array t)) (size: U.t)
  : Steel (array t & array t & ref (array t) & ref (array t))
  (varray arr `star` vptr ptr)
  (fun r ->
  varray (_fst r) `star`
  varray (_snd r) `star`
  vptr (_thd r) `star`
  vptr (_fth r)
  )
  (requires fun h0 ->
    U.v size < length arr /\
    get_prev arr == None /\
    get_succ arr == None /\
    sel ptr h0 == arr
  )
  (ensures fun h0 r h1 ->
    U.v size < length arr /\
    adjacent (_fst r) (_snd r) /\
    get_prev (_fst r) == None /\
    get_succ (_snd r) == None /\
    sel (_thd r) h1 == _fst r /\
    sel (_fth r) h1 == _snd r /\
    length (_fst r) = U.v size /\
    length (_fst r) + length (_snd r) == length arr /\
    Seq.append (_fst r) (_snd r) == arr /\
      //(reveal (asel (_fst r) h1))
      //(reveal (asel (_snd r) h1))
    //== asel arr h0 /\
    _fst r
    //reveal (asel (_fst r) h1)
    == fst (Seq.split arr (U.v size)) /\
    _snd r
    //reveal (asel (_snd r) h1)
    == snd (Seq.split arr (U.v size)) /\
    //(let arr1 = asel (_fst r) h1 in
    //let arr2 = asel (_snd r) h1 in
    //let arr0 = asel arr h0 in
    (let arr1 = _fst r in
    let arr2 = _snd r in
    let arr0 = arr in
    let r1 = Seq.split arr0 (U.v size) in
    let r2 = arr1, arr2 in
    U.v size < length arr /\
    length arr = Seq.length arr /\
    r1 == r2)
    //fst r1 == fst r2 /\
    //snd r1 == snd r2)
  )
  =
  let h0 = get () in
  let r = split_root arr ptr size in
  let h1 = get () in
  //let arr0 = hide (asel arr h0) in
  //let arr1 = hide (asel (_fst r) h1) in
  //let arr2 = hide (asel (_snd r) h1) in
  let arr0 = arr in
  let arr1 = _fst r in
  let arr2 = _snd r in
  assert (
    Seq.append (reveal arr1) (reveal arr2) == reveal arr0 /\
    Seq.length (reveal arr1) = U.v size
  );
  append_split_lemma
    arr1 arr2 arr0 (U.v size);
  assert ((reveal arr1, reveal arr2)
    == Seq.split arr0 (U.v size));
  return r

(*)



  assert (
    Seq.append arr1 arr2 == reveal arr0 /\
    Seq.length arr1 = U.v size /\
    Seq.length arr1 + Seq.length arr2 = Seq.length arr0
  );
  let arrs34 = hide (Seq.split arr0 (U.v size)) in
  let arr3 = hide (fst (reveal arrs34)) in
  let arr4 = hide (snd (reveal arrs34)) in
  assert (
    Seq.append arr3 arr4 == reveal arr0 /\
    Seq.length arr3 = U.v size /\
    Seq.length arr3 + Seq.length arr4 = Seq.length arr0
  );
  assert (Seq.length arr1 = Seq.length arr3);
  assert (Seq.length arr2 = Seq.length arr4);
  let arr12 = hide (Seq.append arr1 arr2) in
  let arr34 = hide (Seq.append arr3 arr4) in
  assert (arr12 == arr34);
  //Seq.lemma_eq_refl arr12 arr34;
  //let b : x:bool{x = true} = true in
  let arr3 : _:(erased (Seq.seq t)){
    Seq.length (reveal arr1) == Seq.length (reveal arr3) /\
    Seq.length (reveal arr2) == Seq.length (reveal arr4)
  } = arr3 in
  assert (Seq.equal arr12 arr34);
  Seq.lemma_append_inj
    (reveal arr1) (reveal arr2)
    (reveal arr3) (reveal arr4);
  assert (reveal arr1 == reveal arr3);
  assert (reveal arr2 == reveal arr4);
  assert ((arr1, arr2) == (arr3, arr4));
  return r
*)


let test (#opened:Mem.inames) (ptr: t)
  : SteelGhostT Spec.block opened
  (vblock ptr) (fun _ -> vblock ptr)
  =
  let h = get () in
  let b = v_block ptr h in
  b

[@@ expect_failure]
let test2 (#t: Type0) (arr: array t)
  : Steel unit
  (varray arr) (fun _ -> varray arr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    asel arr h0 == asel arr h1 /\
    reveal (asel arr h0) == arr
  )
  =
  return ()

let block_view_content_id (blk: block)
  : Lemma
  (Spec.get_content (block_view blk) == get_content blk)
  = ()

let _get_size (ptr: t)
  : Steel U.t
  (vblock ptr) (fun _ -> vblock ptr)
  (requires fun _ -> True)
  (ensures fun h0 s h1 ->
    let b1 = v_block ptr h1 in
    let b0 = v_block ptr h0 in
    b0.size == b1.size /\
    b0.content == b1.content /\
    b0.is_free == b1.is_free /\
    True
  )
  =
  let blk = unpack_block ptr in
  let s = get_size blk in
  pack_block ptr
    (get_size_ptr blk)
    (get_status_ptr blk)
    (get_content_ptr blk)
    (get_content blk);
  return s



let split_block (ptr: t) (size: U.t)
  : Steel (t & t)
  (vblock ptr)
  (fun r -> vblock (fst r) `star` vblock (snd r))
  (fun h0 ->
    U.v size <= Spec.get_size (v_block ptr h0) /\
    Spec.is_free (v_block ptr h0) /\
    True
    // TODO
    //Spec.get_size (v_block ptr h0)
    //== Seq.length (Spec.get_content (v_block ptr h0))
  )
  (fun h0 r h1 ->
    // TODO
    let _ = admit () in
    // TODO: pre/post cond
    U.v size <= Spec.get_size (v_block ptr h0) /\
    (let spec_r = Spec.split_block (v_block ptr h0) (U.v size) in
    let blk1 = v_block (fst r) h1 in
    let blk2 = v_block (snd r) h1 in
    let sblk1 = fst spec_r in
    let sblk2 = snd spec_r in
    Spec.is_free blk1 == Spec.is_free sblk1 /\
    Spec.is_free blk2 == Spec.is_free sblk2 /\
    Spec.get_size blk1 == Spec.get_size sblk1 /\
    Spec.get_size blk2 == Spec.get_size sblk2 /\
    Spec.get_content blk1 == Spec.get_content sblk1 /\
    blk1 == sblk1 /\
    blk2 == sblk2
    //v_block (fst r) h1 == fst spec_r /\
    //v_block (snd r) h1 == snd spec_r
    )
  )
  =
  //let blk_size = _get_size ptr in
  let h00 = get () in
  let blk = unpack_block ptr in
  let blk_size = read (get_size_ptr blk) in

  // 1 : size
  //let blk_size = get_size blk in
  let new_size1 = size in
  assert (U.v size <= U.v blk_size);
  let new_size2 = U.sub blk_size size in
  assert (U.v new_size1 + U.v new_size2 = U.v blk_size);
  // 2 : status
  //let blk_status = get_status blk in
  //let new_status1 = blk_status in
  //let new_status2 = blk_status in
  let new_status1 = true in
  let new_status2 = true in
  // 3 : content
  assume (U.v size < length (get_content blk));
  assume (get_prev (get_content blk) == None);
  assume (get_succ (get_content blk) == None);
  let h0 = get () in
  //let split_r = split_root
  //  (get_content blk) (get_content_ptr blk) size in
  let split_r = split_root_lemma
    (get_content blk) (get_content_ptr blk) size in
  let h1 = get () in
  //let arr0 = hide (asel (get_content blk) h0) in
  let arr0 = get_content blk in
  //let arr1 = hide (asel (_fst split_r) h1) in
  //let arr2 = hide (asel (_snd split_r) h1) in
  let arr1 = _fst split_r in
  let arr2 = _snd split_r in
  assert (Seq.split arr0 (U.v size)
  == (reveal arr1, reveal arr2));


  let spec_r = hide (Spec.split_block
    (reveal (v_block ptr h00))
    (U.v size)) in
  Spec.split_block_lemma (reveal (v_block ptr h00)) (U.v size);
  assert (reveal arr1 == Spec.get_content (fst spec_r));
  assert (reveal arr2 == Spec.get_content (snd spec_r));
  //admit ();

  //let

  //let h1 = get () in
  //assert (Seq.append
  //  (reveal (asel (_fst split_r) h1))
  //  (reveal (asel (_snd split_r) h1))
  //  == asel (get_content blk) h0);
  //Seq.lemma_split (asel (get_content blk) h0) (U.v size);
  //assert (reveal (asel (_fst split_r) h1)
  //== fst (Seq.split (asel (get_content blk) h0) (U.v size)));
  //assert (reveal (asel (_snd split_r) h1)
  //== snd (Seq.split (asel (get_content blk) h0) (U.v size)));
  //assume (U.v size < Spec.get_size (reveal (v_block ptr h00)));
  //assume (Spec.get_size (reveal (v_block ptr h00))
  //== Seq.length (Spec.get_content (reveal (v_block ptr h00))));
  //let sblk1 = fst spec_r in
  //let sblk2 = snd spec_r in

  //assert (Spec.get_content (v_block (_fst split_r) h1)
  //== snd (Seq.split (asel (get_content blk) h0) (U.v size)));

  //assert (Spec.get_content (v_block ptr h0)
  //  == asel (get_content blk) h0);
  //admit (); sladmit ();

  // 1 : blk1
  write (get_size_ptr blk) new_size1;
  write (get_status_ptr blk) new_status1;
  let new_blk1 = mk_block
    new_size1 (get_size_ptr blk)
    new_status1 (get_status_ptr blk)
    (_fst split_r) (_thd split_r) in
  write ptr new_blk1;
  pack_block ptr
    (get_size_ptr blk)
    (get_status_ptr blk)
    (_thd split_r)
    (_fst split_r);
  // 2 : blk2
  let new_size_ptr2 = malloc new_size2 in
  let new_status_ptr2 = malloc new_status2 in
  let new_blk2 = mk_block
    new_size2 new_size_ptr2
    new_status2 new_status_ptr2
    (_snd split_r) (_fth split_r) in
  let new_blk_ptr2 = malloc new_blk2 in
  pack_block new_blk_ptr2
    new_size_ptr2
    new_status_ptr2
    (_fth split_r)
    (_snd split_r);
  //admit ();
  //sladmit ();
  return (ptr, new_blk_ptr2)


(*)
// comme create_tree{,_no_alloc}
// no_root : besoin d'ouvrir le bloc précédent et le bloc suivant
// varray as for tree, with the possibility of being null?
// could ease many things

//let merge_block

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
