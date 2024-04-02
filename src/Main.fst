module Main

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

module TLA = Steel.TLArray

open FStar.Mul
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module A = Steel.Array
module R = Steel.Reference
module L = Steel.SpinLock
module AL = ArrayList
module ALG = ArrayListGen
module SAA = Steel.ArrayArith

open Prelude
open SizeClass
open SteelVRefineDep
open SteelStarSeqUtils

open Config
open Utils2
open Mman

module G = FStar.Ghost

let metadata_max_ex = SlabsCommon2.metadata_max_ex

let slab_size = SlabsCommon2.slab_size

// Size of the slab region for one size class
// metadata_max * page_size
// ==
// metadata_max_ex * slab_size
let sc_slab_region_size = SlabsCommon2.slab_region_size

#push-options  "--ide_id_info_off"
(**  Handwritten mmap functions to allocate basic data structures *)

let ind_aux r idxs : vprop =
  SlabsCommon.ind_varraylist_aux r idxs

let ind_aux2 r idxs : vprop =
  SlabsCommon2.ind_varraylist_aux r idxs

val intro_ind_varraylist_nil (#opened:_)
  (r: A.array AL.cell)
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  : SteelGhost unit opened
      (A.varray r `star` A.varray r_idxs)
      (fun _ -> SlabsCommon.ind_varraylist r r_idxs)
      (requires fun h ->
        let s : Seq.lseq US.t 7 = A.asel r_idxs h in
        A.length r == 0 /\
        Seq.index s 0 == AL.null_ptr /\
        Seq.index s 1 == AL.null_ptr /\
        Seq.index s 2 == AL.null_ptr /\
        Seq.index s 3 == AL.null_ptr /\
        Seq.index s 4 == AL.null_ptr /\
        Seq.index s 5 == AL.null_ptr /\
        Seq.index s 6 == 0sz
      )
      (ensures fun _ _ _ -> True)

let intro_ind_varraylist_nil r r_idxs =
  let open SlabsCommon in
  ALG.intro_arraylist_nil
    pred1 pred2 pred3 pred4 pred5
    r
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    0sz;
  let idxs
    : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  ind_varraylist_aux2_lemma r idxs
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      0sz;
  change_equal_slprop
    (AL.varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v 0sz))
    (ind_varraylist_aux2 r idxs);
  intro_vrefine
    (SlabsCommon.ind_varraylist_aux2 r idxs)
    (SlabsCommon.ind_varraylist_aux_refinement r idxs);
  intro_vdep
    (A.varray r_idxs)
    (SlabsCommon.ind_varraylist_aux r idxs)
    (ind_aux r)

val intro_ind_varraylist_nil2 (#opened:_)
  (r: A.array AL.cell)
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  : SteelGhost unit opened
      (A.varray r `star` A.varray r_idxs)
      (fun _ -> SlabsCommon2.ind_varraylist r r_idxs)
      (requires fun h ->
        let s : Seq.lseq US.t 7 = A.asel r_idxs h in
        A.length r == 0 /\
        Seq.index s 0 == AL.null_ptr /\
        Seq.index s 1 == AL.null_ptr /\
        Seq.index s 2 == AL.null_ptr /\
        Seq.index s 3 == AL.null_ptr /\
        Seq.index s 4 == AL.null_ptr /\
        Seq.index s 5 == AL.null_ptr /\
        Seq.index s 6 == 0sz
      )
      (ensures fun _ _ _ -> True)

let intro_ind_varraylist_nil2 r r_idxs =
  let open SlabsCommon2 in
  ALG.intro_arraylist_nil
    pred1 pred2 pred3 pred4 pred5
    r
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    AL.null_ptr
    0sz;
  let idxs
    : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  ind_varraylist_aux2_lemma r idxs
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      AL.null_ptr
      0sz;
  change_equal_slprop
    (AL.varraylist pred1 pred2 pred3 pred4 pred5 r
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v AL.null_ptr)
      (US.v 0sz))
    (ind_varraylist_aux2 r idxs);
  intro_vrefine
    (SlabsCommon2.ind_varraylist_aux2 r idxs)
    (SlabsCommon2.ind_varraylist_aux_refinement r idxs);
  intro_vdep
    (A.varray r_idxs)
    (SlabsCommon2.ind_varraylist_aux r idxs)
    (ind_aux2 r)

val intro_left_vprop_empty (#opened:_)
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  : SteelGhost unit opened
      (A.varray (split_l md_region 0sz) `star`
      A.varray r_idxs)
      (fun _ -> SlabsCommon.left_vprop sc slab_region md_bm_region md_region r_idxs 0sz)
      (requires fun h ->
        let s : Seq.lseq US.t 7 = A.asel r_idxs h in
        Seq.index s 0 == AL.null_ptr /\
        Seq.index s 1 == AL.null_ptr /\
        Seq.index s 2 == AL.null_ptr /\
        Seq.index s 3 == AL.null_ptr /\
        Seq.index s 4 == AL.null_ptr /\
        Seq.index s 5 == AL.null_ptr /\
        Seq.index s 6 == 0sz
      )
      (ensures fun _ _ _ -> True)

#push-options "--z3rlimit 50"
let intro_left_vprop_empty sc slab_region md_bm_region md_region r_idxs
  =
  let open SlabsCommon in
  intro_ind_varraylist_nil
    (A.split_l md_region 0sz)
    r_idxs;
  let s = gget (ind_varraylist
      (A.split_l md_region 0sz)
      r_idxs) in

  starseq_intro_empty #_
      #(pos:US.t{US.v pos < US.v 0sz})
      #(SlabsCommon.t sc)
      (SlabsCommon.f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SlabsCommon.f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz));

  assert (SeqUtils.init_us_refined (US.v 0sz) `Seq.equal` Seq.empty);

  let open FStar.Tactics in
  assert ((starseq
      #(pos:US.t{US.v pos < US.v 0sz})
      #(t sc)
      (f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz))) ==
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz s))
  by (norm [delta_only [`%left_vprop2]]);

  change_equal_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v 0sz})
      #(t sc)
      (f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz)))
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz s);
  intro_vdep
    (ind_varraylist
      (A.split_l md_region 0sz)
      r_idxs)
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz s)
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz)
#pop-options

val intro_left_vprop_empty2 (#opened:_)
  (sc:sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  : SteelGhost unit opened
      (A.varray (split_l md_region 0sz) `star`
      A.varray r_idxs)
      (fun _ -> SlabsCommon2.left_vprop sc slab_region md_bm_region md_region r_idxs 0sz)
      (requires fun h ->
        let s : Seq.lseq US.t 7 = A.asel r_idxs h in
        Seq.index s 0 == AL.null_ptr /\
        Seq.index s 1 == AL.null_ptr /\
        Seq.index s 2 == AL.null_ptr /\
        Seq.index s 3 == AL.null_ptr /\
        Seq.index s 4 == AL.null_ptr /\
        Seq.index s 5 == AL.null_ptr /\
        Seq.index s 6 == 0sz
      )
      (ensures fun _ _ _ -> True)

#push-options "--z3rlimit 50"
let intro_left_vprop_empty2 sc slab_region md_bm_region md_region r_idxs
  =
  let open SlabsCommon2 in
  intro_ind_varraylist_nil2
    (A.split_l md_region 0sz)
    r_idxs;
  let s = gget (ind_varraylist
      (A.split_l md_region 0sz)
      r_idxs) in

  starseq_intro_empty #_
      #(pos:US.t{US.v pos < US.v 0sz})
      #(SlabsCommon2.t sc)
      (SlabsCommon2.f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SlabsCommon2.f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz));

  assert (SeqUtils.init_us_refined (US.v 0sz) `Seq.equal` Seq.empty);

  let open FStar.Tactics in
  assert ((starseq
      #(pos:US.t{US.v pos < US.v 0sz})
      #(t sc)
      (f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz))) ==
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz s))
  by (norm [delta_only [`%left_vprop2]]);

  change_equal_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v 0sz})
      #(t sc)
      (f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz)))
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz s);
  intro_vdep
    (ind_varraylist
      (A.split_l md_region 0sz)
      r_idxs)
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz s)
    (left_vprop2 sc slab_region md_bm_region md_region r_idxs 0sz)
#pop-options

val intro_right_vprop_empty (#opened:_)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  : SteelGhost unit opened
     (A.varray (split_r slab_region 0sz) `star`
      A.varray (split_r md_bm_region 0sz) `star`
      A.varray (split_r md_region 0sz))
    (fun _ -> SlabsCommon.right_vprop slab_region md_bm_region md_region 0sz)
    (requires fun h ->
      A.asel (split_r slab_region 0sz) h `Seq.equal` Seq.create (A.length slab_region) U8.zero /\
      A.asel (split_r md_bm_region 0sz) h `Seq.equal` Seq.create (A.length md_bm_region) U64.zero)
    (ensures fun _ _ _ -> True)

let intro_right_vprop_empty slab_region md_bm_region md_region =
  let open SlabsCommon in
  change_equal_slprop
    (A.varray (A.split_r slab_region 0sz))
    (A.varray (A.split_r slab_region (US.mul 0sz (u32_to_sz page_size))));
  change_equal_slprop
    (A.varray (A.split_r md_bm_region 0sz))
    (A.varray (A.split_r md_bm_region (US.mul 0sz 4sz)));
  intro_vrefine
    (A.varray (A.split_r slab_region (US.mul 0sz (u32_to_sz page_size)))) zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region (US.mul 0sz 4sz))) zf_u64;
  assert_norm (
    (A.varray (A.split_r slab_region (US.mul 0sz (u32_to_sz page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul 0sz 4sz))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region 0sz) ==
    (right_vprop slab_region md_bm_region md_region 0sz));
  change_equal_slprop
    ((A.varray (A.split_r slab_region (US.mul 0sz (u32_to_sz page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (US.mul 0sz 4sz))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region 0sz))
    (right_vprop slab_region md_bm_region md_region 0sz)

val intro_right_vprop_empty2 (#opened:_)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  : SteelGhost unit opened
     (A.varray (split_r slab_region 0sz) `star`
      A.varray (split_r md_bm_region 0sz) `star`
      A.varray (split_r md_region 0sz))
    (fun _ -> SlabsCommon2.right_vprop slab_region md_bm_region md_region 0sz)
    (requires fun h ->
      A.asel (split_r slab_region 0sz) h `Seq.equal` Seq.create (A.length slab_region) U8.zero /\
      A.asel (split_r md_bm_region 0sz) h `Seq.equal` Seq.create (A.length md_bm_region) false)
    (ensures fun _ _ _ -> True)

let intro_right_vprop_empty2 slab_region md_bm_region md_region =
  let open SlabsCommon2 in
  change_equal_slprop
    (A.varray (A.split_r slab_region 0sz))
    (A.varray (A.split_r slab_region (US.mul 0sz slab_size)));
  intro_vrefine
    (A.varray (A.split_r slab_region (US.mul 0sz slab_size))) zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region 0sz)) zf_b;
  assert_norm (
    (A.varray (A.split_r slab_region (US.mul 0sz slab_size))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region 0sz)
      `vrefine` zf_b) `star`
    A.varray (A.split_r md_region 0sz) ==
    (right_vprop slab_region md_bm_region md_region 0sz));
  change_equal_slprop
    ((A.varray (A.split_r slab_region (US.mul 0sz slab_size))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region 0sz)
      `vrefine` zf_b) `star`
    A.varray (A.split_r md_region 0sz))
    (right_vprop slab_region md_bm_region md_region 0sz)

#restart-solver

let vrefinedep_ext
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f f': ( (t_of (vrefine v p)) -> Tot vprop))
  : Lemma (requires f == f') (ensures vrefinedep v p f == vrefinedep v p f')
  = ()

#restart-solver

let init_idxs (r_idxs: array US.t{A.length r_idxs == 7})
  : Steel unit
  (A.varray r_idxs) (fun _ -> A.varray r_idxs)
  (requires fun _ -> True)
  (ensures fun _ _ h1 ->
    let s
      : Seq.lseq US.t 7
      = A.asel r_idxs h1 in
    Seq.index s 0 == AL.null_ptr /\
    Seq.index s 1 == AL.null_ptr /\
    Seq.index s 2 == AL.null_ptr /\
    Seq.index s 3 == AL.null_ptr /\
    Seq.index s 4 == AL.null_ptr /\
    Seq.index s 5 == AL.null_ptr /\
    Seq.index s 6 == 0sz
  )
  =
  A.upd r_idxs 0sz AL.null_ptr;
  A.upd r_idxs 1sz AL.null_ptr;
  A.upd r_idxs 2sz AL.null_ptr;
  A.upd r_idxs 3sz AL.null_ptr;
  A.upd r_idxs 4sz AL.null_ptr;
  A.upd r_idxs 5sz AL.null_ptr;
  A.upd r_idxs 6sz 0sz

#push-options "--z3rlimit 300 --compat_pre_typed_indexed_effects --fuel 0 --ifuel 0"
noextract inline_for_extraction
let init_struct_aux
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region == U32.v page_size * US.v metadata_max})
  (md_bm_region: array U64.t{A.length md_bm_region == US.v 4sz * US.v metadata_max})
  (md_region: array AL.cell{A.length md_region == US.v metadata_max})
  : Steel size_class_struct_sc
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop_sc scs)
  (requires fun h0 ->
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0)
  )
  (ensures fun _ r h1 ->
    r.size == Sc sc /\
    //zf_u8 (A.asel (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) (US.sub n 1sz))) h1) /\
    //zf_u64 (A.asel (A.split_l md_bm_region (US.mul (US.mul metadata_max 4sz) (US.sub n 1sz))) h1) /\
    r.slab_region == slab_region /\
    r.md_bm_region == md_bm_region /\
    r.md_region == md_region /\
    True
  )
  =
  let open SlabsCommon in
  let s1 = gget (A.varray slab_region) in
  let s2 = gget (A.varray md_bm_region) in
  zf_u8_split s1 0;
  zf_u64_split s2 0;
  A.ghost_split slab_region 0sz;
  A.ghost_split md_bm_region 0sz;
  A.ghost_split md_region 0sz;

  drop (A.varray (A.split_l md_bm_region 0sz));
  drop (A.varray (A.split_l slab_region 0sz));

  intro_right_vprop_empty slab_region md_bm_region md_region;

  let r_idxs = mmap_array_us_init 7sz in
  init_idxs r_idxs;
  let idxs
    : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  intro_left_vprop_empty sc
    slab_region md_bm_region md_region r_idxs;

  let md_count = mmap_ptr_us_init () in
  R.write md_count 0sz;

  intro_vrefinedep
    (R.vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux sc
      slab_region md_bm_region md_region
      r_idxs)
    (left_vprop sc slab_region md_bm_region md_region
      r_idxs 0sz `star`
     right_vprop slab_region md_bm_region md_region 0sz);

  [@inline_let]
  let scs = {
    size = Sc sc;
    is_extended = false;
    slabs_idxs = r_idxs;
    md_count = md_count;
    slab_region = slab_region;
    md_bm_region = md_bm_region;
    md_bm_region_b = A.null #bool;
    md_region = md_region;
  } in

  change_slprop_rel
    (vrefinedep
      (R.vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux sc
        slab_region md_bm_region md_region r_idxs)
    )
    (size_class_vprop_sc scs)
    (fun _ _ -> True)
    (fun _ ->
      let open FStar.Tactics in
      assert (
        size_class_vprop_sc scs
        ==
        vrefinedep
          (R.vptr scs.md_count)
          vrefinedep_prop
          (size_class_vprop_aux (get_sc scs.size)
            scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
      ) by (norm [delta_only [`%size_class_vprop]]; trefl ())
    );
  return scs

#restart-solver

noextract inline_for_extraction
let init_struct_aux2
  (sc:sc_ex)
  (slab_region: array U8.t{A.length slab_region == US.v slab_size * US.v metadata_max_ex})
  (md_bm_region: array bool{A.length md_bm_region == US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region == US.v metadata_max_ex})
  : Steel size_class_struct_sc_ex
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop_sc_ex scs)
  (requires fun h0 ->
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_b (A.asel md_bm_region h0)
  )
  (ensures fun _ r h1 ->
    r.size == Sc_ex sc /\
    //zf_u8 (A.asel (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) (US.sub n 1sz))) h1) /\
    //zf_u64 (A.asel (A.split_l md_bm_region (US.mul (US.mul metadata_max 4sz) (US.sub n 1sz))) h1) /\
    r.slab_region == slab_region /\
    r.md_bm_region_b == md_bm_region /\
    r.md_region == md_region /\
    True
  )
  =
  let open SlabsCommon2 in
  let s1 = gget (A.varray slab_region) in
  let s2 = gget (A.varray md_bm_region) in
  zf_u8_split s1 0;
  zf_b_split s2 0;
  A.ghost_split slab_region 0sz;
  A.ghost_split md_bm_region 0sz;
  A.ghost_split md_region 0sz;

  drop (A.varray (A.split_l md_bm_region 0sz));
  drop (A.varray (A.split_l slab_region 0sz));

  intro_right_vprop_empty2 slab_region md_bm_region md_region;

  let r_idxs = mmap_array_us_init 7sz in
  init_idxs r_idxs;
  let idxs
    : G.erased (Seq.lseq US.t 7)
    = gget (A.varray r_idxs) in
  intro_left_vprop_empty2 sc
    slab_region md_bm_region md_region r_idxs;

  let md_count = mmap_ptr_us_init () in
  R.write md_count 0sz;

  intro_vrefinedep
    (R.vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux sc
      slab_region md_bm_region md_region
      r_idxs)
    (left_vprop sc slab_region md_bm_region md_region
      r_idxs 0sz `star`
     right_vprop slab_region md_bm_region md_region 0sz);

  [@inline_let]
  let scs = {
    size = Sc_ex sc;
    is_extended = true;
    slabs_idxs = r_idxs;
    md_count = md_count;
    slab_region = slab_region;
    md_bm_region = A.null #U64.t;
    md_bm_region_b = md_bm_region;
    md_region = md_region;
  } in

  change_slprop_rel
    (vrefinedep
      (R.vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux sc
        slab_region md_bm_region md_region r_idxs)
    )
    (size_class_vprop_sc_ex scs)
    (fun _ _ -> True)
    (fun _ ->
      let open FStar.Tactics in
      assert (
        size_class_vprop_sc_ex scs
        ==
        vrefinedep
          (R.vptr scs.md_count)
          vrefinedep_prop
          (size_class_vprop_aux (get_sc_ex scs.size)
            scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
      ) by (norm [delta_only [`%size_class_vprop]]; trefl ())
    );
  return scs

#restart-solver

open MiscArith
#push-options "--z3rlimit 100"
noextract inline_for_extraction
let init_struct
  //(n: US.t{
  //  US.v n > 0 /\
  //  US.fits (US.v metadata_max * US.v n) /\
  //  US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
  //  US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
  //  US.v metadata_max * US.v (u32_to_sz page_size) <= US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
  //  US.v metadata_max * US.v 4sz <= US.v metadata_max * US.v 4sz * US.v n /\
  //  US.v metadata_max <= US.v metadata_max * US.v n
  //})
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region >= U32.v page_size * US.v metadata_max})
  (md_bm_region: array U64.t{A.length md_bm_region >= US.v 4sz * US.v metadata_max})
  (md_region: array AL.cell{A.length md_region >= US.v metadata_max})
  : Steel size_class_struct_sc
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop_sc scs `star`
    A.varray (A.split_r slab_region (US.mul metadata_max (u32_to_sz page_size))) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max 4sz)) `star`
    A.varray (A.split_r md_region metadata_max)
  )
  (requires fun h0 ->
    US.fits (US.v metadata_max) /\
    US.fits (US.v metadata_max * US.v 4sz) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size)) /\
    US.fits (US.v metadata_max_ex * US.v slab_size) /\
  //  US.v n > 0 /\
  //  US.fits (US.v metadata_max * US.v n) /\
  //  US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
  //  US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
  //  US.v metadata_max * US.v (u32_to_sz page_size) <= US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
  //  US.v metadata_max * US.v 4sz <= US.v metadata_max * US.v 4sz * US.v n /\
  //  US.v metadata_max <= US.v metadata_max * US.v n
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    //array_u8_alignment slab_region sc_slab_region_size /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0)
  )
  (ensures fun _ r h1 ->
    r.size == Sc sc /\
    array_u8_alignment (A.split_r slab_region (US.mul metadata_max (u32_to_sz page_size))) (u32_to_sz page_size) /\
    //array_u8_alignment (A.split_r slab_region (US.mul metadata_max (u32_to_sz page_size))) sc_slab_region_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul metadata_max (u32_to_sz page_size))) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul metadata_max 4sz)) h1) /\
    A.ptr_of r.slab_region == A.ptr_of slab_region /\
    A.offset (A.ptr_of r.slab_region) == A.offset (A.ptr_of slab_region) /\
    same_base_array r.slab_region slab_region /\
    same_base_array r.md_bm_region md_bm_region /\
    same_base_array r.md_region md_region /\
    True
  )
  =
  intro_fits_u32 ();
  let s1 = gget (A.varray slab_region) in
  let s2 = gget (A.varray md_bm_region) in
  zf_u8_split s1 (US.v (US.mul metadata_max (u32_to_sz page_size)));
  zf_u64_split s2 (US.v (US.mul metadata_max 4sz));
  A.ghost_split slab_region (US.mul metadata_max (u32_to_sz page_size));
  A.ghost_split md_bm_region (US.mul metadata_max 4sz);
  A.ghost_split md_region metadata_max;
  let slab_region' = A.split_l slab_region (US.mul metadata_max (u32_to_sz page_size)) in
  let md_bm_region' = A.split_l md_bm_region (US.mul metadata_max 4sz) in
  let md_region' = A.split_l md_region metadata_max in
  change_equal_slprop
    (A.varray (A.split_l slab_region (US.mul metadata_max (u32_to_sz page_size))))
    (A.varray slab_region');
  change_equal_slprop
    (A.varray (A.split_l md_bm_region (US.mul metadata_max 4sz)))
    (A.varray md_bm_region');
  change_equal_slprop
    (A.varray (A.split_l md_region metadata_max))
    (A.varray md_region');
  assert (A.length slab_region' == US.v metadata_max * U32.v page_size);
  assert (A.length md_bm_region' == US.v metadata_max * US.v 4sz);
  assert (A.length md_region' == US.v metadata_max);
  assert (US.v (US.mul metadata_max (u32_to_sz page_size))
  == US.v metadata_max * U32.v page_size
  );
  lemma_mod_mul2 (US.v metadata_max) (U32.v page_size) 16;
  assert (US.v (US.mul metadata_max (u32_to_sz page_size)) % 16 == 0);
  array_u8_alignment_lemma slab_region slab_region' (u32_to_sz  page_size) (u32_to_sz page_size);
  array_u8_alignment_lemma slab_region
    (A.split_r slab_region (US.mul metadata_max (u32_to_sz page_size)))
    (u32_to_sz page_size) (u32_to_sz page_size);
  assert (array_u8_alignment slab_region' (u32_to_sz page_size));
  let scs = init_struct_aux sc slab_region' md_bm_region' md_region' in
  return scs

noextract inline_for_extraction
let init_struct2
  (sc:sc_ex)
  (slab_region: array U8.t{A.length slab_region >= US.v slab_size * US.v metadata_max_ex})
  (md_bm_region: array bool{A.length md_bm_region >= US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region >= US.v metadata_max_ex})
  : Steel size_class_struct_sc_ex
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop_sc_ex scs `star`
    A.varray (A.split_r slab_region (US.mul metadata_max_ex slab_size)) `star`
    A.varray (A.split_r md_bm_region metadata_max_ex) `star`
    A.varray (A.split_r md_region metadata_max_ex)
  )
  (requires fun h0 ->
    US.fits (US.v metadata_max) /\
    US.fits (US.v metadata_max * US.v 4sz) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size)) /\
    US.fits (US.v metadata_max_ex * US.v slab_size) /\
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_b (A.asel md_bm_region h0)
  )
  (ensures fun _ r h1 ->
    r.size == Sc_ex sc /\
    //array_u8_alignment (A.split_r slab_region (US.mul metadata_max (u32_to_sz page_size))) page_size /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul metadata_max_ex slab_size)) h1) /\
    zf_b (A.asel (A.split_r md_bm_region metadata_max_ex) h1) /\
    A.ptr_of r.slab_region == A.ptr_of slab_region /\
    A.offset (A.ptr_of r.slab_region) == A.offset (A.ptr_of slab_region) /\
    same_base_array r.slab_region slab_region /\
    same_base_array r.md_bm_region_b md_bm_region /\
    same_base_array r.md_region md_region /\
    True
  )
  =
  intro_fits_u32 ();
  let s1 = gget (A.varray slab_region) in
  let s2 = gget (A.varray md_bm_region) in
  zf_u8_split s1 (US.v (US.mul metadata_max_ex slab_size));
  zf_b_split s2 (US.v metadata_max_ex);
  A.ghost_split slab_region (US.mul metadata_max_ex slab_size);
  A.ghost_split md_bm_region metadata_max_ex;
  A.ghost_split md_region metadata_max_ex;
  let slab_region' = A.split_l slab_region (US.mul metadata_max_ex slab_size) in
  let md_bm_region' = A.split_l md_bm_region metadata_max_ex in
  let md_region' = A.split_l md_region metadata_max_ex in
  change_equal_slprop
    (A.varray (A.split_l slab_region (US.mul metadata_max_ex slab_size)))
    (A.varray slab_region');
  change_equal_slprop
    (A.varray (A.split_l md_bm_region metadata_max_ex))
    (A.varray md_bm_region');
  change_equal_slprop
    (A.varray (A.split_l md_region metadata_max_ex))
    (A.varray md_region');
  assert (A.length slab_region' == US.v metadata_max_ex * US.v slab_size);
  assert (A.length md_bm_region' == US.v metadata_max_ex);
  assert (A.length md_region' == US.v metadata_max_ex);
  assert (US.v (US.mul metadata_max_ex slab_size)
  == US.v metadata_max * U32.v page_size
  );
  lemma_mod_mul2 (US.v metadata_max) (U32.v page_size) 16;
  assert (US.v (US.mul metadata_max (u32_to_sz page_size)) % 16 == 0);
  array_u8_alignment_lemma slab_region slab_region'
    (u32_to_sz page_size) (u32_to_sz page_size);
  array_u8_alignment_lemma slab_region
    (A.split_r slab_region (US.mul metadata_max_ex slab_size))
    (u32_to_sz page_size) (u32_to_sz page_size);
  assert (array_u8_alignment slab_region' (u32_to_sz page_size));
  let scs = init_struct_aux2 sc slab_region' md_bm_region' md_region' in
  return scs

let split_r_r (#opened:_) (#a: Type)
  (k1: US.t)
  (k2: US.t)
  (arr: array a{
    US.fits (US.v k1 + US.v k2) /\
    US.v k1 + US.v k2 <= A.length arr
  })
  : SteelGhost unit opened
  (A.varray (
    A.split_r (A.split_r arr k1) k2
  ))
  (fun _ -> A.varray (
    A.split_r arr (US.add k1 k2)
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.split_r (A.split_r arr k1) k2
    ==
    A.split_r arr (US.add k1 k2) /\
    A.asel (A.split_r (A.split_r arr k1) k2) h0
    ==
    A.asel (A.split_r arr (US.add k1 k2)) h1
  )
  =
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_r (A.split_r arr k1) k2))
    (A.ptr_of (A.split_r arr (US.add k1 k2)));
  change_equal_slprop
    (A.varray (A.split_r (A.split_r arr k1) k2))
    (A.varray (A.split_r arr (US.add k1 k2)))

let split_r_r_mul (#opened:_) (#a: Type)
  (n: US.t)
  (k1: US.t)
  (k2: US.t{US.v k2 == US.v k1 + 1})
  (arr: array a{
    US.fits (US.v n * US.v k2) /\
    US.v n * US.v k2 <= A.length arr
  })
  : SteelGhost unit opened
  (A.varray (
    A.split_r (A.split_r arr (US.mul n k1)) n
  ))
  (fun _ -> A.varray (
    A.split_r arr (US.mul n k2)
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.split_r (A.split_r arr (US.mul n k1)) n
    ==
    A.split_r arr (US.mul n k2) /\
    A.asel (A.split_r (A.split_r arr (US.mul n k1)) n) h0
    ==
    A.asel (A.split_r arr (US.mul n k2)) h1
  )
  =
  split_r_r (US.mul n k1) n arr;
  change_equal_slprop
    (A.varray (split_r arr (US.add (US.mul n k1) n)))
    (A.varray (split_r arr (US.mul n k2)))

let _ = ()

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50 --split_queries no"

//#push-options "--z3smtopt '(set-option :smt.arith.nl false)'"

module FML = FStar.Math.Lemmas

let _ : squash (US.fits_u64) = intro_fits_u64 ()

let f_lemma
  (n: US.t{
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (k: US.t{US.v k <= US.v n})
  : Lemma
  (
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v k) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v k) /\
    US.fits (US.v metadata_max * US.v k) /\
    US.v metadata_max * US.v (u32_to_sz page_size) * US.v k <= US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    US.v metadata_max * US.v 4sz * US.v k <= US.v metadata_max * US.v 4sz * US.v n /\
    US.v metadata_max * US.v k <= US.v metadata_max * US.v n /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size)) /\
    US.fits (US.v metadata_max * US.v 4sz) /\
    True
  )
  =
  FML.lemma_mult_le_right (US.v metadata_max * US.v (u32_to_sz page_size)) (US.v k) (US.v n);
  FML.lemma_mult_le_right (US.v metadata_max * US.v 4sz) (US.v k) (US.v n);
  FML.lemma_mult_le_right (US.v metadata_max) (US.v k) (US.v n)


#restart-solver

unfold
let size_class_pred (slab_region:array U8.t) (sc:size_class) (i:nat) : prop =
  same_base_array slab_region sc.data.slab_region /\
  A.offset (A.ptr_of sc.data.slab_region) == A.offset (A.ptr_of slab_region) + US.v sc_slab_region_size * i

noextract inline_for_extraction
val init_wrapper
  (sc: sc)
  (n: US.t{
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (k: US.t{US.v k <= US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k'
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n /\
    A.length md_region >= US.v metadata_max * US.v k /\
    A.length md_region >= US.v metadata_max * US.v k'
  })
  : Steel size_class
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k))
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k'))
  )
  (requires fun h0 ->
    US.v k < US.v n /\
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    True
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) h1) /\
    r.data.size == Sc sc /\
    size_class_pred slab_region r (US.v k)
    //same_base_array slab_region r.data.slab_region /\
    //A.offset (A.ptr_of r.data.slab_region) == A.offset (A.ptr_of slab_region) + US.v metadata_max * US.v (u32_to_sz page_size) * US.v k
  )

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let init_wrapper sc n k k' slab_region md_bm_region md_region
  =
  f_lemma n k;
  f_lemma n k';
  //f_lemma n (US.sub n k);
  //admit ();
  let data = init_struct sc
    (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k))
    (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k))
    (A.split_r md_region (US.mul metadata_max k))
  in
  split_r_r_mul
    (US.mul metadata_max (u32_to_sz page_size))
    k
    k'
    slab_region;
  split_r_r_mul
    (US.mul metadata_max 4sz)
    k
    k'
    md_bm_region;
  split_r_r_mul
    metadata_max
    k
    k'
    md_region;
  assume (A.offset (A.ptr_of data.slab_region) == A.offset (A.ptr_of slab_region) + US.v metadata_max * US.v (u32_to_sz page_size) * US.v k);
  change_slprop_rel
    (size_class_vprop_sc data)
    (size_class_vprop data)
    (fun x y -> x == y)
    (fun _ -> admit ());
  let lock = L.new_lock (size_class_vprop data) in
  let sc = {data; lock} in
  return sc
#pop-options

let f_lemma2
  (n: US.t{
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v n) /\
    US.fits (US.v metadata_max_ex * US.v n)
  })
  (k: US.t{US.v k <= US.v n})
  : Lemma
  (
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v k) /\
    US.fits (US.v metadata_max_ex * US.v k) /\
    US.v metadata_max_ex * US.v slab_size * US.v k <= US.v metadata_max_ex * US.v slab_size * US.v n /\
    US.v metadata_max_ex * US.v k <= US.v metadata_max_ex * US.v n /\
    US.fits (US.v metadata_max_ex * US.v slab_size) /\
    True
  )
  =
  FML.lemma_mult_le_right (US.v metadata_max_ex * US.v slab_size) (US.v k) (US.v n);
  FML.lemma_mult_le_right (US.v metadata_max_ex) (US.v k) (US.v n)

noextract inline_for_extraction
val init_wrapper2
  (sc: sc_ex)
  (n: US.t{
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v n) /\
    US.fits (US.v metadata_max_ex * US.v n)
  })
  (k: US.t{US.v k <= US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max_ex * US.v slab_size * US.v n /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * US.v k /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * US.v k'
  })
  (md_bm_region: array bool{
    A.length md_bm_region == US.v metadata_max_ex * US.v n /\
    A.length md_bm_region >= US.v metadata_max_ex * US.v k /\
    A.length md_bm_region >= US.v metadata_max_ex * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max_ex * US.v n /\
    A.length md_region >= US.v metadata_max_ex * US.v k /\
    A.length md_region >= US.v metadata_max_ex * US.v k'
  })
  : Steel size_class
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex k))
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k')) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex k')) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex k'))
  )
  (requires fun h0 ->
    US.v k < US.v n /\
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex k)) h0) /\
    True
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k')) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k')) h1) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex k')) h1) /\
    r.data.size == Sc_ex sc /\
    size_class_pred slab_region r (US.v k)
    //same_base_array slab_region r.data.slab_region /\
    //A.offset (A.ptr_of r.data.slab_region) == A.offset (A.ptr_of slab_region) + US.v metadata_max * US.v (u32_to_sz page_size) * US.v k
  )

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let init_wrapper2 sc n k k' slab_region md_bm_region md_region
  =
  f_lemma2 n k;
  f_lemma2 n k';
  //f_lemma n (US.sub n k);
  //admit ();
  let data = init_struct2 sc
    (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k))
    (A.split_r md_bm_region (US.mul metadata_max_ex k))
    (A.split_r md_region (US.mul metadata_max_ex k))
  in
  split_r_r_mul
    (US.mul metadata_max_ex slab_size)
    k
    k'
    slab_region;
  split_r_r_mul
    metadata_max_ex
    k
    k'
    md_bm_region;
  split_r_r_mul
    metadata_max_ex
    k
    k'
    md_region;
  assume (A.offset (A.ptr_of data.slab_region) == A.offset (A.ptr_of slab_region) + US.v metadata_max * US.v (u32_to_sz page_size) * US.v k);
  assume (array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k')) (u32_to_sz page_size));
  //assert (A.offset (A.ptr_of data.slab_region) == A.offset (A.ptr_of slab_region) + US.v metadata_max * US.v (u32_to_sz page_size) * US.v k);
  change_slprop_rel
    (size_class_vprop_sc_ex data)
    (size_class_vprop data)
    (fun x y -> x == y)
    (fun _ -> admit ());
  let lock = L.new_lock (size_class_vprop data) in
  let sc = {data; lock} in
  return sc
#pop-options

module G = FStar.Ghost
module UP = FStar.PtrdiffT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let slab_region_size
  : v:US.t{
    US.v v == US.v metadata_max * U32.v page_size * US.v nb_size_classes * US.v nb_arenas /\
    UP.fits (US.v v)
  }
  =
  metadata_max_up_fits ();
  sc_slab_region_size `US.mul` nb_size_classes `US.mul` nb_arenas
#pop-options

//[@"opaque_to_smt"]
#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
/// A logical predicate indicating that a list of sizes corresponds
/// to the sizes of a list of size_classes
let synced_sizes
  //(nb_arenas: US.t)
  //(n: US.t)
  (offset: US.t)
  (size_classes: Seq.seq size_class)
  (sizes:TLA.t sc_union)
  (k:nat{
    k <= Seq.length size_classes /\
    k + US.v offset <= TLA.length sizes
  })
  : prop
  =
  forall (i:US.t{US.v i < k}). (
    US.fits (US.v offset + US.v i) /\
    TLA.get sizes (US.add offset i)
    == (Seq.index size_classes (US.v i)).data.size
  )

#restart-solver

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
/// Performs the initialization of one size class of length [size_c], and stores it in the
/// size_classes array at index [k]
val init_size_class
  (offset: US.t)
  //(size_c: sc)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (k: US.t{US.v k < US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k'
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n /\
    A.length md_region >= US.v metadata_max * US.v k /\
    A.length md_region >= US.v metadata_max * US.v k'
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k')) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    TLA.length sizes > US.v offset + US.v k /\
    synced_sizes offset (asel size_classes h0) sizes (US.v k) /\

    //(forall (i:nat{i < US.v n}) . Sc? (Seq.index (asel size_classes h0) i).data.size) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i) /\
    True
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) h1) /\
    TLA.length sizes >= US.v offset + US.v k' /\
    synced_sizes offset (asel size_classes h1) sizes (US.v k') /\
    //(forall (i:nat{i < US.v n}) . Sc? (Seq.index (asel size_classes h1) i).data.size) /\
    (forall (i:nat{i <= US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i) /\
    True
  )

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let init_size_class
  offset n k k' slab_region md_bm_region md_region size_classes sizes
  =
  assume (US.fits (US.v offset + US.v k));
  let idx = US.add offset k in
  let size = TLA.get sizes idx in
  (**) let g0 = gget (varray size_classes) in
  //assume (size == (Seq.index g0 (US.v k)).data.size);
  assume (Sc? size);
  //by (let open FStar.Tactics in
  //    set_fuel 1; set_ifuel 1; set_rlimit 100;
  //    ());
  let Sc size = size in
  //(**) let g_sizes0 = gget (varray sizes) in
  f_lemma n k;
  //upd sizes k size;
  let sc = init_wrapper size n k k' slab_region md_bm_region md_region in
  upd size_classes k sc;

  (**) let g1 = gget (varray size_classes) in
  //(**) let g_sizes1 = gget (varray sizes) in
  //(**) assert (Ghost.reveal g_sizes1 == Seq.upd (Ghost.reveal g_sizes0) (US.v k) size);
  (**) assert (Ghost.reveal g1 == Seq.upd (Ghost.reveal g0) (US.v k) sc)
#pop-options

/// Performs the initialization of one size class of length [size_c], and stores it in the
/// size_classes array at index [k]
val init_size_class2
  (offset: US.t)
  //(size_c: sc)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v n) /\
    US.fits (US.v metadata_max_ex * US.v n)
  })
  (k: US.t{US.v k < US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max_ex * US.v slab_size * US.v n /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * US.v k /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * US.v k'
  })
  (md_bm_region: array bool{
    A.length md_bm_region == US.v metadata_max_ex * US.v n /\
    A.length md_bm_region >= US.v metadata_max_ex * US.v k /\
    A.length md_bm_region >= US.v metadata_max_ex * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max_ex * US.v n /\
    A.length md_region >= US.v metadata_max_ex * US.v k /\
    A.length md_region >= US.v metadata_max_ex * US.v k'
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex k)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k')) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex k')) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex k')) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex k)) h0) /\
    TLA.length sizes > US.v offset + US.v k /\
    synced_sizes offset (asel size_classes h0) sizes (US.v k) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i) /\
    True
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k')) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k')) h1) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex k')) h1) /\
    TLA.length sizes >= US.v offset + US.v k' /\
    synced_sizes offset (asel size_classes h1) sizes (US.v k') /\
    (forall (i:nat{i <= US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i) /\
    True
  )

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let init_size_class2
  offset n k k' slab_region md_bm_region md_region size_classes sizes
  =
  assume (US.fits (US.v offset + US.v k));
  let idx = US.add offset k in
  let size = TLA.get sizes idx in
  assume (Sc_ex? size);
  let Sc_ex size = size in
  (**) let g0 = gget (varray size_classes) in
  //(**) let g_sizes0 = gget (varray sizes) in
  f_lemma2 n k;
  //upd sizes k size;
  let sc = init_wrapper2 size n k k' slab_region md_bm_region md_region in
  upd size_classes k sc;

  (**) let g1 = gget (varray size_classes) in
  //(**) let g_sizes1 = gget (varray sizes) in
  //(**) assert (Ghost.reveal g_sizes1 == Seq.upd (Ghost.reveal g_sizes0) (US.v k) size);
  (**) assert (Ghost.reveal g1 == Seq.upd (Ghost.reveal g0) (US.v k) sc)
#pop-options

/// An attribute, that will indicate that the annotated functions should be unfolded at compile-time
irreducible let reduce_attr : unit = ()

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
val init_size_classes_aux (l:list sc)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (k: US.t{US.v k < US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * US.v k'
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n /\
    A.length md_region >= US.v metadata_max * US.v k /\
    A.length md_region >= US.v metadata_max * US.v k'
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max n)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    US.v k + List.length l == US.v n /\
    Cons? l /\

    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h0) sizes (US.v k) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i) /\
    True
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h1) sizes (US.v n) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i) /\
    True
  )
#pop-options

#restart-solver

open MiscArith

#restart-solver

// We need to bump the fuel to reason about the length of the lists
#push-options "--z3rlimit 300 --fuel 2 --ifuel 1 --query_stats"
let rec init_size_classes_aux l offset n k k' slab_region md_bm_region md_region size_classes sizes
  = match l with
  | [hd] ->
      assert (US.v k' == US.v n);
      init_size_class offset n k k' slab_region md_bm_region md_region size_classes sizes;
      // Need to rewrite the k' into n to satisfy the postcondition
      change_equal_slprop (A.varray (split_r md_bm_region _)) (A.varray (split_r md_bm_region _));
      change_equal_slprop (A.varray (split_r md_region _)) (A.varray (split_r md_region _));
      change_equal_slprop (A.varray (split_r slab_region _)) (A.varray (split_r slab_region _))
  | hd::tl ->
      init_size_class offset n k k' slab_region md_bm_region md_region size_classes sizes;
      // This proof obligation in the recursive call seems especially problematic.
      // The call to the lemma alleviates the issue, we might need something similar for
      // the md_region and md_bm_region in the future
      assert (US.v (k' `US.add` 1sz) <= US.v n);
      f_lemma n (k' `US.add` 1sz);

      init_size_classes_aux tl offset n k' (k' `US.add` 1sz) slab_region md_bm_region md_region size_classes sizes
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
val init_size_classes_aux2 (l:list sc_ex)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v n) /\
    US.fits (US.v metadata_max_ex * US.v n)
  })
  (k: US.t{US.v k < US.v n})
  (k': US.t{US.v k' <= US.v n})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max_ex * US.v slab_size * US.v n /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * US.v k /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * US.v k'
  })
  (md_bm_region: array bool{
    A.length md_bm_region == US.v metadata_max_ex * US.v n /\
    A.length md_bm_region >= US.v metadata_max_ex * US.v k /\
    A.length md_bm_region >= US.v metadata_max_ex * US.v k'
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max_ex * US.v n /\
    A.length md_region >= US.v metadata_max_ex * US.v k /\
    A.length md_region >= US.v metadata_max_ex * US.v k'
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex k)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex n)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    US.v k + List.length l == US.v n /\
    Cons? l /\

    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) k)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex k)) h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h0) sizes (US.v k) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i) /\
    True
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) h1) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h1) sizes (US.v n) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i) /\
    True
  )

#push-options "--z3rlimit 300 --fuel 2 --ifuel 1 --query_stats"
let rec init_size_classes_aux2 l offset n k k' slab_region md_bm_region md_region size_classes sizes
  = match l with
  | [hd] ->
      assert (US.v k' == US.v n);
      init_size_class2 offset n k k' slab_region md_bm_region md_region size_classes sizes;
      // Need to rewrite the k' into n to satisfy the postcondition
      change_equal_slprop (A.varray (split_r md_bm_region _)) (A.varray (split_r md_bm_region _));
      change_equal_slprop (A.varray (split_r md_region _)) (A.varray (split_r md_region _));
      change_equal_slprop (A.varray (split_r slab_region _)) (A.varray (split_r slab_region _))
  | hd::tl ->
      init_size_class2 offset n k k' slab_region md_bm_region md_region size_classes sizes;
      // This proof obligation in the recursive call seems especially problematic.
      // The call to the lemma alleviates the issue, we might need something similar for
      // the md_region and md_bm_region in the future
      assert (US.v (k' `US.add` 1sz) <= US.v n);
      f_lemma2 n (k' `US.add` 1sz);

      init_size_classes_aux2 tl offset n k' (k' `US.add` 1sz) slab_region md_bm_region md_region size_classes sizes
#pop-options

/// The normalization steps for reduction at compile-time
unfold
let normal_steps = [
      delta_attr [`%reduce_attr];
      delta_only [`%List.append];
      iota; zeta; primops]

unfold
let normal (#a:Type) (x:a) =
  Pervasives.norm normal_steps x

#push-options "--fuel 0 --ifuel 0"
/// Entrypoint, allocating all size classes according to the list of sizes [l]
inline_for_extraction noextract
val init_size_classes (l:list sc)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * 0 /\
    A.length slab_region >= US.v metadata_max * US.v (u32_to_sz page_size) * 1
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * 0 /\
    A.length md_bm_region >= US.v metadata_max * US.v 4sz * 1
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n /\
    A.length md_region >= US.v metadata_max * 0 /\
    A.length md_region >= US.v metadata_max * 1
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max 0sz)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max n)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    //(forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i) /\
    //synced_sizes offset (asel size_classes h0) sizes 0 /\
    True
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h1) sizes (US.v n) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i) /\
    True
  )

#push-options "--fuel 1 --ifuel 1"
let init_size_classes l offset n slab_region md_bm_region md_region size_classes sizes =
  (normal (init_size_classes_aux l offset n 0sz 1sz)) slab_region md_bm_region md_region size_classes sizes
#pop-options

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
/// Entrypoint, allocating all size classes according to the list of sizes [l]
inline_for_extraction noextract
val init_size_classes2 (l:list sc_ex)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v n) /\
    US.fits (US.v metadata_max_ex * US.v n)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max_ex * US.v slab_size * US.v n /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * 0 /\
    A.length slab_region >= US.v metadata_max_ex * US.v slab_size * 1
  })
  (md_bm_region: array bool{
    A.length md_bm_region == US.v metadata_max_ex * US.v n /\
    A.length md_bm_region >= US.v metadata_max_ex * 0 /\
    A.length md_bm_region >= US.v metadata_max_ex * 1
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max_ex * US.v n /\
    A.length md_region >= US.v metadata_max_ex * 0 /\
    A.length md_region >= US.v metadata_max_ex * 1
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  ///\ TLA.length sizes >= US.v offset /\ TLA.length sizes >= A.length size_classes})
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex 0sz)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex 0sz)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex n)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) 0sz)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) 0sz)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex 0sz)) h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h0) sizes 0 /\
    True
    //(forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) h1) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h1) sizes (US.v n) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i) /\
    True
  )

#restart-solver

#push-options "--fuel 1 --ifuel 1"
let init_size_classes2 l offset n slab_region md_bm_region md_region size_classes sizes =
  (normal (init_size_classes_aux2 l offset n 0sz 1sz)) slab_region md_bm_region md_region size_classes sizes
#pop-options

val init_all_size_classes1 (l:list sc)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max 0sz)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    //synced_sizes offset (asel size_classes h0) sizes 0 /\
    True
  )
  (ensures fun _ r h1 ->
    //array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) (u32_to_sz page_size) /\
    //zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    //zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h1) sizes (US.v n) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i) /\
    True
  )

#push-options "--fuel 1 --ifuel 1"
let init_all_size_classes1
  l offset n slab_region md_bm_region md_region size_classes sizes
  =
  f_lemma n 0sz;
  f_lemma n 1sz;
  init_size_classes l offset n slab_region md_bm_region md_region size_classes sizes;
  drop (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)));
  drop (A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)));
  drop (A.varray (A.split_r md_region (US.mul metadata_max n)))
#pop-options

val init_all_size_classes2 (l:list sc_ex)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v n) /\
    US.fits (US.v metadata_max_ex * US.v n)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max_ex * US.v slab_size * US.v n
  })
  (md_bm_region: array bool{
    A.length md_bm_region == US.v metadata_max_ex * US.v n
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max_ex * US.v n
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  ///\ TLA.length sizes >= US.v offset /\ TLA.length sizes >= A.length size_classes})
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max_ex 0sz)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max_ex 0sz)) `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) 0sz)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) 0sz)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex 0sz)) h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    True
    //(forall (i:nat{i < US.v offset}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    //array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) (u32_to_sz page_size) /\
    //zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) h1) /\
    //zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes offset (asel size_classes h1) sizes (US.v n) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

#push-options "--fuel 1 --ifuel 1"
let init_all_size_classes2
  l offset n slab_region md_bm_region md_region size_classes sizes
  =
  f_lemma2 n 0sz;
  f_lemma2 n 1sz;
  init_size_classes2 l offset n slab_region md_bm_region md_region size_classes sizes;
  drop (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)));
  drop (A.varray (A.split_r md_bm_region (US.mul metadata_max_ex n)));
  drop (A.varray (A.split_r md_region (US.mul metadata_max_ex n)))
#pop-options

[@"opaque_to_smt"]
let synced_sizes2
  (offset: US.t)
  (size_classes:Seq.seq size_class)
  (sizes:TLA.t sc_union)
  (k:nat{
    k <= Seq.length size_classes /\
    k + US.v offset <= TLA.length sizes
  })
  : prop
  =
  synced_sizes offset size_classes sizes k

[@"opaque_to_smt"]
let size_class_preds
  (size_classes:Seq.seq size_class)
  (k:nat{k <= Seq.length size_classes})
  (slab_region: array U8.t{A.length slab_region >= US.v sc_slab_region_size * k})
  : prop
  =
  forall (i:nat{i < k}). (
    size_class_pred slab_region (Seq.index size_classes i) i
  )

val init_all_size_classes_wrapper1 (l:list sc)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    //synced_sizes (asel size_classes h0) 0 sizes /\
    //(forall (i:nat{i < US.v n}) . Sc? (Seq.index (asel size_classes h0) i).data.size) /\
    True
    //(forall (i:nat{i < 0}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    //array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) (u32_to_sz page_size) /\
    //zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    //zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n) /\
    size_class_preds (asel size_classes h1) (US.v n) slab_region
  )

#push-options "--fuel 1 --ifuel 1"
let init_all_size_classes_wrapper1
  l offset n slab_region md_bm_region md_region size_classes sizes
  =
  Math.Lemmas.mul_zero_right_is_zero (US.v (US.mul metadata_max (u32_to_sz page_size)));
  Math.Lemmas.mul_zero_right_is_zero (US.v (US.mul metadata_max 4sz));
  Math.Lemmas.mul_zero_right_is_zero (US.v metadata_max);
  A.ptr_shift_zero (A.ptr_of slab_region);
  A.ptr_shift_zero (A.ptr_of md_bm_region);
  A.ptr_shift_zero (A.ptr_of md_region);

  change_equal_slprop
    (A.varray slab_region)
    (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)));
  change_equal_slprop
    (A.varray md_bm_region)
    (A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)));
  change_equal_slprop
    (A.varray md_region)
    (A.varray (A.split_r md_region (US.mul metadata_max 0sz)));
  init_all_size_classes1 l offset n slab_region md_bm_region md_region size_classes sizes;
  reveal_opaque (`%synced_sizes2) synced_sizes2;
  reveal_opaque (`%size_class_preds) size_class_preds
#pop-options

val init_all_size_classes_wrapper2 (l:list sc_ex)
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n) /\
    US.fits (US.v metadata_max_ex * US.v slab_size * US.v n) /\
    US.fits (US.v metadata_max_ex * US.v n)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max_ex * US.v slab_size * US.v n
  })
  (md_bm_region: array bool{
    A.length md_bm_region == US.v metadata_max_ex * US.v n
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max_ex * US.v n
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  ///\ TLA.length sizes >= US.v offset /\ TLA.length sizes >= A.length size_classes})
  //(sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region `star`
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (fun r ->
    A.varray size_classes
    //`star`
    //A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_b (A.asel md_bm_region h0) /\
    TLA.length sizes >= US.v offset + US.v n /\
    True
    //(forall (i:nat{i < US.v offset}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    //array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) (u32_to_sz page_size) /\
    //zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) n)) h1) /\
    //zf_b (A.asel (A.split_r md_bm_region (US.mul metadata_max_ex n)) h1) /\
    TLA.length sizes >= US.v offset + US.v n /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n) /\
    size_class_preds (asel size_classes h1) (US.v n) slab_region
  )

#push-options "--fuel 1 --ifuel 1"
let init_all_size_classes_wrapper2
  l offset n slab_region md_bm_region md_region size_classes sizes
  =
  Math.Lemmas.mul_zero_right_is_zero (US.v (US.mul metadata_max_ex slab_size));
  Math.Lemmas.mul_zero_right_is_zero (US.v metadata_max_ex);
  A.ptr_shift_zero (A.ptr_of slab_region);
  A.ptr_shift_zero (A.ptr_of md_bm_region);
  A.ptr_shift_zero (A.ptr_of md_region);

  change_equal_slprop
    (A.varray slab_region)
    (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max_ex slab_size) 0sz)));
  change_equal_slprop
    (A.varray md_bm_region)
    (A.varray (A.split_r md_bm_region (US.mul metadata_max_ex 0sz)));
  change_equal_slprop
    (A.varray md_region)
    (A.varray (A.split_r md_region (US.mul metadata_max_ex 0sz)));
  init_all_size_classes2 l offset n slab_region md_bm_region md_region size_classes sizes;
  reveal_opaque (`%synced_sizes2) synced_sizes2;
  reveal_opaque (`%size_class_preds) size_class_preds
#pop-options

//module TLAO = TLAOverlay

#restart-solver

val synced_sizes_join_lemma''
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v offset + US.v n)
  })
  (size_classes: Seq.lseq size_class (US.v n))
  (sizes: TLA.t sc_union)
  (n1 n2: US.t)
  (i:US.t{US.v i < US.v n})
  : Lemma
  (requires (
    US.v n1 + US.v n2 == US.v n /\
    US.v n1 > 0 /\
    US.v n2 > 0 /\
    (let scs1, scs2 = Seq.split size_classes (US.v n1) in
    TLA.length sizes >= US.v n + US.v offset /\
    synced_sizes2 offset scs1 sizes (US.v n1) /\
    synced_sizes2 (US.add offset n1) scs2 sizes (US.v n2) /\
    True
  )))
  (ensures (
    TLA.get sizes (US.add offset i)
    == (Seq.index size_classes (US.v i)).data.size
  ))

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100 --query_stats"
let synced_sizes_join_lemma''
  offset n size_classes sizes n1 n2 i
  =
  let scs1, scs2 = Seq.split size_classes (US.v n1) in
  reveal_opaque (`%synced_sizes2) synced_sizes2;
  if US.v i < US.v n1
  then (
    ()
  ) else (
    assert (US.v i - US.v n1 < US.v n2);
    assert (TLA.get sizes (US.add (US.add offset n1) (US.sub i n1))
    ==
    (Seq.index scs2 (US.v (US.sub i n1))).data.size);
    assert (TLA.get sizes (US.add (US.add offset n1) (US.sub i n1))
    == TLA.get sizes (US.add offset i));
    Seq.lemma_index_slice size_classes (US.v n1) (US.v n) (US.v i - US.v n1);
    assert (Seq.index scs2 (US.v (US.sub i n1))
    ==
    Seq.index size_classes (US.v i));
    ()
  )
#pop-options

let synced_sizes_join_lemma'
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v offset + US.v n)
  })
  (size_classes: Seq.lseq size_class (US.v n))
  (sizes: TLA.t sc_union)
  (n1 n2: US.t)
  (i:nat{i < US.v n})
  : Lemma
  (requires (
    US.v n1 + US.v n2 == US.v n /\
    US.v n1 > 0 /\
    US.v n2 > 0 /\
    (let scs1, scs2 = Seq.split size_classes (US.v n1) in
    TLA.length sizes >= US.v n + US.v offset /\
    synced_sizes2 offset scs1 sizes (US.v n1) /\
    synced_sizes2 (US.add offset n1) scs2 sizes (US.v n2) /\
    True
  )))
  (ensures
    US.fits i /\
    TLA.get sizes (US.add offset (US.uint_to_t i))
    == (Seq.index size_classes i).data.size
  )
  =
  synced_sizes_join_lemma'' offset n size_classes sizes n1 n2 (US.uint_to_t i)

let synced_sizes_join_lemma
  (offset: US.t)
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.fits (US.v offset + US.v n)
  })
  (size_classes: Seq.lseq size_class (US.v n))
  (sizes: TLA.t sc_union)
  (n1 n2: US.t)
  : Lemma
  (requires
    US.v n1 + US.v n2 == US.v n /\
    US.v n1 > 0 /\
    US.v n2 > 0 /\
    (let scs1, scs2 = Seq.split size_classes (US.v n1) in
    TLA.length sizes >= US.v n + US.v offset /\
    synced_sizes2 offset scs1 sizes (US.v n1) /\
    synced_sizes2 (US.add offset n1) scs2 sizes (US.v n2) /\
    True)
  )
  (ensures
    synced_sizes2 offset size_classes sizes (US.v n)
  )
  =
  reveal_opaque (`%synced_sizes2) synced_sizes2;
  Classical.forall_intro (Classical.move_requires (
    synced_sizes_join_lemma' offset n size_classes sizes n1 n2 
  ))

val synced_sizes_join
  (#opened: _)
  (offset: US.t)
  (n1: US.t{US.v n1 > 0})
  (n2: US.t{US.v n2 > 0})
  (n: US.t{
    UInt.size (US.v n) U32.n /\
    US.v n == US.v n1 + US.v n2 /\
    US.fits (US.v offset + US.v n)
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  // (s1: Seq.lseq size_class (US.v n1))
  // (s2: Seq.lseq size_class (US.v n2))
  : SteelGhost unit opened
  (
    A.varray (A.split_l size_classes n1) `star`
    A.varray (A.split_r size_classes n1)
  )
  (fun _ ->
    A.varray size_classes
  )
  (requires fun h0 ->
    TLA.length sizes >= US.v n + US.v offset /\
    // s1 `Seq.equal` (asel (A.split_l size_classes n1) h0) /\
    //s2 `Seq.equal` (asel (A.split_r size_classes n1) h0) /\
    synced_sizes2 offset (asel (A.split_l size_classes n1) h0) sizes (US.v n1) /\
    synced_sizes2 (US.add offset n1) (asel (A.split_r size_classes n1) h0) sizes
(US.v n2)
  )
  (ensures fun h0 _ h1 ->
    TLA.length sizes >= US.v n + US.v offset /\
    asel size_classes h1 `Seq.equal` Seq.append (asel (A.split_l size_classes n1) h0) (asel (A.split_r size_classes n1) h0) /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n)
  )

#push-options "--fuel 1 --ifuel 1"
let synced_sizes_join offset n1 n2 n size_classes sizes
  =
  let s1 = gget (A.varray (A.split_l size_classes n1)) in
  let s2 = gget (A.varray (A.split_r size_classes n1)) in
  A.ghost_join
   (A.split_l size_classes n1)
   (A.split_r size_classes n1)
   ();
  change_equal_slprop
   (A.varray (A.merge
     (A.split_l size_classes n1)
     (A.split_r size_classes n1)))
   (A.varray size_classes);
  let s = gget (A.varray size_classes) in
  let s1', s2' = Seq.split s (US.v n1) in
  Seq.lemma_append_inj s1 s2 s1' s2';
  synced_sizes_join_lemma offset n s sizes n1 n2
#pop-options

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
val slab_region_pred_join_lemma_aux'
  (n: US.t{
    US.fits (US.v sc_slab_region_size * US.v n)
  })
  (slab_region: array U8.t{A.length slab_region = US.v sc_slab_region_size * US.v n})
  (size_classes: Seq.lseq size_class (US.v n))
  (n1 n2: US.t)
  (_:unit{
    US.v n1 + US.v n2 == US.v n /\
    US.v n1 > 0 /\
    US.fits (US.v sc_slab_region_size * US.v n1) /\
    US.fits (US.v sc_slab_region_size * US.v n2) /\
    US.v n2 > 0 /\
    (let scs1, scs2 = Seq.split size_classes (US.v n1) in
    (forall (i:nat{i < US.v n1}).
      size_class_pred (A.split_l slab_region (US.mul sc_slab_region_size n1)) (Seq.index scs1 i) i
    ) /\
    A.length (A.split_r slab_region (US.mul sc_slab_region_size n1))
    == US.v sc_slab_region_size * US.v n2 /\
    (forall (i:nat{i < US.v n2}).
      size_class_pred (A.split_r slab_region (US.mul sc_slab_region_size n1)) (Seq.index scs2 i) i
    ))
  })
  (i:nat{i < US.v n})
  : Lemma
  (
    size_class_pred slab_region (Seq.index size_classes i) i
  )
#pop-options

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"
let slab_region_pred_join_lemma_aux' n slab_region size_classes n1 n2 _ i
  =
  admit ();
  let scs1, scs2 = Seq.split size_classes (US.v n1) in
  if i < US.v n1
  then (
    assert (Seq.index scs1 i == Seq.index size_classes i);
    assert (A.offset (A.ptr_of (A.split_l slab_region (US.mul sc_slab_region_size n1)))
    == A.offset (A.ptr_of slab_region))
  ) else (
    Seq.lemma_index_slice size_classes (US.v n1) (US.v n) (i - US.v n1);
    assert (Seq.index scs2 (i - US.v n1)
    == Seq.index size_classes i);
    assert (A.offset (A.ptr_of (A.split_r slab_region (US.mul  sc_slab_region_size n1)))
    == A.offset (A.ptr_of slab_region) + US.v sc_slab_region_size * US.v n1);
    assert (A.offset (A.ptr_of (A.split_r slab_region (US.mul sc_slab_region_size n1))) + US.v sc_slab_region_size * (i - US.v n1)
    ==
    A.offset (A.ptr_of slab_region) + US.v sc_slab_region_size * i)
  )
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
val slab_region_pred_join_lemma'
  (n: US.t{
    US.fits (US.v sc_slab_region_size * US.v n)
  })
  (slab_region: array U8.t{A.length slab_region == US.v sc_slab_region_size * US.v n})
  (size_classes: Seq.lseq size_class (US.v n))
  (n1 n2: US.t)
  : Lemma
  (requires
    US.v n1 + US.v n2 == US.v n /\
    US.v n1 > 0 /\
    US.v n2 > 0 /\
    US.fits (US.v sc_slab_region_size * US.v n1) /\
    US.fits (US.v sc_slab_region_size * US.v n2) /\
    (let scs1, scs2 = Seq.split size_classes (US.v n1) in
    (forall (i:nat{i < US.v n1}).
      size_class_pred (A.split_l slab_region (US.mul sc_slab_region_size n1)) (Seq.index scs1 i) i
    ) /\
    (forall (i:nat{i < US.v n2}).
      size_class_pred (A.split_r slab_region (US.mul sc_slab_region_size n1)) (Seq.index scs2 i) i
    ))
  )
  (ensures
    forall (i:nat{i < US.v n}).
      size_class_pred slab_region (Seq.index size_classes i) i
  )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let slab_region_pred_join_lemma' n slab_region size_classes n1 n2
  =
  admit ();
  Classical.forall_intro (Classical.move_requires (
    slab_region_pred_join_lemma_aux' n slab_region size_classes n1 n2 ()
  ))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
val slab_region_pred_join_lemma
  (n1 n2: US.t)
  (n: US.t{
    US.fits (US.v sc_slab_region_size * US.v n)
  })
  (slab_region: array U8.t{A.length slab_region == US.v sc_slab_region_size * US.v n})
  (size_classes: Seq.lseq size_class (US.v n))
  : Lemma
  (requires
    US.v n1 + US.v n2 == US.v n /\
    US.v n1 > 0 /\
    US.v n2 > 0 /\
    US.fits (US.v sc_slab_region_size * US.v n1) /\
    US.fits (US.v sc_slab_region_size * US.v n2) /\
    (let scs = Seq.split size_classes (US.v n1) in
      size_class_preds (fst scs) (US.v n1) (A.split_l slab_region (US.mul sc_slab_region_size n1)) /\
      size_class_preds (snd scs) (US.v n2) (A.split_r slab_region (US.mul sc_slab_region_size n1))
    )
  )
  (ensures
    size_class_preds size_classes (US.v n) slab_region
  )
#pop-options

let slab_region_pred_join_lemma n1 n2 n slab_region size_classes
  =
  reveal_opaque (`%size_class_preds) size_class_preds;
  slab_region_pred_join_lemma' n slab_region size_classes n1 n2

#restart-solver

(*
so far, so good, with the exception of:
- sc? and sc_ex? pattern: use a opaque predicate
*)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
val init_all_size_classes'
  (#opened:_)
  (offset: US.t)
  (n1: US.t{US.v n1 > 0})
  (n2: US.t{US.v n2 > 0})
  (n: US.t{
    US.v n == US.v n1 + US.v n2 /\
    UInt.size (US.v n) U32.n /\
    US.fits (US.v sc_slab_region_size * US.v n) /\
    //US.fits (US.v sc_slab_region_size * US.v n1) /\
    //US.fits (US.v sc_slab_region_size * US.v n2) /\
    US.fits (US.v n + US.v offset)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v sc_slab_region_size * US.v n /\
    A.length slab_region >= US.v sc_slab_region_size * US.v n1 /\
    A.length slab_region >= US.v sc_slab_region_size * US.v n2 /\
    True
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  : SteelGhost unit opened
  (
    A.varray (A.split_l size_classes n1) `star`
    A.varray (A.split_r size_classes n1)
  )
  (fun _ ->
    A.varray size_classes
  )
  (requires fun h0 ->
    A.length (A.split_l slab_region (US.mul sc_slab_region_size n1)) == US.v sc_slab_region_size * US.v n1 /\
    A.length (A.split_r slab_region (US.mul sc_slab_region_size n1)) == US.v sc_slab_region_size * US.v n2 /\
    TLA.length sizes >= US.v n + US.v offset /\
    synced_sizes2 offset
      (asel (A.split_l size_classes n1) h0) sizes (US.v n1) /\
    synced_sizes2 (US.add offset n1)
      (asel (A.split_r size_classes n1) h0) sizes (US.v n2) /\
    size_class_preds (asel (A.split_l size_classes n1) h0) (US.v n1) (A.split_l slab_region (US.mul sc_slab_region_size n1)) /\
    size_class_preds (asel (A.split_r size_classes n1) h0) (US.v n2) (A.split_r slab_region (US.mul sc_slab_region_size n1)) /\
    True
    //(forall (i:nat{i < US.v n1}).
    //  size_class_pred (A.split_l slab_region (US.mul n1 sc_slab_region_size)) (Seq.index (asel (A.split_l size_classes n1) h0) i) i
    //)
    ///\
    //(forall (i:nat{i < US.v n2}).
    //  size_class_pred (A.split_r slab_region (US.mul n1 sc_slab_region_size)) (Seq.index (asel (A.split_r size_classes n1) h0) i) i
    //)
  )
  (ensures fun _ _ h1 ->
    TLA.length sizes >= US.v n + US.v offset /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n) /\
    size_class_preds (asel size_classes h1) (US.v n) slab_region
  )
#pop-options

#restart-solver

//[@@ handle_smt_goals]
//let tac () : FStar.Tactics.Tac unit = FStar.Tactics.norm [zeta_full; delta_only [`%focus_rmem; `%focus_rmem'; `%unrestricted_focus_rmem]]

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300 --query_stats"
let init_all_size_classes'
  offset
  n1 n2 n
  slab_region
  size_classes
  sizes
  =
  let size_classes1_s0 = gget (A.varray (A.split_l size_classes n1)) in
  let size_classes2_s0 = gget (A.varray (A.split_r size_classes n1)) in
  synced_sizes_join offset n1 n2 n size_classes sizes;
  let size_classes_s1 = gget (A.varray size_classes) in
  assert (G.reveal size_classes_s1 == Seq.append size_classes1_s0 size_classes2_s0);
  Seq.lemma_split size_classes_s1 (US.v n1);
  let size_classes1_s1, size_classes2_s1 = Seq.split size_classes_s1 (US.v n1) in
  Seq.lemma_append_inj
    size_classes1_s0 size_classes2_s0
    size_classes1_s1 size_classes2_s1;
  assert (G.reveal size_classes1_s0 == size_classes1_s1);
  assert (G.reveal size_classes2_s0 == size_classes2_s1);
  //assume (
  //  US.fits (US.v sc_slab_region_size * US.v n1) /\
  //  US.fits (US.v sc_slab_region_size * US.v n2)
  //);
  slab_region_pred_join_lemma n1 n2 n slab_region size_classes_s1
#pop-options

val init_all_size_classes
  (l1:list sc)
  (l2:list sc_ex)
  (offset: US.t)
  (n: US.t{
    US.v n == List.length l1 + List.length l2 /\
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n + US.v offset) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (n1: US.t{US.v n1 == List.length l1 /\ US.v n1 > 0})
  (n2: US.t{US.v n2 == List.length l2 /\ US.v n2 > 0})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n1
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v metadata_max_ex * US.v n2
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n1 + US.v metadata_max_ex * US.v n2
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  : Steel unit
  (
    A.varray (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) `star`
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) `star`
    A.varray md_bm_region `star`
    A.varray md_bm_region_b `star`
    A.varray (A.split_l md_region (US.mul metadata_max n1)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max n1)) `star`
    A.varray (A.split_l size_classes n1) `star`
    A.varray (A.split_r size_classes n1)
  )
  (fun _ ->
    A.varray size_classes
  )
  (requires fun h0 ->
    Cons? l1 /\
    Cons? l2 /\
    US.v n1 > 0 /\
    US.v n2 > 0 /\
    array_u8_alignment (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) (u32_to_sz page_size) /\
    array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) h0) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) h0) /\
    zf_u64 (A.asel md_bm_region h0) /\
    zf_b (A.asel md_bm_region_b h0) /\
    TLA.length sizes >= US.v n + US.v offset /\
    //(forall (i:nat{i < US.v n1}) . Sc? (Seq.index (asel (A.split_l size_classes n1) h0) i).data.size) /\
    //(forall (i:nat{i < US.v n2}) . Sc_ex? (Seq.index (asel (A.split_r size_classes n1) h0) i).data.size) /\
    True
  )
  (ensures fun _ _ h1 ->
    TLA.length sizes >= US.v n + US.v offset /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n) /\
    size_class_preds (asel size_classes h1) (US.v n) slab_region
    //(forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

#restart-solver

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let init_all_size_classes
  l1 l2
  offset
  n n1 n2
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  init_all_size_classes_wrapper1 l1 offset n1
    (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1))
    md_bm_region
    (A.split_l md_region (US.mul metadata_max n1))
    (A.split_l size_classes n1)
    sizes;
  assume (A.length (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1))
  ==
  US.v metadata_max_ex * US.v slab_size * US.v n2);
  assume (A.length (A.split_r md_region (US.mul metadata_max n1))
  ==
  US.v metadata_max_ex * US.v n2);
  assume (A.length (A.split_r size_classes n1) == US.v n2);
  init_all_size_classes_wrapper2 l2 (US.add offset n1) n2
    (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1))
    md_bm_region_b
    (A.split_r md_region (US.mul metadata_max n1))
    (A.split_r size_classes n1)
    sizes;
  init_all_size_classes'
    offset
    n1 n2 n
    slab_region
    size_classes
    sizes
#pop-options

val init_all_size_classes_wrapper
  (l1:list sc)
  (l2:list sc_ex)
  (offset: US.t)
  (n: US.t{
    US.v n == List.length l1 + List.length l2 /\
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n + US.v offset) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n)
  })
  (n1: US.t{US.v n1 == List.length l1})
  (n2: US.t{US.v n2 == List.length l2})
  (slab_region: array U8.t{
    A.length slab_region == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v metadata_max * US.v 4sz * US.v n1
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v metadata_max_ex * US.v n2
  })
  (md_region: array AL.cell{
    A.length md_region == US.v metadata_max * US.v n1 + US.v metadata_max_ex * US.v n2
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  : Steel unit
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_bm_region_b `star`
    A.varray md_region `star`
    A.varray size_classes
  )
  (fun _ ->
    A.varray size_classes
  )
  (requires fun h0 ->
    Cons? l1 /\
    Cons? l2 /\
    US.v n1 > 0 /\
    US.v n2 > 0 /\
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0) /\
    zf_b (A.asel md_bm_region_b h0) /\
    TLA.length sizes >= US.v n + US.v offset /\
    //(forall (i:nat{i < US.v n1}) . Sc? (Seq.index (asel size_classes h0) i).data.size) /\
    //(forall (i:nat{i >= US.v n1 /\ i < US.v n}) . Sc_ex? (Seq.index (asel size_classes h0) i).data.size) /\
    True
  )
  (ensures fun _ _ h1 ->
    TLA.length sizes >= US.v n + US.v offset /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n) /\
    size_class_preds (asel size_classes h1) (US.v n) slab_region
  )


#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"
let init_all_size_classes_wrapper
  l1 l2
  offset
  n n1 n2
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  let slab_region_s0 = gget (A.varray slab_region) in
  f_lemma n n1;
  zf_u8_split
    slab_region_s0
    (US.v (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1));
  A.ghost_split slab_region
    (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1);
  A.ghost_split md_region
    (US.mul metadata_max n1);
  A.ghost_split size_classes n1;
  assume (array_u8_alignment (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) (u32_to_sz page_size));
  assume (array_u8_alignment (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n1)) (u32_to_sz page_size));
  let size_classes1_s0 = gget (A.varray (A.split_l size_classes n1)) in
  let size_classes2_s0 = gget (A.varray (A.split_r size_classes n1)) in
  init_all_size_classes
    l1 l2
    offset
    n n1 n2
    slab_region
    md_bm_region
    md_bm_region_b
    md_region
    size_classes
    sizes
#pop-options

// so far, initialization of one arena
// now, initialization of several arenas

#restart-solver


(*
so far, so good, with the exception of:
- sc? and sc_ex? pattern: use a opaque predicate
*)

/// A logical predicate indicating that a list of sizes corresponds
/// to the sizes of a list of size_classes
[@"opaque_to_smt"]
unfold
let hidden_pred
  (l1: list sc)
  (l2: list sc_ex)
  (n n1 n2 s1 s2 s3: US.t)
  : prop
  =
  US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
  US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
  US.fits (US.v metadata_max * US.v n) /\
  US.v n1 == List.length l1 /\ US.v n1 > 0 /\
  US.v n2 == List.length l2 /\ US.v n2 > 0 /\
  US.v n == US.v n1 + US.v n2 /\
  Cons? l1 /\
  Cons? l2 /\
  US.v n == List.length l1 + List.length l2 /\
  // arena_slab_region_size
  //US.v s1 == US.v sc_slab_region_size * US.v n /\
  // arena md_bm_region size
  US.v s1 == US.v metadata_max * US.v 4sz * US.v n1 /\
  // arena md_bm_region_b size
  US.v s2 == US.v metadata_max_ex * US.v n2 /\
  // arena md_region size
  US.v s3 == US.v metadata_max * US.v n1 + US.v metadata_max_ex * US.v n2

val init_one_arena'
  (offset: US.t)
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n + US.v offset)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size
  })
  (size_classes: array size_class{A.length size_classes == US.v n})
  (sizes: TLA.t sc_union)
  : Steel unit
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_bm_region_b `star`
    A.varray md_region `star`
    A.varray size_classes
  )
  (fun _ ->
    A.varray size_classes
  )
  (requires fun h0 ->
    US.v n == US.v n1 + US.v n2 /\
    //(forall (i:nat{i < US.v n1}) . Sc? (Seq.index (asel size_classes h0) i).data.size) /\
    //(forall (i:nat{i >= US.v n1 /\ i < US.v n}) . Sc_ex? (Seq.index (asel size_classes h0) i).data.size) /\
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0) /\
    zf_b (A.asel md_bm_region_b h0) /\
    TLA.length sizes >= US.v n + US.v offset /\
    US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size
  )
  (ensures fun _ _ h1 ->
    TLA.length sizes >= US.v n + US.v offset /\
    A.length slab_region >= US.v sc_slab_region_size * US.v n /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n) /\
    size_class_preds (asel size_classes h1) (US.v n) slab_region
  )

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"
let init_one_arena'
  offset
  l1 l2 n1 n2 n
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  reveal_opaque (`%hidden_pred) hidden_pred;
  init_all_size_classes_wrapper
    l1 l2
    offset
    n n1 n2
    slab_region
    md_bm_region
    md_bm_region_b
    md_region
    size_classes
    sizes
#pop-options

#restart-solver

//[@"opaque_to_smt"]
//let sc_list_layout1
//  (n1 n2: (v:US.t{US.v v > 0}))
//  (n: US.t{US.v n == US.v n1 + US.v n2})
//  (sizes: TLA.t sc_union{TLA.length sizes == US.v n})
//  : prop
//  =
//  (forall (i:US.t{US.v i < US.v n1}).
//    Sc? (TLA.get sizes i)) /\
//  (forall (i:US.t{US.v i >= US.v n1 /\ US.v i < US.v n}).
//    Sc_ex? (TLA.get sizes i))
//
//#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
//[@"opaque_to_smt"]
//let sc_list_layout2
//  (nb_arenas: US.t{US.v nb_arenas > 0})
//  (n1 n2: (v:US.t{US.v v > 0}))
//  (n: US.t{US.v n == US.v n1 + US.v n2})
//  (sizes: TLA.t sc_union{
//    US.fits (US.v nb_arenas * US.v n) /\
//    TLA.length sizes == US.v nb_arenas * US.v n
//  })
//  : prop
//  =
//  (forall (k:US.t{US.v k < US.v nb_arenas}).
//    US.fits (US.v nb_arenas * US.v k) /\
//    (forall (i: US.t{US.v i < US.v n1}).
//      US.fits (US.v nb_arenas * US.v k + US.v i) /\
//      US.v nb_arenas * US.v k + US.v i < TLA.length sizes /\
//      Sc? (TLA.get sizes (US.add (US.mul nb_arenas k) i))
//    ) /\
//    (forall (i: US.t{US.v i >= US.v n1 /\ US.v i < US.v n}).
//      US.fits (US.v nb_arenas * US.v k + US.v i) /\
//      US.v nb_arenas * US.v k + US.v i < TLA.length sizes /\
//      Sc_ex? (TLA.get sizes (US.add (US.mul nb_arenas k) i))
//    )
//  )
//#pop-options
//
//let sc_list_layout_lemma
//  (nb_arenas: US.t{US.v nb_arenas > 1})
//  (n1 n2: (v:US.t{US.v v > 0}))
//  (n: US.t{US.v n == US.v n1 + US.v n2})
//  (sizes: TLA.t sc_union{
//    US.fits (US.v nb_arenas * US.v n) /\
//    TLA.length sizes == US.v nb_arenas * US.v n
//  })
//  : Lemma
//  (requires sc_list_layout2 nb_arenas n1 n2 n sizes)
//  (ensures (
//    let sizes1, sizes2 = TLAO.split sizes (US.v n) in
//    sc_list_layout1 n1 n2 n sizes1))
//  = admit ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
val init_one_arena
  (offset: US.t)
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n + US.v offset)
  })
  (nb_arenas: US.t{US.v nb_arenas > 0})
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (slab_region: array U8.t{
    A.length slab_region >= US.v arena_slab_region_size
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region >= US.v arena_md_bm_region_size
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size
  })
  (md_region: array AL.cell{
    A.length md_region >= US.v arena_md_region_size
  })
  (size_classes: array size_class{
    A.length size_classes >= US.v n
  })
  (sizes: TLA.t sc_union)//{TLA.length sizes == US.v n * US.v nb_arenas})
  : Steel unit
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_bm_region_b `star`
    A.varray md_region `star`
    A.varray size_classes
  )
  (fun _ ->
    A.varray (A.split_r slab_region arena_slab_region_size) `star`
    A.varray (A.split_r md_bm_region arena_md_bm_region_size) `star`
    A.varray (A.split_r md_bm_region_b arena_md_bm_region_b_size) `star`
    A.varray (A.split_r md_region arena_md_region_size) `star`
    //A.varray (A.split_l size_classes n) `star`
    //A.varray (A.split_r size_classes n)
    A.varray size_classes
  )
  (requires fun h0 ->
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0) /\
    zf_b (A.asel md_bm_region_b h0) /\
    US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size /\
    US.v n1 + US.v n2 == US.v n /\
    TLA.length sizes >= US.v n + US.v offset /\
    A.length size_classes >= US.v n /\
    //sc_list_layout1 n1 n2 n
    //(forall (i:nat{i < US.v n1}) . Sc? (Seq.index (asel size_classes h0) i).data.size) /\
    //(forall (i:nat{i >= US.v n1 /\ i < US.v n}) . Sc_ex? (Seq.index (asel size_classes h0) i).data.size) /\
    True
    //(forall (k:nat{k < US.v nb_arenas}).
    //  (forall (i:nat{i < US.v n1}) .
    //    Sc? (Seq.index (asel size_classes h0) (k * US.v nb_arenas + i)).data.size) /\
    //  (forall (i:nat{i >= US.v n1 /\ i < US.v n}) .
    //    Sc_ex? (Seq.index (asel size_classes h0) (k * US.v nb_arenas + i)).data.size)
    //)
  )
  (ensures fun _ _ h1 ->
    array_u8_alignment (A.split_r slab_region arena_slab_region_size) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region arena_slab_region_size) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region arena_md_bm_region_size) h1) /\
    zf_b (A.asel (A.split_r md_bm_region_b arena_md_bm_region_b_size) h1) /\
    TLA.length sizes >= US.v n + US.v offset /\
    A.length size_classes >= US.v n /\
    A.length slab_region >= US.v sc_slab_region_size * US.v n /\
    synced_sizes2 offset (asel size_classes h1) sizes (US.v n) /\
    size_class_preds (asel size_classes h1) (US.v n) slab_region
  )
#pop-options

#restart-solver

#restart-solver

let synced_sizes2_extend_lemma
  (offset: US.t)
  (size_classes1 size_classes2:Seq.seq size_class)
  (sizes:TLA.t sc_union)
  (k:nat{
    k <= Seq.length size_classes1 /\
    k <= Seq.length size_classes2 /\
    k + US.v offset <= TLA.length sizes
  })
  : Lemma
  (requires
    Seq.slice size_classes1 0 k
    ==
    Seq.slice size_classes2 0 k /\
    synced_sizes2 offset size_classes1 sizes k
  )
  (ensures
    synced_sizes2 offset size_classes2 sizes k
  )
  =
  Classical.forall_intro (SeqUtils.lemma_index_slice size_classes1 0 k);
  Classical.forall_intro (SeqUtils.lemma_index_slice size_classes2 0 k);
  assume (forall (i:nat{i < k}).
    Seq.index size_classes1 i
    ==
    Seq.index size_classes2 i
  );
  reveal_opaque (`%synced_sizes2) synced_sizes2

let size_class_preds_extend_lemma
  (size_classes1 size_classes2:Seq.seq size_class)
  (k:nat{
    k <= Seq.length size_classes1 /\
    k <= Seq.length size_classes2
  })
  (slab_region1 slab_region2: (v:array U8.t{A.length v >= US.v sc_slab_region_size * k}))
  : Lemma
  (requires
    Seq.slice size_classes1 0 k
    ==
    Seq.slice size_classes2 0 k /\
    A.offset (A.ptr_of slab_region1)
    ==
    A.offset (A.ptr_of slab_region2) /\
    same_base_array slab_region1 slab_region2 /\
    size_class_preds size_classes1 k slab_region1
  )
  (ensures
    size_class_preds size_classes2 k slab_region2
  )
  =
  assume (forall (i:nat{i < k}).
    Seq.index size_classes1 i
    ==
    Seq.index size_classes2 i
  );
  reveal_opaque (`%size_class_preds) size_class_preds

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"
let init_one_arena
  offset
  l1 l2 n1 n2 n
  nb_arenas
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  let slab_region_s = gget (A.varray slab_region) in
  let md_bm_region_s = gget (A.varray md_bm_region) in
  let md_bm_region_b_s = gget (A.varray md_bm_region_b) in
  zf_u8_split slab_region_s (US.v arena_slab_region_size);
  zf_u64_split md_bm_region_s (US.v arena_md_bm_region_size);
  zf_b_split md_bm_region_b_s (US.v arena_md_bm_region_b_size);
  A.ghost_split slab_region arena_slab_region_size;
  A.ghost_split md_bm_region arena_md_bm_region_size;
  A.ghost_split md_bm_region_b arena_md_bm_region_b_size;
  A.ghost_split md_region arena_md_region_size;
  A.ghost_split size_classes n;
  //assume (US.v nb_arenas > 1);
  //let sizes1, sizes2 = TLAO.split sizes (US.v n) in
  assume (array_u8_alignment (A.split_l slab_region arena_slab_region_size) (u32_to_sz page_size));
  assume (array_u8_alignment (A.split_r slab_region arena_slab_region_size) (u32_to_sz page_size));
  init_one_arena'
    offset
    l1 l2 n1 n2 n
    arena_slab_region_size
    arena_md_region_size
    arena_md_bm_region_size
    arena_md_bm_region_b_size
    (A.split_l slab_region arena_slab_region_size)
    (A.split_l md_bm_region arena_md_bm_region_size)
    (A.split_l md_bm_region_b arena_md_bm_region_b_size)
    (A.split_l md_region arena_md_region_size)
    (A.split_l size_classes n)
    sizes;
  let s1 = gget (A.varray (A.split_l size_classes n)) in
  let s2 = gget (A.varray (A.split_r size_classes n)) in
  A.ghost_join
   (A.split_l size_classes n)
   (A.split_r size_classes n)
   ();
  change_equal_slprop
   (A.varray (A.merge
     (A.split_l size_classes n)
     (A.split_r size_classes n)))
   (A.varray size_classes);
  let s = gget (A.varray size_classes) in
  let s1', s2' = Seq.split s (US.v n) in
  Seq.lemma_append_inj s1 s2 s1' s2';
  Seq.lemma_split s (US.v n);
  assert (Seq.slice s 0 (US.v n) == Seq.slice s1 0 (US.v n));
  synced_sizes2_extend_lemma offset
    s1 s
    sizes
    (US.v n);
  size_class_preds_extend_lemma
    s1 s
    (US.v n)
    (A.split_l slab_region arena_slab_region_size)
    slab_region;
  ()

[@"opaque_to_smt"]
unfold
let hidden_pred2
  (n s1: US.t)
  : prop
  =
  US.v n > 0 /\
  US.v s1 > 0 /\
  US.v s1 == US.v sc_slab_region_size * US.v n

// predicate:
// sizes of k arenas after the offset-nth one
// are properly synced
[@"opaque_to_smt"]
let synced_sizes_arena
  (n: US.t)
  (arena_slab_region_size: US.t)
  (offset: US.t)
  (size_classes:Seq.seq size_class)
  (sizes:TLA.t sc_union)
  (k:nat{
    US.v n * k <= Seq.length size_classes /\
    US.v n * (k + US.v offset) <= TLA.length sizes /\
    US.fits (US.v n * (US.v offset + k)) /\
    //US.fits (US.v n * US.v offset)
    True
  })
  : prop
  =
  assert (US.v n * k + US.v (US.mul n offset) <= TLA.length sizes);
  synced_sizes2 (US.mul n offset) size_classes sizes (US.v n * k)

// predicate:
//

[@"opaque_to_smt"]
let size_class_preds_arena
  (n: US.t)
  (arena_slab_region_size: US.t)
  (size_classes:Seq.seq size_class)
  (k:nat{
    US.v n * k <= Seq.length size_classes /\
    hidden_pred2 n arena_slab_region_size
  })
  (slab_region: array U8.t{A.length slab_region >= US.v arena_slab_region_size * k})
  : prop
  =
  reveal_opaque (`%hidden_pred2) hidden_pred2;
  assert (US.v sc_slab_region_size * (US.v n * k)
  == (US.v sc_slab_region_size * US.v n) * k);
  assert (US.v sc_slab_region_size * (US.v n * k)
  == US.v arena_slab_region_size * k);
  size_class_preds size_classes (US.v n * k) slab_region

val init_one_arena2
  (offset: US.t)
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    US.fits (US.v n * (US.v offset + 1))
  })
  (nb_arenas: US.t{US.v nb_arenas > 0})
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (slab_region: array U8.t{
    A.length slab_region >= US.v arena_slab_region_size
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region >= US.v arena_md_bm_region_size
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size
  })
  (md_region: array AL.cell{
    A.length md_region >= US.v arena_md_region_size
  })
  (size_classes: array size_class{
    A.length size_classes >= US.v n
  })
  (sizes: TLA.t sc_union)//{TLA.length sizes == US.v n * US.v nb_arenas})
  : Steel unit
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_bm_region_b `star`
    A.varray md_region `star`
    A.varray size_classes
  )
  (fun _ ->
    A.varray (A.split_r slab_region arena_slab_region_size) `star`
    A.varray (A.split_r md_bm_region arena_md_bm_region_size) `star`
    A.varray (A.split_r md_bm_region_b arena_md_bm_region_b_size) `star`
    A.varray (A.split_r md_region arena_md_region_size) `star`
    //A.varray (A.split_l size_classes n) `star`
    //A.varray (A.split_r size_classes n)
    A.varray size_classes
  )
  (requires fun h0 ->
    array_u8_alignment slab_region (u32_to_sz page_size) /\
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0) /\
    zf_b (A.asel md_bm_region_b h0) /\
    //US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size /\
    hidden_pred2 n arena_slab_region_size /\
    TLA.length sizes >= US.v n * (US.v offset + 1) /\
    A.length size_classes >= US.v n /\
    //sc_list_layout1 n1 n2 n
    //(forall (i:nat{i < US.v n1}) . Sc? (Seq.index (asel size_classes h0) i).data.size) /\
    //(forall (i:nat{i >= US.v n1 /\ i < US.v n}) . Sc_ex? (Seq.index (asel size_classes h0) i).data.size) /\
    True
    //(forall (k:nat{k < US.v nb_arenas}).
    //  (forall (i:nat{i < US.v n1}) .
    //    Sc? (Seq.index (asel size_classes h0) (k * US.v nb_arenas + i)).data.size) /\
    //  (forall (i:nat{i >= US.v n1 /\ i < US.v n}) .
    //    Sc_ex? (Seq.index (asel size_classes h0) (k * US.v nb_arenas + i)).data.size)
    //)
  )
  (ensures fun _ _ h1 ->
    array_u8_alignment (A.split_r slab_region arena_slab_region_size) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region arena_slab_region_size) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region arena_md_bm_region_size) h1) /\
    zf_b (A.asel (A.split_r md_bm_region_b arena_md_bm_region_b_size) h1) /\
    TLA.length sizes >= US.v n * (US.v offset + 1) /\
    A.length size_classes >= US.v n /\
    hidden_pred2 n arena_slab_region_size /\
    synced_sizes_arena n arena_slab_region_size
      offset (asel size_classes h1) sizes 1 /\
    size_class_preds_arena n arena_slab_region_size
      (asel size_classes h1) 1 slab_region /\
    //size_class_preds (asel size_classes h1) (US.v n) slab_region
    True
  )

#restart-solver

let synced_sizes_arena_lemma
  (n: US.t)
  (arena_slab_region_size: US.t)
  (offset: US.t)
  (size_classes:Seq.seq size_class)
  (sizes:TLA.t sc_union)
  (k:nat{
    hidden_pred2 n arena_slab_region_size /\
    US.v n * k <= Seq.length size_classes /\
    US.v n * (k + US.v offset) <= TLA.length sizes /\
    US.v n * k + US.v n * US.v offset <= TLA.length sizes /\
    US.fits (US.v n * (US.v offset + k)) /\
    //US.fits (US.v n * US.v offset)
    True
 
  })
  : Lemma
  (requires
    synced_sizes2 (US.mul n offset) size_classes sizes (US.v n * k)
  )
  (ensures
    synced_sizes_arena n arena_slab_region_size offset size_classes sizes k
  )
  =
  admit ();
  assert (US.v n * k + US.v (US.mul n offset) <= TLA.length sizes);
  reveal_opaque (`%synced_sizes_arena) synced_sizes_arena

let size_class_preds_arena_lemma
  (n: US.t)
  (arena_slab_region_size: US.t)
  (size_classes:Seq.seq size_class)
  (k:nat{US.v n * k <= Seq.length size_classes})
  (slab_region: array U8.t{A.length slab_region >= US.v arena_slab_region_size * k})
  : Lemma
  (requires
    US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    size_class_preds size_classes (US.v n * k) slab_region /\
    hidden_pred2 n arena_slab_region_size
  )
  (ensures
    size_class_preds_arena n arena_slab_region_size size_classes k slab_region
  )
  =
  reveal_opaque (`%size_class_preds_arena) size_class_preds_arena

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"
let init_one_arena2
  offset
  l1 l2 n1 n2 n
  nb_arenas
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  assume (US.fits (US.v n * US.v offset));
  let offset' = US.mul n offset in
  assume (US.fits (US.v n + US.v offset'));
  assume (TLA.length sizes >= US.v n + US.v offset');
  reveal_opaque (`%hidden_pred2) hidden_pred2;
  init_one_arena
    offset'
    l1 l2 n1 n2 n
    nb_arenas
    arena_slab_region_size
    arena_md_region_size
    arena_md_bm_region_size
    arena_md_bm_region_b_size
    slab_region
    md_bm_region
    md_bm_region_b
    md_region
    size_classes
    sizes;
  let s = gget (A.varray size_classes) in
  assert (synced_sizes2 offset' s sizes (US.v n));
  assert (synced_sizes2 (US.mul n offset) s sizes (US.v n * 1));
  synced_sizes_arena_lemma n arena_slab_region_size offset s sizes 1;
  assert (synced_sizes_arena n arena_slab_region_size offset s sizes 1);
  assert (size_class_preds s (US.v n * 1) slab_region);
  size_class_preds_arena_lemma n arena_slab_region_size s 1 slab_region;
  assert (size_class_preds_arena n arena_slab_region_size s 1 slab_region);
  ()
  //reveal_opaque (`%size_class_preds_arena) size_class_preds_arena
#pop-options

///// A logical predicate indicating that a list of sizes corresponds
///// to the sizes of a list of size_classes
//let size_class_preds_arena
//
//  (arena_slab_region_size: US.t{US.v arena_slab_region_size > 0})
//  (size_classes:Seq.seq size_class)
//  (k:nat{k <= Seq.length size_classes})
//  (slab_region: array U8.t{A.length slab_region >= US.v sc_slab_region_size * k})
//  : prop
//  =
//  forall (i:nat{i < k}). (
//    size_class_pred slab_region (Seq.index size_classes i) i
//  )

//[@"opaque_to_smt"]
//let size_class_preds2
//  (size_classes:Seq.seq size_class)
//  (k:nat{k <= Seq.length size_classes})
//  (slab_region: array U8.t{A.length slab_region >= US.v sc_slab_region_size * k})
//  : prop
//  =
//  forall (i:nat{i < k}). (
//    size_class_pred slab_region (Seq.index size_classes i) i
//  )



#push-options "--fuel 0 --ifuel 0 --z3rlimit 500 --split_queries no --query_stats"
val init_nth_arena_aux
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0 /\
    US.fits (US.v n * US.v nb_arenas) /\
    US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_region_size * US.v nb_arenas) /\
    True
  })
  //})
  (k: US.t{US.v k < US.v nb_arenas /\
    US.fits (US.v n * US.v k) /\
    US.fits (US.v arena_slab_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k) /\
    US.fits (US.v arena_md_region_size * US.v k)
  })
  (k': US.t{US.v k' <= US.v nb_arenas /\
    US.fits (US.v n * US.v k') /\
    US.fits (US.v arena_slab_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k') /\
    US.fits (US.v arena_md_region_size * US.v k')
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size * US.v nb_arenas /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k' /\
    A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size * US.v nb_arenas /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k' /\
    A.length (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) >= US.v arena_md_bm_region_size
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size * US.v nb_arenas /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k' /\
    A.length (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) >= US.v arena_md_bm_region_b_size
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size * US.v nb_arenas /\
    A.length md_region >= US.v arena_md_region_size * US.v k /\
    A.length md_region >= US.v arena_md_region_size * US.v k' /\
    A.length (A.split_r md_region (US.mul arena_md_region_size k)) >= US.v arena_md_region_size
  })
  (size_classes: array size_class{
    A.length size_classes == US.v n * US.v nb_arenas /\
    A.length size_classes >= US.v n * US.v k /\
    A.length size_classes >= US.v n * US.v k'
  })
  //{
  //  A.length size_classes == US.v n * US.v nb_arenas /\
  //  A.length size_classes >= US.v n * US.v k'
  //})
  (sizes: TLA.t sc_union)
  //{
  //  TLA.length sizes == US.v n * US.v nb_arenas /\
  //  TLA.length sizes >= US.v n * US.v k'
  //})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size k)) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size k)) `star`
    A.varray (A.split_r size_classes (US.mul n k))
  )
  (fun _ ->
    A.varray (A.split_r (A.split_r slab_region (US.mul arena_slab_region_size k)) arena_slab_region_size) `star`
    A.varray (A.split_r (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) arena_md_bm_region_size) `star`
    A.varray (A.split_r (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) arena_md_bm_region_b_size) `star`
    A.varray (A.split_r (A.split_r md_region (US.mul arena_md_region_size k)) arena_md_region_size) `star`
    //A.varray (A.split_r slab_region (US.mul arena_slab_region_size k')) `star`
    //A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) `star`
    //A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) `star`
    //A.varray (A.split_r md_region (US.mul arena_md_region_size k')) `star`
    A.varray (A.split_r size_classes (US.mul n k))
    //A.varray (A.split_r size_classes (US.mul n k')) `star`
    //A.varray (A.split_l (A.split_r size_classes (US.mul n k)) n)
  )
  (requires fun h0 ->
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) h0) /\
    //US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size /\
    hidden_pred2 n arena_slab_region_size /\
    US.fits (US.v n * (US.v k + 1)) /\
    A.length size_classes >= US.v n * US.v k /\
    TLA.length sizes >= US.v n * (US.v k + 1) /\
    A.length size_classes >= US.v n * 1 /\
    //A.length size_classes >= US.v n * US.v k /\
    //synced_sizes_arena n arena_slab_region_size
    //  k (asel (A.split_r size_classes (US.mul n k)) h0) sizes 1 /\
    //size_class_preds_arena n arena_slab_region_size
    //  (asel size_classes h0) (US.v k) slab_region /\
    True
  )
  (ensures fun _ _ h1 ->
    array_u8_alignment (A.split_r (A.split_r slab_region (US.mul arena_slab_region_size k)) arena_slab_region_size) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r (A.split_r slab_region (US.mul arena_slab_region_size k)) arena_slab_region_size) h1) /\
    zf_u64 (A.asel (A.split_r (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) arena_md_bm_region_size) h1) /\
    zf_b (A.asel (A.split_r (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) arena_md_bm_region_b_size) h1) /\
    TLA.length sizes >= US.v n * (US.v k + 1) /\
    A.length (A.split_r size_classes (US.mul n k)) >= US.v n * 1 /\
    hidden_pred2 n arena_slab_region_size /\
    synced_sizes_arena n arena_slab_region_size
      k (asel (A.split_r size_classes (US.mul n k)) h1) sizes 1 /\
    A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size * 1 /\
    size_class_preds_arena n arena_slab_region_size
      (asel (A.split_r size_classes (US.mul n k)) h1) 1 (A.split_r slab_region (US.mul arena_slab_region_size k)) /\
    True
  )

#restart-solver

let _ = ()

#restart-solver

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 800 --query_stats"
//--z3cliopt smt.arith.nl=false"

module SM = Steel.Memory

#restart-solver

val init_nth_arena_aux_split_split
  (#opened:_)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0 /\
    US.fits (US.v n * US.v nb_arenas) /\
    US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_region_size * US.v nb_arenas) /\
    True
  })
  //})
  (k: US.t{US.v k < US.v nb_arenas /\
    US.fits (US.v n * US.v k) /\
    US.fits (US.v arena_slab_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k) /\
    US.fits (US.v arena_md_region_size * US.v k)
  })
  (k': US.t{US.v k' <= US.v nb_arenas /\
    US.fits (US.v n * US.v k') /\
    US.fits (US.v arena_slab_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k') /\
    US.fits (US.v arena_md_region_size * US.v k')
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size * US.v nb_arenas /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k' /\
    A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size * US.v nb_arenas /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k' /\
    A.length (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) >= US.v arena_md_bm_region_size
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size * US.v nb_arenas /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k' /\
    A.length (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) >= US.v arena_md_bm_region_b_size
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size * US.v nb_arenas /\
    A.length md_region >= US.v arena_md_region_size * US.v k /\
    A.length md_region >= US.v arena_md_region_size * US.v k' /\
    A.length (A.split_r md_region (US.mul arena_md_region_size k)) >= US.v arena_md_region_size
  })
  //(size_classes: array size_class{
  //  A.length size_classes == US.v n * US.v nb_arenas /\
  //  A.length size_classes >= US.v n * US.v k /\
  //  A.length size_classes >= US.v n * US.v k'
  //})
  //(m: SM.mem)
  //{
  //  A.length size_classes == US.v n * US.v nb_arenas /\
  //  A.length size_classes >= US.v n * US.v k'
  //})
  //(sizes: TLA.t sc_union)
  //{
  //  TLA.length sizes == US.v n * US.v nb_arenas /\
  //  TLA.length sizes >= US.v n * US.v k'
  //})
  : SteelGhost unit opened
  (
    A.varray (A.split_r (A.split_r slab_region (US.mul arena_slab_region_size k)) arena_slab_region_size) `star`
    A.varray (A.split_r (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) arena_md_bm_region_size) `star`
    A.varray (A.split_r (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) arena_md_bm_region_b_size) `star`
    A.varray (A.split_r (A.split_r md_region (US.mul arena_md_region_size k)) arena_md_region_size)
    //`star`
    //A.varray (A.split_r size_classes (US.mul n k))
  )
  (fun _ ->
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size k')) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size k'))
    //`star`
    //A.varray (A.split_r size_classes (US.mul n k))
    //A.varray (A.split_r size_classes (US.mul n k')) `star`
    //A.varray (A.split_l (A.split_r size_classes (US.mul n k)) n)
  )
  (requires fun h0 ->
    zf_u8 (A.asel (A.split_r (A.split_r slab_region (US.mul arena_slab_region_size k)) arena_slab_region_size) h0) /\
    zf_u64 (A.asel (A.split_r (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) arena_md_bm_region_size) h0) /\
    zf_b (A.asel (A.split_r (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) arena_md_bm_region_b_size) h0)
  )
  (ensures fun h0 _ h1 ->
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) h1) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) h1)
  )
  //  A.asel (A.split_r slab_region (US.mul arena_slab_region_size k')) h1
  //  `Seq.equal`
  //  A.asel (A.split_r (A.split_r slab_region (US.mul arena_slab_region_size k)) arena_slab_region_size) h0 /\
  //  A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) h1
  //  `Seq.equal`
  //  A.asel (A.split_r (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) arena_md_bm_region_size) h0 /\
  //  A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) h1
  //  `Seq.equal`
  //  A.asel (A.split_r (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) arena_md_bm_region_b_size) h0 /\
  //  A.asel (A.split_r md_region (US.mul arena_md_region_size k')) h1
  //  `Seq.equal`
  //  A.asel (A.split_r (A.split_r md_region (US.mul arena_md_region_size k)) arena_md_region_size) h0
  //)

let init_nth_arena_aux_split_split
  n
  arena_slab_region_size
  arena_md_region_size
  arena_md_bm_region_size
  arena_md_bm_region_b_size
  nb_arenas
  k k'
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  =
  sladmit ()

  //split_r_r_mul
  //  arena_slab_region_size
  //  k
  //  k'
  //  slab_region;
  //split_r_r_mul
  //  arena_md_bm_region_size
  //  k
  //  k'
  //  md_bm_region;
  //split_r_r_mul
  //  arena_md_bm_region_b_size
  //  k
  //  k'
  //  md_bm_region_b;
  //split_r_r_mul
  //  arena_md_region_size
  //  k
  //  k'
  //  md_region

#restart-solver

let init_nth_arena_aux
  l1 l2 n1 n2 n
  arena_slab_region_size
  arena_md_region_size
  arena_md_bm_region_size
  arena_md_bm_region_b_size
  nb_arenas
  k k'
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  //admit ();
  //assume (TLA.length sizes >= US.v n + (US.v n * US.v k));
  //assume (
  //  US.v n > 0 /\
  //  UInt.size (US.v n) U32.n
  //);
  //assume (US.v n * US.v k >= 0);
  ////assume (US.v n + US.v (US.mul n k) >= 0);
  ////assume (US.fits (US.v n + US.v (US.mul n k)));
  ////assume (
  ////  US.v arena_slab_region_size * US.v k >= 0 /\
  ////  US.v arena_md_bm_region_size * US.v k >= 0 /\
  ////  US.v arena_md_bm_region_b_size * US.v k >= 0 /\
  ////  US.v arena_md_region_size * US.v k >= 0
  ////);
  //assume (
  //  US.fits (US.v arena_slab_region_size * US.v k) /\
  //  US.fits (US.v arena_md_bm_region_size * US.v k) /\
  //  US.fits (US.v arena_md_bm_region_b_size * US.v k) /\
  //  US.fits (US.v arena_md_region_size * US.v k)
  //);
  //assume (A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size);
  //assume (A.length (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) >= US.v arena_md_bm_region_size);
  //assume (A.length (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) >= US.v arena_md_bm_region_b_size);
  //assume (A.length (A.split_r md_region (US.mul arena_md_region_size k)) >= US.v arena_md_region_size);
  //assume (A.length size_classes >= US.v n);
  //assume (US.fits (US.v n * US.v k));
  //assume (US.fits (US.v n + US.v (US.mul n k)));
  //assume (TLA.length sizes >= US.v n + US.v (US.mul n k));
  assume (US.fits (US.v n * (US.v k + 1)));
  assume (TLA.length sizes >= US.v n * (US.v k + 1));
  //let n' : n:US.t{
  //  US.v n > 0 /\
  //  UInt.size (US.v n) 32 /\
  //  US.fits (US.v n * (US.v k + 1))
  //} = n in
  //change_equal_slprop
  //  (A.varray (A.split_r size_classes (US.mul n k)))
  //  (A.varray (A.split_r size_classes (US.mul n' k)));
  init_one_arena2
    k
    l1 l2 n1 n2 n
    nb_arenas
    arena_slab_region_size
    arena_md_region_size
    arena_md_bm_region_size
    arena_md_bm_region_b_size
    (A.split_r slab_region (US.mul arena_slab_region_size k))
    (A.split_r md_bm_region (US.mul arena_md_bm_region_size k))
    (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k))
    (A.split_r md_region (US.mul arena_md_region_size k))
    (A.split_r size_classes (US.mul n k))
    sizes

#restart-solver

val init_nth_arena'
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0 /\
    US.fits (US.v n * US.v nb_arenas) /\
    US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_region_size * US.v nb_arenas) /\
    True
  })
  //})
  (k: US.t{US.v k < US.v nb_arenas /\
    US.fits (US.v n * US.v k) /\
    US.fits (US.v arena_slab_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k) /\
    US.fits (US.v arena_md_region_size * US.v k)
  })
  (k': US.t{US.v k' <= US.v nb_arenas /\
    US.fits (US.v n * US.v k') /\
    US.fits (US.v arena_slab_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k') /\
    US.fits (US.v arena_md_region_size * US.v k')
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size * US.v nb_arenas /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k' /\
    A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size * US.v nb_arenas /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k' /\
    A.length (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) >= US.v arena_md_bm_region_size
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size * US.v nb_arenas /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k' /\
    A.length (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) >= US.v arena_md_bm_region_b_size
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size * US.v nb_arenas /\
    A.length md_region >= US.v arena_md_region_size * US.v k /\
    A.length md_region >= US.v arena_md_region_size * US.v k' /\
    A.length (A.split_r md_region (US.mul arena_md_region_size k)) >= US.v arena_md_region_size
  })
  (size_classes: array size_class{
    A.length size_classes == US.v n * US.v nb_arenas /\
    A.length size_classes >= US.v n * US.v k /\
    A.length size_classes >= US.v n * US.v k'
  })
  //{
  //  A.length size_classes == US.v n * US.v nb_arenas /\
  //  A.length size_classes >= US.v n * US.v k'
  //})
  (sizes: TLA.t sc_union)
  //{
  //  TLA.length sizes == US.v n * US.v nb_arenas /\
  //  TLA.length sizes >= US.v n * US.v k'
  //})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size k)) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size k)) `star`
    A.varray (A.split_r size_classes (US.mul n k))
  )
  (fun _ ->
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size k')) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size k')) `star`
    //A.varray (A.split_r slab_region (US.mul arena_slab_region_size k')) `star`
    //A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) `star`
    //A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) `star`
    //A.varray (A.split_r md_region (US.mul arena_md_region_size k')) `star`
    A.varray (A.split_r size_classes (US.mul n k))
    //A.varray (A.split_r size_classes (US.mul n k')) `star`
    //A.varray (A.split_l (A.split_r size_classes (US.mul n k)) n)
  )
  (requires fun h0 ->
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) h0) /\
    //US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size /\
    hidden_pred2 n arena_slab_region_size /\
    US.fits (US.v n * (US.v k + 1)) /\
    A.length size_classes >= US.v n * US.v k /\
    TLA.length sizes >= US.v n * (US.v k + 1) /\
    A.length size_classes >= US.v n * 1 /\
    //A.length size_classes >= US.v n * US.v k /\
    //synced_sizes_arena n arena_slab_region_size
    //  k (asel (A.split_r size_classes (US.mul n k)) h0) sizes 1 /\
    //size_class_preds_arena n arena_slab_region_size
    //  (asel size_classes h0) (US.v k) slab_region /\
    True
  )
  (ensures fun _ _ h1 ->
    //array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size k')) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) h1) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) h1) /\
    TLA.length sizes >= US.v n * (US.v k + 1) /\
    A.length (A.split_r size_classes (US.mul n k)) >= US.v n * 1 /\
    hidden_pred2 n arena_slab_region_size /\
    synced_sizes_arena n arena_slab_region_size
      k (asel (A.split_r size_classes (US.mul n k)) h1) sizes 1 /\
    A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size * 1 /\
    size_class_preds_arena n arena_slab_region_size
      (asel (A.split_r size_classes (US.mul n k)) h1) 1 (A.split_r slab_region (US.mul arena_slab_region_size k)) /\
    True
  )

let init_nth_arena'
  l1 l2 n1 n2 n
  arena_slab_region_size
  arena_md_region_size
  arena_md_bm_region_size
  arena_md_bm_region_b_size
  nb_arenas
  k k'
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  init_nth_arena_aux
    l1 l2 n1 n2 n
    arena_slab_region_size
    arena_md_region_size
    arena_md_bm_region_size
    arena_md_bm_region_b_size
    nb_arenas
    k k'
    slab_region
    md_bm_region
    md_bm_region_b
    md_region
    size_classes
    sizes;
  init_nth_arena_aux_split_split
    n
    arena_slab_region_size
    arena_md_region_size
    arena_md_bm_region_size
    arena_md_bm_region_b_size
    nb_arenas
    k k'
    slab_region
    md_bm_region
    md_bm_region_b
    md_region

val init_nth_arena
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0 /\
    US.fits (US.v n * US.v nb_arenas) /\
    US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_region_size * US.v nb_arenas) /\
    True
  })
  //})
  (k: US.t{US.v k < US.v nb_arenas /\
    US.fits (US.v n * US.v k) /\
    US.fits (US.v arena_slab_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k) /\
    US.fits (US.v arena_md_region_size * US.v k)
  })
  (k': US.t{US.v k' <= US.v nb_arenas /\
    US.fits (US.v n * US.v k') /\
    US.fits (US.v arena_slab_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_size * US.v k') /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k') /\
    US.fits (US.v arena_md_region_size * US.v k')
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size * US.v nb_arenas /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k' /\
    A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size * US.v nb_arenas /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k' /\
    A.length (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) >= US.v arena_md_bm_region_size
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size * US.v nb_arenas /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k' /\
    A.length (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) >= US.v arena_md_bm_region_b_size
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size * US.v nb_arenas /\
    A.length md_region >= US.v arena_md_region_size * US.v k /\
    A.length md_region >= US.v arena_md_region_size * US.v k' /\
    A.length (A.split_r md_region (US.mul arena_md_region_size k)) >= US.v arena_md_region_size
  })
  (size_classes: array size_class{
    A.length size_classes == US.v n * US.v nb_arenas /\
    A.length size_classes >= US.v n * US.v k /\
    A.length size_classes >= US.v n * US.v k'
  })
  //{
  //  A.length size_classes == US.v n * US.v nb_arenas /\
  //  A.length size_classes >= US.v n * US.v k'
  //})
  (sizes: TLA.t sc_union)
  //{
  //  TLA.length sizes == US.v n * US.v nb_arenas /\
  //  TLA.length sizes >= US.v n * US.v k'
  //})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size k)) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size k)) `star`
    A.varray (A.split_r size_classes (US.mul n k))
  )
  (fun _ ->
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size k')) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size k')) `star`
    //A.varray (A.split_r slab_region (US.mul arena_slab_region_size k')) `star`
    //A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) `star`
    //A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) `star`
    //A.varray (A.split_r md_region (US.mul arena_md_region_size k')) `star`
    A.varray (A.split_r size_classes (US.mul n k))
    //A.varray (A.split_r size_classes (US.mul n k')) `star`
    //A.varray (A.split_l (A.split_r size_classes (US.mul n k)) n)
  )
  (requires fun h0 ->
    US.v k' == US.v k + 1 /\
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) h0) /\
    //US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size /\
    hidden_pred2 n arena_slab_region_size /\
    US.fits (US.v n * (US.v k + 1)) /\
    A.length size_classes >= US.v n * US.v k /\
    TLA.length sizes >= US.v n * (US.v k + 1) /\
    A.length size_classes >= US.v n * 1 /\
    //A.length size_classes >= US.v n * US.v k /\
    //synced_sizes_arena n arena_slab_region_size
    //  k (asel (A.split_r size_classes (US.mul n k)) h0) sizes 1 /\
    //size_class_preds_arena n arena_slab_region_size
    //  (asel size_classes h0) (US.v k) slab_region /\
    True
  )
  (ensures fun _ _ h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size k')) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k')) h1) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k')) h1) /\
    TLA.length sizes >= US.v n * (US.v k + 1) /\
    A.length (A.split_r size_classes (US.mul n k)) >= US.v n * 1 /\
    hidden_pred2 n arena_slab_region_size /\
    synced_sizes_arena n arena_slab_region_size
      k (asel (A.split_r size_classes (US.mul n k)) h1) sizes 1 /\
    A.length (A.split_r slab_region (US.mul arena_slab_region_size k)) >= US.v arena_slab_region_size * 1 /\
    size_class_preds_arena n arena_slab_region_size
      (asel (A.split_r size_classes (US.mul n k)) h1) 1 (A.split_r slab_region (US.mul arena_slab_region_size k)) /\
    True
  )

let init_nth_arena
  l1 l2 n1 n2 n
  arena_slab_region_size
  arena_md_region_size
  arena_md_bm_region_size
  arena_md_bm_region_b_size
  nb_arenas
  k k'
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  assume (array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size k')) (u32_to_sz page_size));
  init_nth_arena'
    l1 l2 n1 n2 n
    arena_slab_region_size
    arena_md_region_size
    arena_md_bm_region_size
    arena_md_bm_region_b_size
    nb_arenas
    k k'
    slab_region
    md_bm_region
    md_bm_region_b
    md_region
    size_classes
    sizes

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400 --split_queries no --query_stats"
val init_n_first_arenas
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0})
  //  US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_region_size * US.v nb_arenas)
  //})
  (k: US.t{US.v k <= US.v nb_arenas /\
    US.fits (US.v arena_slab_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_size * US.v k) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v k) /\
    US.fits (US.v arena_md_region_size * US.v k)
  })
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size * US.v nb_arenas /\
    A.length slab_region >= US.v arena_slab_region_size * US.v k
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size * US.v nb_arenas /\
    A.length md_bm_region >= US.v arena_md_bm_region_size * US.v k
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size * US.v nb_arenas /\
    A.length md_bm_region_b >= US.v arena_md_bm_region_b_size * US.v k
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size * US.v nb_arenas /\
    A.length md_region >= US.v arena_md_region_size * US.v k
  })
  (size_classes: array size_class{
    A.length size_classes == US.v n * US.v nb_arenas /\
    A.length size_classes >= US.v n * US.v k
  })
  (sizes: TLA.t sc_union{
    TLA.length sizes == US.v n * US.v nb_arenas /\
    TLA.length sizes >= US.v n * US.v k
  })
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size 0sz)) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size 0sz)) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size 0sz)) `star`
    A.varray size_classes
  )
  (fun _ ->
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size k)) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size k)) `star`
    A.varray size_classes
  )
  (requires fun h0 ->
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size 0sz)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size 0sz)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size 0sz)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size 0sz)) h0) /\
    US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size
  )
  (ensures fun _ _ h1 ->
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size k)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size k)) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)) h1) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)) h1) /\
    A.length slab_region >= US.v sc_slab_region_size * (US.v n * US.v k) /\
    //Seq.length (asel size_classes h1) >= US.v n * US.v k /\
    UInt.size (US.v n * US.v k) U32.n /\
    synced_sizes2 0sz (asel size_classes h1) sizes (US.v n * US.v k) /\
    size_class_preds (asel size_classes h1) (US.v n * US.v k) slab_region /\
    True
  )


#push-options "--fuel 0 --ifuel 0 --z3rlimit 600 --split_queries no --query_stats"
let rec init_n_first_arenas
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0})
  k
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  = match k with
  | 0sz ->
      admit ();
      change_equal_slprop
        (A.varray (A.split_r slab_region (US.mul arena_slab_region_size 0sz)))
        (A.varray (A.split_r slab_region (US.mul arena_slab_region_size k)));
      change_equal_slprop
        (A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size 0sz)))
        (A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size k)));
      change_equal_slprop
        (A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size 0sz)))
        (A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size k)));
      change_equal_slprop
        (A.varray (A.split_r md_region (US.mul arena_md_region_size 0sz)))
        (A.varray (A.split_r md_region (US.mul arena_md_region_size k)))
  | 1sz ->
      admit  ();
      init_nth_arena
        l1 l2 n1 n2 n
        arena_slab_region_size
        arena_md_region_size
        arena_md_bm_region_size
        arena_md_bm_region_b_size
        nb_arenas
        0sz
        1sz
        slab_region
        md_bm_region
        md_bm_region_b
        md_region
        size_classes
        sizes;
      sladmit ()
  | _ ->
      init_n_first_arenas
        l1 l2 n1 n2 n
        arena_slab_region_size
        arena_md_region_size
        arena_md_bm_region_size
        arena_md_bm_region_b_size
        nb_arenas
        (US.sub k 1sz)
        slab_region
        md_bm_region
        md_bm_region_b
        md_region
        size_classes
        sizes;
      init_nth_arena
        l1 l2 n1 n2 n
        arena_slab_region_size
        arena_md_region_size
        arena_md_bm_region_size
        arena_md_bm_region_b_size
        nb_arenas
        (US.sub k 1sz)
        k
        slab_region
        md_bm_region
        md_bm_region_b
        md_region
        size_classes
        sizes;
      admit ()

[@ (Comment "Test")]
let test (n: nat) = 3

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400 --split_queries no --query_stats"
val init_all_arenas
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0})
  //  US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
  //  US.fits (US.v arena_md_region_size * US.v nb_arenas)
  //})
  (slab_region: array U8.t{
    A.length slab_region == US.v arena_slab_region_size * US.v nb_arenas
  })
  (md_bm_region: array U64.t{
    A.length md_bm_region == US.v arena_md_bm_region_size * US.v nb_arenas
  })
  (md_bm_region_b: array bool{
    A.length md_bm_region_b == US.v arena_md_bm_region_b_size * US.v nb_arenas
  })
  (md_region: array AL.cell{
    A.length md_region == US.v arena_md_region_size * US.v nb_arenas
  })
  (size_classes: array size_class{
    A.length size_classes == US.v n * US.v nb_arenas
  })
  (sizes: TLA.t sc_union{
    TLA.length sizes == US.v n * US.v nb_arenas
  })
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul arena_slab_region_size 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size 0sz)) `star`
    A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size 0sz)) `star`
    A.varray (A.split_r md_region (US.mul arena_md_region_size 0sz)) `star`
    A.varray size_classes
  )
  (fun _ ->
    A.varray size_classes
  )
  (requires fun h0 ->
    array_u8_alignment (A.split_r slab_region (US.mul arena_slab_region_size 0sz)) (u32_to_sz page_size) /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul arena_slab_region_size 0sz)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul arena_md_bm_region_size 0sz)) h0) /\
    zf_b (A.asel (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size 0sz)) h0) /\
    US.v arena_slab_region_size == US.v sc_slab_region_size * US.v n /\
    hidden_pred l1 l2 n n1 n2
      arena_md_bm_region_size
      arena_md_bm_region_b_size
      arena_md_region_size
  )
  (ensures fun _ _ h1 ->
    A.length slab_region == US.v sc_slab_region_size * (US.v n * US.v nb_arenas) /\
    //Seq.length (asel size_classes h1) >= US.v n * US.v k /\
    UInt.size (US.v n * US.v nb_arenas) U32.n /\
    synced_sizes (asel size_classes h1) (US.v n * US.v nb_arenas) sizes /\
    size_class_preds (asel size_classes h1) (US.v n * US.v nb_arenas) slab_region /\
    True
  )

let init_all_arenas
  (l1:list sc)
  (l2:list sc_ex)
  (n1 n2: US.t)
  (n: US.t{
    US.v n > 0 /\
    UInt.size (US.v n) U32.n /\
    True
    //US.fits (US.v n)
  })
  (arena_slab_region_size
   arena_md_region_size
   arena_md_bm_region_size
   arena_md_bm_region_b_size: (v:US.t{US.v v > 0}))
  (nb_arenas: US.t{US.v nb_arenas > 0})
  slab_region
  md_bm_region
  md_bm_region_b
  md_region
  size_classes
  sizes
  =
  assume (
    US.fits (US.v arena_slab_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_bm_region_b_size * US.v nb_arenas) /\
    US.fits (US.v arena_md_region_size * US.v nb_arenas)
  );
  //TODO: add normalization here
  init_all_size_classes_n_first_arenas
    l1 l2 n1 n2 n
    arena_slab_region_size
    arena_md_region_size
    arena_md_bm_region_size
    arena_md_bm_region_b_size
    nb_arenas
    nb_arenas
    slab_region
    md_bm_region
    md_bm_region_b
    md_region
    size_classes
    sizes;
  drop (A.varray (A.split_r slab_region (US.mul arena_slab_region_size nb_arenas)));
  drop (A.varray (A.split_r md_bm_region (US.mul arena_md_bm_region_size nb_arenas)));
  drop (A.varray (A.split_r md_bm_region_b (US.mul arena_md_bm_region_b_size nb_arenas)));
  drop (A.varray (A.split_r md_region (US.mul arena_md_region_size nb_arenas)))

open NullOrVarray

inline_for_extraction noextract
let return_null ()
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> is_null r)
  =
  intro_null_null_or_varray #U8.t

/// Wrapper around allocate_size_class, that does not return a pair, and instead
/// always returns a valid permission on the new pointer if it is not null
inline_for_extraction noextract
val allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r -> null_or_varray r `star` size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    not (is_null r) ==> (
      A.length r == U32.v (get_u32 scs.size) /\
      array_u8_alignment r 16sz /\
      ((U32.v (get_u32 scs.size) > 0 /\ (U32.v page_size) % (U32.v (get_u32 scs.size)) == 0) ==> array_u8_alignment r (u32_to_sz (get_u32 scs.size)))
    )
  )

let allocate_size_class scs =
  //TODO
  admit ();
  let r = SizeClass.allocate_size_class scs in
  intro_vrewrite
    (if A.is_null r then emp else A.varray r)
    (null_or_varray_f r);
  return r
