module SizeClass

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module US = FStar.SizeT

module G = FStar.Ghost

module SL = BlobList

module P = Steel.FractionalPermission
module SM = Steel.Memory
module A = Steel.Array

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

open Utils2
open Slabs

#push-options "--ide_id_info_off"

//TODO: remove blob, use ptrdiff style
//TODO: improve max_sc bound, use better spec'ed ffs64

open FStar.Mul
noeq
type size_class_struct = {
  size: sc;
  partial_slabs: ref SL.t;
  empty_slabs: ref SL.t;
  full_slabs: ref SL.t;
  md_count: ref U32.t;
  slab_region: slab_region:array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size};
  //TODO: duplicata due to karamel extraction issue
  md_bm_region: md_bm_region:array U64.t{A.length md_bm_region = U32.v metadata_max * 4};
  md_region: md_region:array SL.cell{A.length md_region = U32.v metadata_max};
  //lock: ref bool;
}

[@@erasable]
noeq
type blob2 = {
  scs_v: size_class_struct;
  partial_slabs_v: list SL.blob;
  empty_slabs_v: list SL.blob;
  full_slabs_v: list SL.blob;
  md_count_v: U32.t;
  slab_region_v: Seq.seq U8.t;
  md_bm_region_v: Seq.seq U64.t;
  md_region_v: Seq.seq SL.cell;
}

open SteelVRefineDep

let size_class_vprop_aux
  (scs: size_class_struct)
  : vprop
  =
  SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
  SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
  SL.ind_llist (p_full scs.size) scs.full_slabs `star`
  vrefinedep
    (vptr scs.md_count)
    //TODO: hideous coercion
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
      (A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `vrefine` zf_u64) `star`
      A.varray (A.split_r scs.md_region (u32_to_sz v))
    )

let size_class_vprop
  (r: ref size_class_struct)
  : vprop
  =
  vdep
    (vptr r)
    (fun scs -> size_class_vprop_aux scs)

let size_class_vprop_test
  (r: ref size_class_struct)
  : Steel unit
  (size_class_vprop r)
  (fun _ -> size_class_vprop r)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 ->
    h0 (size_class_vprop r)
    ==
    h1 (size_class_vprop r)
  )
  =
  let x = elim_vdep (vptr r) (fun scs -> size_class_vprop_aux scs) in
  intro_vdep
    (vptr r)
    (size_class_vprop_aux (G.reveal x))
    (fun scs -> size_class_vprop_aux scs);
  admit ()


let allocate_size_class_sl_lemma1
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (size_class_vprop_aux scs)) m
  )
  (ensures
    SM.interp (hp_of (
      SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
      SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
      SL.ind_llist (p_full scs.size) scs.full_slabs `star`
      vrefinedep
        (vptr scs.md_count)
        //TODO: hideous coercion
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
          A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
          A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
          A.varray (A.split_r scs.md_region (u32_to_sz v))
        )
    )) m /\
    sel_of (size_class_vprop_aux scs) m
    ==
    sel_of (
      SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
      SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
      SL.ind_llist (p_full scs.size) scs.full_slabs `star`
      vrefinedep
        (vptr scs.md_count)
        //TODO: hideous coercion
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
          A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
          A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
          A.varray (A.split_r scs.md_region (u32_to_sz v))
        )
    ) m
  )
  = ()

let allocate_size_class_sl_lemma2
  (scs: size_class_struct)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
      SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
      SL.ind_llist (p_full scs.size) scs.full_slabs `star`
      vrefinedep
        (vptr scs.md_count)
        //TODO: hideous coercion
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
          A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
          A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
          A.varray (A.split_r scs.md_region (u32_to_sz v))
        )
    )) m
  )
  (ensures
    SM.interp (hp_of (size_class_vprop_aux scs)) m /\
    sel_of (size_class_vprop_aux scs) m
    ==
    sel_of (
      SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
      SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
      SL.ind_llist (p_full scs.size) scs.full_slabs `star`
      vrefinedep
        (vptr scs.md_count)
        //TODO: hideous coercion
        (fun x -> U32.v x <= U32.v metadata_max == true)
        (fun v ->
          A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
          A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
          A.varray (A.split_r scs.md_region (u32_to_sz v))
        )
    ) m
  )
  = ()

#push-options "--z3rlimit 100 --query_stats --compat_pre_typed_indexed_effects"
let allocate_size_class
  (ptr: ref size_class_struct)
  : Steel (array U8.t & G.erased bool)
  (size_class_vprop ptr)
  (fun r ->
    (if (G.reveal (snd r)) then A.varray (fst r) else emp) `star`
    size_class_vprop ptr)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  let scs' = elim_vdep
    (vptr ptr)
    (fun scs -> size_class_vprop_aux scs) in
  let scs : size_class_struct = read ptr in
  change_equal_slprop
    (size_class_vprop_aux (G.reveal scs'))
    (size_class_vprop_aux scs);
  change_slprop_rel
    (size_class_vprop_aux scs)
    (SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
    SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
    SL.ind_llist (p_full scs.size) scs.full_slabs `star`
    vrefinedep
      (vptr scs.md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r scs.md_region (u32_to_sz v))
      )
    )
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let result = allocate_slab
    scs.size scs.partial_slabs scs.empty_slabs scs.full_slabs
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count in
  change_slprop_rel
    (SL.ind_llist (p_partial scs.size) scs.partial_slabs `star`
    SL.ind_llist (p_empty scs.size) scs.empty_slabs `star`
    SL.ind_llist (p_full scs.size) scs.full_slabs `star`
    vrefinedep
      (vptr scs.md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r scs.slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r scs.md_region (u32_to_sz v))
      )
    )
    (size_class_vprop_aux scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  intro_vdep
    (vptr ptr)
    (size_class_vprop_aux scs)
    (fun scs -> size_class_vprop_aux scs);
  return result
