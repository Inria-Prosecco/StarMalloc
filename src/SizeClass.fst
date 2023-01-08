module SizeClass

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

module G = FStar.Ghost

module SL = Selectors.LList

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
  partial_slabs: ref (SL.t blob);
  empty_slabs: ref (SL.t blob);
  full_slabs: ref (SL.t blob);
  md_count: ref U32.t;
  slab_region: slab_region:array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size};
  //TODO: duplicata due to karamel extraction issue
  md_bm_region: md_bm_region:array U64.t{A.length md_bm_region = U32.v metadata_max * 4};
  md_region: md_region:array (SL.cell blob){A.length md_region = U32.v metadata_max};
  //lock: ref bool;
}

noeq
type blob2 = {
  scs_v: size_class_struct;
  partial_slabs_v: list blob;
  empty_slabs_v: list blob;
  full_slabs_v: list blob;
  md_count_v: U32.t;
  slab_region_v: Seq.seq U8.t;
  md_bm_region_v: Seq.seq U64.t;
  md_region_v: Seq.seq (SL.cell blob);
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
      A.varray (A.split_r scs.md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
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


#push-options "--z3rlimit 50"
let allocate_size_class
  (r: ref size_class_struct)
  //: Steel unit
  : Steel (array U8.t)
  (size_class_vprop r)
  (fun result ->
    A.varray result `star`
    size_class_vprop r)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  let scs' = elim_vdep
    (vptr r)
    (fun scs -> size_class_vprop_aux scs) in
  let scs = read r in
  change_slprop_rel
    (size_class_vprop_aux (G.reveal scs'))
    (size_class_vprop_aux scs)
    (fun x y -> x == y)
    (fun _ -> admit ());
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
    (fun _ -> admit ());
  let result = allocate_slab
    scs.size scs.partial_slabs scs.empty_slabs scs.full_slabs
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count in
  sladmit ();
  //intro_vdep
  //  (vptr r)
  //  (size_class_vprop_aux scs)
  //  (fun scs -> size_class_vprop_aux scs);
  return result
