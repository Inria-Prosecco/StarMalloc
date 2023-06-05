module Main

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

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
open SlabsCommon
open SteelVRefineDep
open SteelStarSeqUtils

open Config
open Utils2


#push-options  "--ide_id_info_off"
(**  Handwritten mmap functions to allocate basic data structures *)

assume val mmap_u8 (len: US.t)
  : Steel (array U8.t)
    emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v len) U8.zero
    )

assume val mmap_u64 (len: US.t)
  : Steel (array U64.t)
    emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v len) U64.zero
    )

assume val mmap_ptr_us (_:unit)
  : SteelT (R.ref US.t)
    emp
    (fun r -> R.vptr r)

assume val mmap_cell_status (len: US.t)
  : Steel (array AL.cell)
     emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a
    )

noeq
type size_class =
  {
    // The content of the sizeclass
    data : size_class_struct;
    // Mutex locking ownership of the sizeclass
    lock : L.lock (size_class_vprop data);
  }

assume val mmap_sc (len: US.t)
  : Steel (array size_class)
     emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a
    )

assume val mmap_sizes (len: US.t)
  : Steel (array sc)
     emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a
    )

/// An attribute, that will indicate that the annotated functions should be unfolded at compile-time
irreducible let reduce_attr : unit = ()

/// The normalization steps for reduction at compile-time
unfold
let normal_steps = [
      delta_attr [`%reduce_attr];
      delta_only [`%List.append];
      iota; zeta; primops]

unfold
let normal (#a:Type) (x:a) =
  Pervasives.norm normal_steps x

let ind_aux r idxs : vprop =
  SlabsCommon.ind_varraylist_aux r idxs

//#push-options "--compat_pre_core 0 --compat_pre_typed_indexed_effects"
val intro_ind_varraylist_nil (#opened:_)
  (r: A.array AL.cell)
  (r1 r2 r3 r4 r5: R.ref US.t)
  : SteelGhost unit opened
      (A.varray r `star` R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4 `star` R.vptr r5)
      (fun _ -> ind_varraylist r r1 r2 r3 r4 r5)
      (requires fun h -> A.length r == 0 /\
        R.sel r1 h == AL.null_ptr /\
        R.sel r2 h == AL.null_ptr /\
        R.sel r3 h == AL.null_ptr /\
        R.sel r4 h == AL.null_ptr /\
        R.sel r5 h == AL.null_ptr
      )
      (ensures fun _ _ _ -> True)

let intro_ind_varraylist_nil r r1 r2 r3 r4 r5 =
  ALG.intro_arraylist_nil
    pred1 pred2 pred3 pred4 pred5
    r
    AL.null_ptr AL.null_ptr AL.null_ptr AL.null_ptr AL.null_ptr;
  let idxs = gget (R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4 `star` R.vptr r5) in
  intro_vrefine
    (SlabsCommon.ind_varraylist_aux2 r ((((AL.null_ptr, AL.null_ptr), AL.null_ptr), AL.null_ptr), AL.null_ptr))
    (SlabsCommon.ind_varraylist_aux_refinement r ((((AL.null_ptr, AL.null_ptr), AL.null_ptr), AL.null_ptr), AL.null_ptr));
  intro_vdep
    (R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4 `star` R.vptr r5)
    (SlabsCommon.ind_varraylist_aux r ((((AL.null_ptr, AL.null_ptr), AL.null_ptr), AL.null_ptr), AL.null_ptr))
    (ind_aux r)

val intro_left_vprop_empty (#opened:_)
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r1 r2 r3 r4 r5: R.ref US.t)
  : SteelGhost unit opened
      (A.varray (split_l md_region 0sz) `star` R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4 `star` R.vptr r5)
      (fun _ -> SlabsCommon.left_vprop sc slab_region md_bm_region md_region r1 r2 r3 r4 r5 0sz)
      (requires fun h ->
        R.sel r1 h == AL.null_ptr /\
        R.sel r2 h == AL.null_ptr /\
        R.sel r3 h == AL.null_ptr /\
        R.sel r4 h == AL.null_ptr /\
        R.sel r5 h == AL.null_ptr
      )
      (ensures fun _ _ _ -> True)

#push-options "--z3rlimit 30"
let intro_left_vprop_empty sc slab_region md_bm_region md_region r1 r2 r3 r4 r5 =
  intro_ind_varraylist_nil
    (A.split_l md_region 0sz)
    r1 r2 r3 r4 r5;

  let s = gget (ind_varraylist
      (A.split_l md_region 0sz)
      r1 r2 r3 r4 r5) in

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
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 r5 0sz s))
  by (norm [delta_only [`%left_vprop_aux]]);


  change_equal_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v 0sz})
      #(t sc)
      (f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz)))
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 r5 0sz s);

  intro_vdep
    (ind_varraylist
      (A.split_l md_region 0sz)
      r1 r2 r3 r4 r5)
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 r5 0sz s)
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 r5 0sz)

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

#restart-solver

let vrefinedep_ext
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f f': ( (t_of (vrefine v p)) -> Tot vprop))
  : Lemma (requires f == f') (ensures vrefinedep v p f == vrefinedep v p f')
  = ()

#restart-solver

#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects --fuel 0 --ifuel 0"
noextract inline_for_extraction
let init_struct_aux
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region == U32.v page_size * US.v metadata_max})
  (md_bm_region: array U64.t{A.length md_bm_region == US.v 4sz * US.v metadata_max})
  (md_region: array AL.cell{A.length md_region == US.v metadata_max})
  : Steel size_class_struct
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop scs)
  (requires fun h0 ->
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0)
  )
  (ensures fun _ r h1 ->
    U32.eq r.size sc /\
    //zf_u8 (A.asel (A.split_l slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) (US.sub n 1sz))) h1) /\
    //zf_u64 (A.asel (A.split_l md_bm_region (US.mul (US.mul metadata_max 4sz) (US.sub n 1sz))) h1) /\
    r.slab_region == slab_region /\
    r.md_bm_region == md_bm_region /\
    r.md_region == md_region /\
    True
  )
  =
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

  let ptr_partial = mmap_ptr_us () in
  let ptr_empty = mmap_ptr_us () in
  let ptr_full = mmap_ptr_us () in
  let ptr_guard = mmap_ptr_us () in
  let ptr_quarantine = mmap_ptr_us () in

  R.write ptr_partial AL.null_ptr;
  R.write ptr_empty AL.null_ptr;
  R.write ptr_full AL.null_ptr;
  R.write ptr_guard AL.null_ptr;
  R.write ptr_quarantine AL.null_ptr;

  intro_left_vprop_empty sc
    slab_region md_bm_region md_region
    ptr_empty ptr_partial ptr_full ptr_guard ptr_quarantine;

  let md_count = mmap_ptr_us () in
  R.write md_count 0sz;

  intro_vrefinedep
    (R.vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux sc
      slab_region md_bm_region md_region
      ptr_empty ptr_partial ptr_full ptr_guard ptr_quarantine)
    (left_vprop sc slab_region md_bm_region md_region
         ptr_empty ptr_partial ptr_full ptr_guard ptr_quarantine 0sz `star`
     right_vprop slab_region md_bm_region md_region 0sz);


  [@inline_let]
  let scs = {
    size = sc;
    partial_slabs = ptr_partial;
    empty_slabs = ptr_empty;
    full_slabs = ptr_full;
    guard_slabs = ptr_guard;
    quarantine_slabs = ptr_quarantine;
    slab_region = slab_region;
    md_bm_region = md_bm_region;
    md_region = md_region;
    md_count = md_count;
  } in

  change_slprop_rel
    (vrefinedep
      (R.vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux sc
        slab_region md_bm_region md_region
        ptr_empty ptr_partial ptr_full ptr_guard ptr_quarantine))
     (size_class_vprop scs)
    (fun _ _ -> True)
    (fun _ ->
      let open FStar.Tactics in
      assert (
        size_class_vprop scs
        ==
        vrefinedep
          (R.vptr scs.md_count)
          vrefinedep_prop
          (size_class_vprop_aux scs.size
            scs.slab_region scs.md_bm_region scs.md_region
            scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs scs.quarantine_slabs)
      ) by (norm [delta_only [`%size_class_vprop]]; trefl ())
    );
  return scs

#restart-solver

//#push-options "--split_queries always --query_stats"
#push-options "--z3rlimit 100"
noextract inline_for_extraction
let init_struct
  (n: US.t{
    US.v n > 0 /\
    US.fits (US.v metadata_max * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.v metadata_max * US.v (u32_to_sz page_size) <= US.v metadata_max * US.v (u32_to_sz page_size) * US.v n /\
    US.v metadata_max * US.v 4sz <= US.v metadata_max * US.v 4sz * US.v n /\
    US.v metadata_max <= US.v metadata_max * US.v n
  })
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region == U32.v page_size * US.v metadata_max * US.v n})
  (md_bm_region: array U64.t{A.length md_bm_region == US.v 4sz * US.v metadata_max * US.v n})
  (md_region: array AL.cell{A.length md_region == US.v metadata_max * US.v n})
  : Steel size_class_struct
  (
    A.varray slab_region `star`
    A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop scs `star`
    A.varray (A.split_r slab_region (US.mul metadata_max (u32_to_sz page_size))) `star`
    A.varray (A.split_r md_bm_region (US.mul metadata_max 4sz)) `star`
    A.varray (A.split_r md_region metadata_max)
  )
  (requires fun h0 ->
    zf_u8 (A.asel slab_region h0) /\
    zf_u64 (A.asel md_bm_region h0)
  )
  (ensures fun _ r h1 ->
    U32.eq r.size sc /\
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
  let scs = init_struct_aux sc slab_region' md_bm_region' md_region' in
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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

noextract inline_for_extraction
val init_wrapper2
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
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    True
  )
  (ensures fun _ r h1 ->
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) h1) /\
    U32.eq r.data.size sc /\
    same_base_array slab_region r.data.slab_region /\
    A.offset (A.ptr_of r.data.slab_region) == A.offset (A.ptr_of slab_region) + US.v metadata_max * US.v (u32_to_sz page_size) * US.v k
  )

#restart-solver

#push-options "--z3rlimit 200 --query_stats --split_queries always"

let init_wrapper2 sc n k k' slab_region md_bm_region md_region
  =
  f_lemma n k;
  f_lemma n k';
  f_lemma n (US.sub n k);
  let data = init_struct (US.sub n k) sc
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
  assert (A.offset (A.ptr_of data.slab_region) == A.offset (A.ptr_of slab_region) + US.v metadata_max * US.v (u32_to_sz page_size) * US.v k);
  let lock = L.new_lock (size_class_vprop data) in
  let sc = {data; lock} in
  return sc

#pop-options

module G = FStar.Ghost
module UP = FStar.PtrdiffT

let slab_region_size
  : v:US.t{
    US.v v == US.v metadata_max * U32.v page_size * US.v nb_size_classes * US.v nb_arenas /\
    UP.fits (US.v v)
  }
  =
  metadata_max_up_fits ();
  slab_size `US.mul` nb_size_classes `US.mul` nb_arenas

open ROArray

unfold
let size_class_pred (slab_region:array U8.t) (sc:size_class) (i:nat) : prop =
  same_base_array slab_region sc.data.slab_region /\
  A.offset (A.ptr_of sc.data.slab_region) == A.offset (A.ptr_of slab_region) + i * US.v slab_size

[@@ reduce_attr]
inline_for_extraction noextract
let sc_list : (l:list sc{List.length l == US.v nb_size_classes})
  = [@inline_let] let l = [16ul; 32ul; 64ul; 128ul; 256ul; 512ul; 1024ul; 2048ul; 4096ul] in
    assert_norm (List.length l == 9);
    l

/// A logical predicate indicating that a list of sizes corresponds
/// to the sizes of a list of size_classes
let synced_sizes (#n:nat) (k:nat{k <= n}) (sizes:Seq.lseq sc n) (size_classes:Seq.lseq size_class n) : prop =
  forall (i:nat{i < k}). Seq.index sizes i == (Seq.index size_classes i).data.size

/// The total number of size classes in the allocator, across all arenas.
/// Used as an abbreviation for specification purposes
inline_for_extraction noextract
let total_nb_sc : n:nat{n == US.v nb_size_classes * US.v nb_arenas} = 36

/// Number of arenas as a nat, for specification purposes. Not relying on US.v
/// allows better normalization for extraction
[@@ reduce_attr]
inline_for_extraction noextract
let nb_arenas_nat : n:nat{n == US.v nb_arenas} = 4

/// Duplicating the list of size_classes sizes for each arena, which enables a simpler
/// initialization directly using the mechanism in place for one arena
[@@ reduce_attr]
inline_for_extraction noextract
let rec arena_sc_list' (i:nat{i <= US.v nb_arenas}) (acc:list sc{List.length acc = i * US.v nb_size_classes}) :
  Tot (l:list sc{List.length l == total_nb_sc}) (decreases (US.v nb_arenas - i))
  = if i = nb_arenas_nat then acc
    else (
      List.append_length acc sc_list;
      arena_sc_list' (i + 1) (acc `List.append` sc_list)
    )

/// Fuel needed to establish that the length of [] is 0
#push-options "--fuel 1"
[@@ reduce_attr]
inline_for_extraction noextract
let arena_sc_list : (l:list sc{List.length l == total_nb_sc /\ Cons? l}) = arena_sc_list' 0 []
#pop-options

/// This gathers all the data for small allocations.
/// In particular, it contains an array with all size_classes data,
/// as well as the slab_region containing the actual memory
noeq
type size_classes_all =
  { size_classes : sc:array size_class{length sc == total_nb_sc}; // The array of size_classes
    sizes : sz:array sc{length sz == total_nb_sc}; // An array of the sizes of [size_classes]
    g_size_classes: Ghost.erased (Seq.lseq size_class (length size_classes)); // The ghost representation of size_classes
    g_sizes: Ghost.erased (Seq.lseq sc (length sizes)); // The ghost representation of sizes
    ro_perm: ro_array size_classes g_size_classes; // The read-only permission on size_classes
    ro_sizes: ro_array sizes g_sizes;
    slab_region: arr:array U8.t{ // The region of memory handled by this size class
      synced_sizes total_nb_sc g_sizes g_size_classes /\
      A.length arr == US.v slab_region_size /\
      (forall (i:nat{i < Seq.length g_size_classes}).
        size_class_pred arr (Seq.index g_size_classes i) i)
    }
  }

/// Performs the initialization of one size class of length [size_c], and stores it in the
/// size_classes array at index [k]
val init_size_class
  (size_c: sc)
  (n: US.t{
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
  (sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k)) `star`
    A.varray size_classes `star`
    A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k')) `star`
    A.varray size_classes `star`
    A.varray sizes
  )
  (requires fun h0 ->
    US.v k' == US.v k + 1 /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    synced_sizes (US.v k) (asel sizes h0) (asel size_classes h0) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k')) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k')) h1) /\
    synced_sizes (US.v k') (asel sizes h1) (asel size_classes h1) /\
    (forall (i:nat{i <= US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

let init_size_class size n k k' slab_region md_bm_region md_region size_classes sizes =
  (**) let g0 = gget (varray size_classes) in
  (**) let g_sizes0 = gget (varray sizes) in
  f_lemma n k;
  upd sizes k size;
  let sc = init_wrapper2 size n k k' slab_region md_bm_region md_region in
  upd size_classes k sc;

  (**) let g1 = gget (varray size_classes) in
  (**) let g_sizes1 = gget (varray sizes) in
  (**) assert (Ghost.reveal g_sizes1 == Seq.upd (Ghost.reveal g_sizes0) (US.v k) size);
  (**) assert (Ghost.reveal g1 == Seq.upd (Ghost.reveal g0) (US.v k) sc)

/// Wrapper around `init_size_class`. It takes as argument a list [l] of sizes
/// for size classes to be created, creates them, and stores them in order in
/// the [size_classes] array. Note, this function should not be extracted as is,
/// it will be reduced at compile-time to yield an idiomatic sequence of calls
/// to `init_size_class`
[@@ reduce_attr]
noextract
val init_size_classes_aux (l:list sc)
  (n: US.t{
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
  (sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max k)) `star`
    A.varray size_classes `star`
    A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max n)) `star`
    A.varray size_classes `star`
    A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    US.v k + List.length l == US.v n /\
    Cons? l /\

    US.v k' == US.v k + 1 /\
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) k)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) k)) h0) /\
    synced_sizes (US.v k) (asel sizes h0) (asel size_classes h0) /\
    (forall (i:nat{i < US.v k}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    synced_sizes (US.v n) (asel sizes h1) (asel size_classes h1) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

/// Small non-linear arithmetic lemma to help with proof obligations below
let lemma_mul_le (a b c c':nat) : Lemma (requires c <= c') (ensures a * b * c <= a * b * c')
  = ()

#restart-solver
// We need to bump the fuel to reason about the length of the lists
#push-options "--z3rlimit 300 --fuel 2 --ifuel 2 --query_stats"
let rec init_size_classes_aux l n k k' slab_region md_bm_region md_region size_classes sizes = match l with
  | [hd] ->
      assert (US.v k' == US.v n);
      init_size_class hd n k k' slab_region md_bm_region md_region size_classes sizes;
      // Need to rewrite the k' into n to satisfy the postcondition
      change_equal_slprop (A.varray (split_r md_bm_region _)) (A.varray (split_r md_bm_region _));
      change_equal_slprop (A.varray (split_r md_region _)) (A.varray (split_r md_region _));
      change_equal_slprop (A.varray (split_r slab_region _)) (A.varray (split_r slab_region _))
  | hd::tl ->
      init_size_class hd n k k' slab_region md_bm_region md_region size_classes sizes;
      // This proof obligation in the recursive call seems especially problematic.
      // The call to the lemma alleviates the issue, we might need something similar for
      // the md_region and md_bm_region in the future
      assert (US.v (k' `US.add` 1sz) <= US.v n);
      lemma_mul_le (US.v metadata_max) (US.v (u32_to_sz page_size)) (US.v (k' `US.add` 1sz)) (US.v n);
      lemma_mul_le (US.v metadata_max) (US.v 4sz) (US.v (k' `US.add` 1sz)) (US.v n);
      init_size_classes_aux tl n k' (k' `US.add` 1sz) slab_region md_bm_region md_region size_classes sizes
#pop-options

/// Entrypoint, allocating all size classes according to the list of sizes [l]
inline_for_extraction noextract
val init_size_classes (l:list sc)
  (n: US.t{
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
  (sizes: array sc{A.length sizes == US.v n})
  : Steel unit
  (
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max 0sz)) `star`
    A.varray size_classes `star`
    A.varray sizes
  )
  (fun r ->
    A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) `star`
    A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) `star`
    A.varray (A.split_r md_region (US.mul metadata_max n)) `star`
    A.varray size_classes `star`
    A.varray sizes
  )
  (requires fun h0 ->
    // Invariant needed to link the list against the size classes
    // allocated in previous iterations
    List.length l == US.v n /\
    Cons? l /\

    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) h0) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) h0) /\
    synced_sizes 0 (asel sizes h0) (asel size_classes h0) /\
    (forall (i:nat{i < 0}) . size_class_pred slab_region (Seq.index (asel size_classes h0) i) i)
  )
  (ensures fun _ r h1 ->
    zf_u8 (A.asel (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) n)) h1) /\
    zf_u64 (A.asel (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) n)) h1) /\
    synced_sizes (US.v n) (asel sizes h1) (asel size_classes h1) /\
    (forall (i:nat{i < US.v n}) . size_class_pred slab_region (Seq.index (asel size_classes h1) i) i)
  )

let init_size_classes l n slab_region md_bm_region md_region size_classes sizes =
  (normal (init_size_classes_aux l n 0sz 1sz)) slab_region md_bm_region md_region size_classes sizes

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
let init
  (_:unit)
  : SteelTop size_classes_all false
  (fun _ -> emp)
  (fun _ r _ -> True)
  =
  [@inline_let]
  let n = nb_size_classes `US.mul` nb_arenas in
  assert (
    US.v n > 0 /\ US.v n >= US.v 1sz /\
    US.v n == total_nb_sc /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size)) /\
    US.fits (US.v metadata_max * US.v 4sz) /\
    US.fits (US.v metadata_max * US.v (u32_to_sz page_size) * US.v n) /\
    US.fits (US.v metadata_max * US.v 4sz * US.v n) /\
    US.fits (US.v metadata_max * US.v n) /\
    True
  );
  let slab_region = mmap_u8 (US.mul (US.mul metadata_max (u32_to_sz page_size)) n) in
  let md_bm_region = mmap_u64 (US.mul (US.mul metadata_max 4sz) n) in
  let md_region = mmap_cell_status (US.mul metadata_max n) in

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

  assert (A.length (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n);
  assert (A.length (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) == US.v metadata_max * 4 * US.v n);
  assert (A.length (A.split_r md_region (US.mul metadata_max 0sz)) == US.v metadata_max * US.v n);

  let size_classes = mmap_sc n in
  let sizes = mmap_sizes n in

  init_size_classes arena_sc_list n slab_region md_bm_region md_region size_classes sizes;

  let g_size_classes = gget (varray size_classes) in
  let g_sizes = gget (varray sizes) in

  let ro_perm = create_ro_array size_classes g_size_classes in
  let ro_sizes = create_ro_array sizes g_sizes in

  drop (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size))
    n)));
  drop (A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz)
    n)));
  drop (A.varray (A.split_r md_region (US.mul metadata_max
   n)));

  [@inline_let]
  let s : size_classes_all = {
    size_classes;
    sizes;
    g_size_classes;
    g_sizes;
    ro_perm;
    ro_sizes;
    slab_region;
  } in
  return s

#reset-options "--fuel 1 --ifuel 1"

#push-options "--print_implicits"

#push-options "--warn_error '-272'"
let sc_all : size_classes_all = init ()
#pop-options

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
  (ensures fun h0 r h1 -> not (is_null r) ==> A.length r == U32.v scs.size)

let allocate_size_class scs =
  let r = SizeClass.allocate_size_class scs in
  intro_vrewrite
    (if A.is_null r then emp else A.varray r)
    (null_or_varray_f r);
  return r

#restart-solver

#push-options "--fuel 0 --ifuel 0 --query_stats"
inline_for_extraction noextract
let slab_malloc_one (i:US.t{US.v i < total_nb_sc}) (bytes: U32.t)
  : Steel
  (array U8.t)
  emp (fun r -> null_or_varray r)
  (requires fun _ ->
    U32.v bytes <= U32.v (Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size
  )
  (ensures fun _ r _ ->
    not (is_null r) ==> (
      A.length r == U32.v (Seq.index (G.reveal sc_all.g_size_classes) (US.v i)).data.size /\
      A.length r >= U32.v bytes
  ))
  =
  let sc = index sc_all.ro_perm i in
  L.acquire sc.lock;
  let sc = index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  let ptr = allocate_size_class sc.data in
  let sc = index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  L.release sc.lock;
  return ptr
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// A wrapper around slab_malloc' that performs dispatch in the size classes
/// for arena [arena_id] in a generic way.
/// The list argument is not actually used, it just serves
/// as a counter that reduces better than nats
[@@ reduce_attr]
noextract
let rec slab_malloc_i
  (l:list sc{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      Seq.length s >= 2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = index sc_all.ro_sizes idx in
      if bytes `U32.lte` size then
        slab_malloc_one idx bytes
      else
        slab_malloc_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// A variant of slab_malloc_i adding slab canaries
[@@ reduce_attr]
noextract
let rec slab_malloc_canary_i
  (l:list sc{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      Seq.length s >= 2 /\
      Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length r - 1) == slab_canaries_magic2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = index sc_all.ro_sizes idx in
      if bytes `U32.lte` (size `U32.sub` 2ul) then
        let ptr = slab_malloc_one idx bytes in
        if is_null ptr then return ptr
        else (
          elim_live_null_or_varray ptr;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) slab_canaries_magic1;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) slab_canaries_magic2;
          intro_live_null_or_varray ptr;
          return ptr
        )
      else
        slab_malloc_canary_i tl (i `US.add` 1sz) arena_id bytes
#pop-options

module T = FStar.Tactics

/// A variant of the normalization, with a zeta full to reduce under
/// matches (and if/then/else). To use with care, as zeta_full can
/// loop and lead to stack overflows
let norm_full () : T.Tac unit =
  T.norm [zeta_full; iota; primops; delta_attr [`%reduce_attr]];
  T.trefl ()

[@@ T.postprocess_with norm_full]
val slab_malloc (arena_id:US.t{US.v arena_id < US.v nb_arenas}) (bytes:U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      Seq.length s >= 2 /\
      (enable_slab_canaries ==>
        Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length r - 1) == slab_canaries_magic2
      )
    )
  )

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_malloc arena_id bytes =
  if enable_slab_canaries then
    (slab_malloc_canary_i sc_list 0sz) arena_id bytes
  else
    (slab_malloc_i sc_list 0sz) arena_id bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// `slab_aligned_alloc` works in a very similar way as `slab_malloc_i`
/// The key difference lies in the condition of the if-branch: we only
/// attempt to allocate in this size class if it satisfies the alignment
/// constraint, i.e., alignment % size == 0
[@@ reduce_attr]
noextract
let rec slab_aligned_alloc_i
  (l:list sc{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (alignment:U32.t)
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      Seq.length s >= 2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = index sc_all.ro_sizes idx in
      if bytes `U32.lte` size && alignment `U32.rem` size = 0ul then
        slab_malloc_one idx bytes
      else
        slab_aligned_alloc_i tl (i `US.add` 1sz) arena_id alignment bytes
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
/// Version of `slab_aligned_alloc_i` with slab canaries
[@@ reduce_attr]
noextract
let rec slab_aligned_alloc_canary_i
  (l:list sc{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == US.v nb_size_classes})
  (arena_id:US.t{US.v arena_id < US.v nb_arenas})
  (alignment:U32.t)
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      Seq.length s >= 2 /\
      Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
      Seq.index s (A.length r - 1) == slab_canaries_magic2
    )
  )
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      [@inline_let] let idx = (arena_id `US.mul` nb_size_classes) `US.add` i in
      let size = index sc_all.ro_sizes idx in
      if bytes `U32.lte` (size `U32.sub` 2ul) && alignment `U32.rem` size = 0ul then
        let ptr = slab_malloc_one idx bytes in
        if is_null ptr then return ptr
        else (
          elim_live_null_or_varray ptr;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) slab_canaries_magic1;
          upd ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) slab_canaries_magic2;
          intro_live_null_or_varray ptr;
          return ptr
        )
      else
        slab_aligned_alloc_canary_i tl (i `US.add` 1sz) arena_id alignment bytes
#pop-options

[@@ T.postprocess_with norm_full]
val slab_aligned_alloc (arena_id:US.t{US.v arena_id < US.v nb_arenas}) (alignment:U32.t) (bytes:U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r h1 ->
    let s : t_of (null_or_varray r)
      = h1 (null_or_varray r) in
    not (is_null r) ==> (
      A.length r >= U32.v bytes /\
      Seq.length s >= 2 /\
      (enable_slab_canaries ==>
        Seq.index s (A.length r - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length r - 1) == slab_canaries_magic2
      )
    )
  )

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let slab_aligned_alloc arena_id alignment bytes =
  if enable_slab_canaries then
    (slab_aligned_alloc_canary_i sc_list 0sz) arena_id alignment bytes
  else
    (slab_aligned_alloc_i sc_list 0sz) arena_id alignment bytes
#pop-options

inline_for_extraction noextract
let slab_free' (i:US.t{US.v i < US.v nb_size_classes * US.v nb_arenas}) (ptr: array U8.t) (diff: US.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun h0 ->
    let sc = Seq.index (G.reveal sc_all.g_size_classes) (US.v i) in
    let diff' = offset (ptr_of ptr) - offset (ptr_of sc.data.slab_region) in
    same_base_array ptr sc.data.slab_region /\
    0 <= diff' /\
    diff' < US.v slab_size /\
    US.v diff = diff')
  (ensures fun h0 _ h1 -> True)
  =
  let sc = ROArray.index sc_all.ro_perm i in
  L.acquire sc.lock;
  let sc = ROArray.index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  let res = deallocate_size_class sc.data ptr diff in
  let sc = ROArray.index sc_all.ro_perm i in
  change_equal_slprop (size_class_vprop _) (size_class_vprop _);
  L.release sc.lock;
  return res

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

#restart-solver

// within_bounds model is awkward, am I just tired?
let slab_getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (fun _ ->
   A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (requires fun _ ->
    //let x = offset (ptr_of ptr) - offset (ptr_of sc_all.slab_region) in
    //((x >= 0 /\ x < US.v slab_region_size) ==> (
    //  (let y = x / US.v slab_size in
    //  0 <= y /\ y < Seq.length sc_all.g_sizes /\
    //  (let sc = Seq.index sc_all.g_sizes y in
    //    (x % US.v slab_size) % (U32.v sc) == 0
    //    ==>
    //    A.length ptr == U32.v sc
    //  ))
    //))
    ///\
    SAA.within_bounds
      (A.split_l (G.reveal sc_all.slab_region) 0sz)
      ptr
      (A.split_r (G.reveal sc_all.slab_region) slab_region_size)
  )
  (ensures fun h0 r h1 ->
    A.asel ptr h1 == A.asel ptr h0 /\
    (r <> 0sz ==>
      (enable_slab_canaries ==>
        A.length ptr == US.v r + 2
      ) /\
      (not enable_slab_canaries ==>
        A.length ptr == US.v r
      )
    )
  )
  =
  SAA.within_bounds_elim
    (A.split_l sc_all.slab_region 0sz)
    (A.split_r sc_all.slab_region slab_region_size)
    ptr;
  UP.fits_lt
    (A.offset (A.ptr_of ptr)
    -
    A.offset (A.ptr_of (A.split_l sc_all.slab_region 0sz)))
    (US.v slab_region_size);
  let diff = A.ptrdiff
    ptr
    (A.split_l sc_all.slab_region 0sz) in
  let diff_sz = UP.ptrdifft_to_sizet diff in
  assert (US.v slab_size > 0);
  let index = US.div diff_sz slab_size in
  let rem = US.rem diff_sz slab_size in
  let size = ROArray.index sc_all.ro_sizes index in
  // some refactor needed wrt SlotsFree
  if US.rem rem (US.uint32_to_sizet size) = 0sz then (
    // TODO: remove assume
    // thanks to the ugly precondition
    assume (A.length ptr == U32.v size);
    if enable_slab_canaries then
      return (US.uint32_to_sizet (size `U32.sub` 2ul))
    else
      return (US.uint32_to_sizet size)
  ) else (
    // invalid pointer
    return 0sz
  )

val slab_free (ptr:array U8.t)
  : Steel bool
  (A.varray ptr `star`
    A.varray (A.split_l sc_all.slab_region 0sz))
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    A.varray (A.split_l sc_all.slab_region 0sz))
  (requires fun _ -> SAA.within_bounds
    (A.split_l (G.reveal sc_all.slab_region) 0sz)
    ptr
    (A.split_r (G.reveal sc_all.slab_region) slab_region_size)
  )
  (ensures fun h0 r _ ->
    let s = A.asel ptr h0 in
    enable_slab_canaries ==>
      (r ==>
        A.length ptr >= 2 /\
        Seq.index s (A.length ptr - 2) == slab_canaries_magic1 /\
        Seq.index s (A.length ptr - 1) == slab_canaries_magic2
      )
  )

let slab_free ptr =
  SAA.within_bounds_elim
    (A.split_l sc_all.slab_region 0sz)
    (A.split_r sc_all.slab_region slab_region_size)
    ptr;
  UP.fits_lt
    (A.offset (A.ptr_of ptr)
    -
    A.offset (A.ptr_of (A.split_l sc_all.slab_region 0sz)))
    (US.v slab_region_size);
  let diff = A.ptrdiff
    ptr
    (A.split_l sc_all.slab_region 0sz) in
  let diff_sz = UP.ptrdifft_to_sizet diff in
  assert (ptr_of (A.split_l sc_all.slab_region 0sz) == ptr_of (sc_all.slab_region));
  assert (US.v slab_size > 0);
  let index = US.div diff_sz slab_size in
  let rem = US.rem diff_sz slab_size in
  (**) let g_sc = G.hide (Seq.index (G.reveal sc_all.g_size_classes) (US.v index)) in
  (**) assert (size_class_pred sc_all.slab_region (G.reveal g_sc) (US.v index));
  let size = ROArray.index sc_all.ro_sizes index in
  // some refactor needed wrt SlotsFree
  if US.rem rem (US.uint32_to_sizet size) <> 0sz then (
    return false
  ) else (
    if enable_slab_canaries then (
      // The client needs to provide the full array back when deallocating.
      // If so, it corresponds to a slot in the size class
      // TODO: add proper precondition @Aymeric,
      // with the alignment property!
      assume (length ptr == U32.v size);
      let magic1 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 2ul)) in
      let magic2 = A.index ptr (US.uint32_to_sizet (size `U32.sub` 1ul)) in
      if magic1 = slab_canaries_magic1 && magic2 = slab_canaries_magic2 then
        slab_free' index ptr rem
      else
        // Canary was overwritten
        return false
    ) else (
      slab_free' index ptr rem
    )
  )
