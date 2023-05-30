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

#push-options "--z3rlimit 200 --query_stats"

let init_wrapper2 sc n k k' slab_region md_bm_region md_region
  =
  admit();
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
    US.v v = US.v metadata_max * U32.v page_size * 9 /\
    UP.fits (US.v v)
  }
  =
  metadata_max_up_fits ();
  assert (US.fits_u64);
  assume (US.v nb_size_classes == 9);
  US.fits_lte
    (US.v metadata_max * U32.v page_size * 9)
    (US.v metadata_max * U32.v page_size * US.v nb_size_classes);
  US.mul slab_size 9sz

open ROArray

unfold
let size_class_pred (slab_region:array U8.t) (sc:size_class) (i:nat) : prop =
  same_base_array slab_region sc.data.slab_region /\
  A.offset (A.ptr_of sc.data.slab_region) == A.offset (A.ptr_of slab_region) + i * US.v slab_size

[@@ reduce_attr]
inline_for_extraction noextract
let nbr_size_classes : (n:nat{US.fits n}) = 9

[@@ reduce_attr]
inline_for_extraction noextract
let sc_list : (l:list sc{List.length l == nbr_size_classes})
  = [@inline_let] let l = [16ul; 32ul; 64ul; 128ul; 256ul; 512ul; 1024ul; 2048ul; 4096ul] in
    assert_norm (List.length l == 9);
    l

/// A logical predicate indicating that a list of sizes corresponds
/// to the sizes of a list of size_classes
let synced_sizes (#n:nat) (k:nat{k <= n}) (sizes:Seq.lseq sc n) (size_classes:Seq.lseq size_class n) : prop =
  forall (i:nat{i < k}). Seq.index sizes i == (Seq.index size_classes i).data.size

/// This gathers all the data for small allocations.
/// In particular, it contains an array with all size_classes data,
/// as well as the slab_region containing the actual memory
noeq
type size_classes_all =
  { size_classes : sc:array size_class{length sc == nbr_size_classes}; // The array of size_classes
    sizes : sz:array sc{length sz == nbr_size_classes}; // An array of the sizes of [size_classes]
    g_size_classes: Ghost.erased (Seq.lseq size_class (length size_classes)); // The ghost representation of size_classes
    g_sizes: Ghost.erased (Seq.lseq sc (length sizes)); // The ghost representation of sizes
    ro_perm: ro_array size_classes g_size_classes; // The read-only permission on size_classes
    ro_sizes: ro_array sizes g_sizes;
    slab_region: arr:array U8.t{ // The region of memory handled by this size class
      synced_sizes nbr_size_classes g_sizes g_size_classes /\
      A.length arr == US.v slab_region_size /\
      (forall (i:nat{i < Seq.length g_size_classes}).
        size_class_pred arr (Seq.index g_size_classes i) i)
    }
  }

/// Performs the initialization of one size class of length [len], and stores it in the
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
  let n = 9sz in
  assume (
    US.v n > 0 /\ US.v n >= US.v 1sz /\
    US.v n == 9 /\
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

  change_slprop_rel
    (A.varray slab_region)
    (A.varray (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)))
    (fun x y -> x == y)
    (fun _ -> admit ());
  change_slprop_rel
    (A.varray md_bm_region)
    (A.varray (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)))
    (fun x y -> x == y)
    (fun _ -> admit ());
  change_slprop_rel
    (A.varray md_region)
    (A.varray (A.split_r md_region (US.mul metadata_max 0sz)))
    (fun x y -> x == y)
    (fun _ -> admit ());
  assert (A.length (A.split_r slab_region (US.mul (US.mul metadata_max (u32_to_sz page_size)) 0sz)) == US.v metadata_max * US.v (u32_to_sz page_size) * US.v n);
  assert (A.length (A.split_r md_bm_region (US.mul (US.mul metadata_max 4sz) 0sz)) == US.v metadata_max * 4 * US.v n);
  assert (A.length (A.split_r md_region (US.mul metadata_max 0sz)) == US.v metadata_max * US.v n);

  let size_classes = mmap_sc 9sz in
  let sizes = mmap_sizes 9sz in

  init_size_classes sc_list n slab_region md_bm_region md_region size_classes sizes;

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

let null_or_varray (#a:Type) (r:array a) : vprop = if is_null r then emp else varray r

inline_for_extraction noextract
let return_null ()
  : Steel (array U8.t)
  emp
  (fun r -> null_or_varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> is_null r)
  = [@inline_let]
    let r = null in
    change_equal_slprop emp (null_or_varray r);
    return r

/// Wrapper around allocate_size_class, that does not return a pair, and instead
/// always returns a valid permission on the new pointer if it is not null
val allocate_size_class
  (scs: size_class_struct)
  : Steel (array U8.t)
  (size_class_vprop scs)
  (fun r -> null_or_varray r `star` size_class_vprop scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> not (is_null r) ==> A.length r == U32.v scs.size)

let allocate_size_class scs =
  let r = SizeClass.allocate_size_class scs in
  change_equal_slprop (if is_null r then emp else varray r) (null_or_varray r);
  return r

#restart-solver

#push-options "--fuel 0 --ifuel 0 --query_stats"
inline_for_extraction noextract
let slab_malloc_one (i:US.t{US.v i < nbr_size_classes}) (bytes: U32.t)
  : Steel
  (array U8.t)
  emp (fun r -> if is_null r then emp else varray r)
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
  let ptr = allocate_size_class sc.data in
  L.release sc.lock;
  return ptr
#pop-options

/// A wrapper around slab_malloc' that performs dispatch in the size classes
/// in a generic way. The list argument is not actually used, it just serves
/// as a counter that reduces better than nats
[@@ reduce_attr]
noextract
let rec slab_malloc_i
  (l:list sc{List.length l <= length sc_all.size_classes})
  (i:US.t{US.v i + List.length l == length sc_all.size_classes})
  bytes
  : Steel (array U8.t)
  emp
  (fun r -> if is_null r then emp else varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> not (is_null r) ==> A.length r >= U32.v bytes)
  = match l with
    | [] -> return_null ()
    | hd::tl ->
      let size = index sc_all.ro_sizes i in
      if bytes `U32.lte` size then
        slab_malloc_one i bytes
      else
        slab_malloc_i tl (i `US.add` 1sz) bytes

module T = FStar.Tactics

/// A variant of the normalization, with a zeta full to reduce under
/// matches (and if/then/else). To use with care, as zeta_full can
/// loop and lead to stack overflows
let norm_full () : T.Tac unit =
  T.norm [zeta_full; iota; primops; delta_attr [`%reduce_attr]];
  T.trefl ()

[@@ T.postprocess_with norm_full]
val slab_malloc (bytes:U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> if is_null r then emp else varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> not (is_null r) ==> A.length r >= U32.v bytes)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let slab_malloc bytes = (slab_malloc_i sc_list 0sz) bytes

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
  (ensures fun _ _ _ -> True)


(*
  // Probably need this as a top-level value somewhere
  assume (length sc_all.size_classes == 2);
  let sc0 = index sc_all.ro_perm 0sz in
  let sc1 = index sc_all.ro_perm 1sz in

  if bytes `U32.lte` sc0.data.size then (
    slab_malloc' sc0 bytes
  ) else if bytes `U32.lte` sc1.data.size then (
    slab_malloc' sc1 bytes

  // ) else if bytes `U32.lte` 32ul then (
  //   slab_malloc' sc_all.sc32 bytes
  // ) else if bytes `U32.lte` 64ul then (
  //   slab_malloc' sc_all.sc64 bytes
  // ) else if bytes `U32.lte` 128ul then (
  //   slab_malloc' sc_all.sc128 bytes
  // ) else if bytes `U32.lte` 256ul then (
  //   slab_malloc' sc_all.sc256 bytes
  // ) else if bytes `U32.lte` 512ul then (
  //   slab_malloc' sc_all.sc512 bytes
  // ) else if bytes `U32.lte` 1024ul then (
  //   slab_malloc' sc_all.sc1024 bytes
  // ) else if bytes `U32.lte` 2048ul then (
  //   slab_malloc' sc_all.sc2048 bytes
  // ) else if bytes `U32.lte` 4096ul then (
  //   slab_malloc' sc_all.sc4096 bytes
  ) else (
    return_null ()
  )

*)

#pop-options

inline_for_extraction noextract
let slab_free' (sc: size_class) (ptr: array U8.t) (diff: US.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun h0 ->
    let diff' = offset (ptr_of ptr) - offset (ptr_of sc.data.slab_region) in
    same_base_array ptr sc.data.slab_region /\
    0 <= diff' /\
    diff' < US.v slab_size /\
    US.v diff = diff')
  (ensures fun h0 _ h1 -> True)
  =
  L.acquire sc.lock;
  let res = deallocate_size_class sc.data ptr diff in
  L.release sc.lock;
  return res

#restart-solver

#push-options "--fuel 0 --ifuel 0"

#restart-solver

//TODO: metaprogramming
let slab_free ptr =
  return false
(*
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

  // Needs to be somewhere at the toplevel
  assume (length sc_all.size_classes == 2);
  let sc0 = ROArray.index sc_all.ro_perm 0sz in
  let sc1 = ROArray.index sc_all.ro_perm 1sz in

  let rem = US.rem diff_sz slab_size in
       if (index = 0sz) then slab_free' sc0 ptr rem
  else if (index = 1sz) then slab_free' sc1 ptr rem
  // else if (index = 2sz) then slab_free' sc_all.sc64 ptr rem
  // else if (index = 3sz) then slab_free' sc_all.sc128 ptr rem
  // else if (index = 4sz) then slab_free' sc_all.sc256 ptr rem
  // else if (index = 5sz) then slab_free' sc_all.sc512 ptr rem
  // else if (index = 6sz) then slab_free' sc_all.sc1024 ptr rem
  // else if (index = 7sz) then slab_free' sc_all.sc2048 ptr rem
  // else if (index = 8sz) then slab_free' sc_all.sc4096 ptr rem
  //TODO: expose n, remove this last case
  else return false
*)

//TODO: metaprogramming
let slab_getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (fun _ ->
   A.varray ptr `star` A.varray (A.split_l sc_all.slab_region 0sz))
  (requires fun _ -> SAA.within_bounds
    (A.split_l (G.reveal sc_all.slab_region) 0sz)
    ptr
    (A.split_r (G.reveal sc_all.slab_region) slab_region_size)
  )
  (ensures fun h0 _ h1 ->
    A.asel ptr h1 == A.asel ptr h0
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
       if (index = 0sz) then return 16sz
  else if (index = 1sz) then return 32sz
  else if (index = 2sz) then return 64sz
  else if (index = 3sz) then return 128sz
  else if (index = 4sz) then return 256sz
  else if (index = 5sz) then return 512sz
  else if (index = 6sz) then return 1024sz
  else if (index = 7sz) then return 2048sz
  else if (index = 8sz) then return 4096sz
  //TODO: expose n, remove this last case
  else return 0sz
