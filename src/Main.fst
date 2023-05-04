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
module RS = RegionSelect
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

assume
val mmap_u8 (len: US.t)
  : Steel (array U8.t)
    emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v len) U8.zero
    )

assume
val mmap_u64 (len: US.t)
  : Steel (array U64.t)
    emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v len) U64.zero
    )

assume
val mmap_ptr_us (_:unit)
  : SteelT (R.ref US.t)
    emp
    (fun r -> R.vptr r)

assume
val mmap_cell_status (len: US.t)
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
  { data : size_class_struct;
    // Mutex locking ownership of the sizeclass
    lock : L.lock (size_class_vprop data);
    // Two tokens for read-only permissions on the start and end
    // of the slab regions, that allow to determine whether a pointer
    // is in the region without acquiring the lock above
    region_start: RS.ro_array (A.split_l data.slab_region 0sz);
    region_end: RS.ro_array (A.split_r data.slab_region slab_size);
    }

let ind_aux pred1 pred2 pred3 pred4 r idxs : vprop =
  SlabsCommon.ind_varraylist_aux pred1 pred2 pred3 pred4 r idxs

//#push-options "--compat_pre_core 0 --compat_pre_typed_indexed_effects"
val intro_ind_varraylist_nil (#opened:_)
  (pred1 pred2 pred3 pred4: AL.status -> prop) (r: A.array AL.cell)
  (r1 r2 r3 r4: R.ref US.t)
  : SteelGhost unit opened
      (A.varray r `star` R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4)
      (fun _ -> ind_varraylist pred1 pred2 pred3 pred4 r r1 r2 r3 r4)
      (requires fun h -> A.length r == 0 /\
        R.sel r1 h == AL.null_ptr /\
        R.sel r2 h == AL.null_ptr /\
        R.sel r3 h == AL.null_ptr /\
        R.sel r4 h == AL.null_ptr
      )
      (ensures fun _ _ _ -> True)

let intro_ind_varraylist_nil pred1 pred2 pred3 pred4 r r1 r2 r3 r4 =
  ALG.intro_arraylist_nil
    pred1 pred2 pred3 pred4
    r
    AL.null_ptr AL.null_ptr AL.null_ptr AL.null_ptr;
  let idxs = gget (R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4) in
  intro_vrefine
    (SlabsCommon.ind_varraylist_aux2 pred1 pred2 pred3 pred4 r (((AL.null_ptr, AL.null_ptr), AL.null_ptr), AL.null_ptr))
    (SlabsCommon.ind_varraylist_aux_refinement pred1 pred2 pred3 pred4 r (((AL.null_ptr, AL.null_ptr), AL.null_ptr), AL.null_ptr));
  intro_vdep
    (R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4)
    (SlabsCommon.ind_varraylist_aux pred1 pred2 pred3 pred4 r (((AL.null_ptr, AL.null_ptr), AL.null_ptr), AL.null_ptr))
    (ind_aux pred1 pred2 pred3 pred4 r)

val intro_left_vprop_empty (#opened:_)
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = US.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max})
  (r1 r2 r3 r4: R.ref US.t)
  : SteelGhost unit opened
      (A.varray (split_l md_region 0sz) `star` R.vptr r1 `star` R.vptr r2 `star` R.vptr r3 `star` R.vptr r4)
      (fun _ -> SlabsCommon.left_vprop sc slab_region md_bm_region md_region r1 r2 r3 r4 0sz)
      (requires fun h ->
        R.sel r1 h == AL.null_ptr /\
        R.sel r2 h == AL.null_ptr /\
        R.sel r3 h == AL.null_ptr /\
        R.sel r4 h == AL.null_ptr
      )
      (ensures fun _ _ _ -> True)

#push-options "--z3rlimit 30"
let intro_left_vprop_empty sc slab_region md_bm_region md_region r1 r2 r3 r4 =
  intro_ind_varraylist_nil pred1 pred2 pred3 pred4
    (A.split_l md_region 0sz)
    r1 r2 r3 r4;

  let s = gget (ind_varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region 0sz)
      r1 r2 r3 r4) in

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
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 0sz s))
  by (norm [delta_only [`%left_vprop_aux]]);


  change_equal_slprop
    (starseq
      #(pos:US.t{US.v pos < US.v 0sz})
      #(t sc)
      (f sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0sz (ALG.dataify (dsnd s)))
      (SeqUtils.init_us_refined (US.v 0sz)))
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 0sz s);

  intro_vdep
    (ind_varraylist pred1 pred2 pred3 pred4
      (A.split_l md_region 0sz)
      r1 r2 r3 r4)
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 0sz s)
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 r4 0sz)

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

let vrefinedep_ext
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f f': ( (t_of (vrefine v p)) -> Tot vprop))
  : Lemma (requires f == f') (ensures vrefinedep v p f == vrefinedep v p f')
  = ()

#restart-solver

#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects --fuel 0 --ifuel 0"
noextract inline_for_extraction
let init_struct (n: US.t{US.v n > 0 /\ US.fits (US.v metadata_max * US.v n)}) (sc:sc)
  //(slab_region: array U8.t{A.length slab_region == U32.v page_size * US.v metadata_max * US.v n})
  //(md_bm_region: array U64.t{A.length md_bm_region == US.v 4sz * US.v metadata_max * US.v n})
  (md_region: array AL.cell{A.length md_region == US.v metadata_max * US.v n})
  : Steel size_class_struct
  (
    //A.varray slab_region `star`
    //A.varray md_bm_region `star`
    A.varray md_region
  )
  (fun scs -> size_class_vprop scs `star`
    A.varrayp (A.split_l scs.slab_region 0sz) halfp `star`
    A.varray (A.split_r scs.slab_region slab_size) `star`
    A.varray (A.split_l md_region (US.mul metadata_max (US.sub n 1sz)))
  )
  (requires fun h0 -> True
    //zf_u8 (A.asel slab_region h0) /\
    //zf_u64 (A.asel md_bm_region h0)
  )
  (ensures fun _ r _ -> U32.eq r.size sc)
  =
  //let s1 = gget (A.varray slab_region) in
  //let s2 = gget (A.varray md_bm_region) in
  //zf_u8_split s1 0;
  //zf_u64_split s2 0;
  intro_fits_u32 ();
  let slab_region = mmap_u8 (US.mul metadata_max (u32_to_sz page_size)) in
  let md_bm_region = mmap_u64 (US.mul metadata_max 4sz) in
  A.ghost_split md_region (US.mul metadata_max (US.sub n 1sz));
  let md_region' = A.split_r md_region (US.mul metadata_max (US.sub n 1sz)) in
  change_equal_slprop
    (A.varray (A.split_r md_region (US.mul metadata_max (US.sub n 1sz))))
    (A.varray md_region');
  //let md_region = mmap_cell_status metadata_max in

  A.ghost_split slab_region slab_size;
  change_slprop_rel
    (A.varray (A.split_l slab_region slab_size))
    (A.varray slab_region)
    (fun x y -> x == y)
    (fun _ -> A.ptr_shift_zero (A.ptr_of slab_region));

  A.ghost_split slab_region 0sz;
  A.ghost_split md_bm_region 0sz;
  A.ghost_split md_region' 0sz;

  A.ghost_split (A.split_r slab_region 0sz) 0sz;

  drop (A.varray (A.split_l (A.split_r slab_region 0sz) 0sz));
  drop (A.varray (A.split_l md_bm_region 0sz));

  intro_right_vprop_empty (A.split_r slab_region 0sz) md_bm_region md_region';

  let ptr_partial = mmap_ptr_us () in
  let ptr_empty = mmap_ptr_us () in
  let ptr_full = mmap_ptr_us () in
  let ptr_guard = mmap_ptr_us () in

  R.write ptr_partial AL.null_ptr;
  R.write ptr_empty AL.null_ptr;
  R.write ptr_full AL.null_ptr;
  R.write ptr_guard AL.null_ptr;

  intro_left_vprop_empty sc (A.split_r slab_region 0sz) md_bm_region md_region' ptr_empty ptr_partial ptr_full ptr_guard;

  let md_count = mmap_ptr_us () in
  R.write md_count 0sz;

  A.share (A.split_l slab_region 0sz) Steel.FractionalPermission.full_perm halfp halfp;
  intro_vrefinedep
    (R.vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux sc
      slab_region md_bm_region md_region'
      ptr_empty ptr_partial ptr_full ptr_guard)
    (left_vprop sc (A.split_r slab_region 0sz) md_bm_region md_region'
         ptr_empty ptr_partial ptr_full ptr_guard 0sz `star`
     right_vprop (A.split_r slab_region 0sz) md_bm_region md_region' 0sz `star`
     A.varrayp (A.split_l slab_region 0sz) halfp);


  [@inline_let]
  let scs = {
    size = sc;
    partial_slabs = ptr_partial;
    empty_slabs = ptr_empty;
    full_slabs = ptr_full;
    guard_slabs = ptr_guard;
    slab_region = slab_region;
    md_bm_region = md_bm_region;
    md_region = md_region';
    md_count = md_count;
  } in

  change_slprop_rel
    (vrefinedep
      (R.vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux sc
        slab_region md_bm_region md_region'
        ptr_empty ptr_partial ptr_full ptr_guard))
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
            scs.empty_slabs scs.partial_slabs scs.full_slabs scs.guard_slabs)
      ) by (norm [delta_only [`%size_class_vprop]]; trefl ())
    );

  change_equal_slprop
    (A.varrayp (A.split_l slab_region 0sz) halfp)
    (A.varrayp (A.split_l scs.slab_region 0sz) halfp);
  change_equal_slprop
    (A.varray (A.split_r slab_region slab_size))
    (A.varray (A.split_r scs.slab_region slab_size));

  return scs

let split_l_l (#opened:_) (#a: Type)
  (k1: US.t)
  (k2: US.t{US.v k1 <= US.v k2})
  (arr: array a{US.v k2 <= A.length arr})
  : SteelGhost unit opened
  (A.varray (
    A.split_l (A.split_l arr k2) k1
  ))
  (fun _ -> A.varray (
    A.split_l arr k1
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel (A.split_l (A.split_l arr k2) k1) h0
    ==
    A.asel (A.split_l arr k1) h1
  )
  =
  A.ptr_base_offset_inj
    (A.ptr_of (A.split_l (A.split_l arr k2) k1))
    (A.ptr_of (A.split_l arr k1));
  change_equal_slprop
    (A.varray (A.split_l (A.split_l arr k2) k1))
    (A.varray (A.split_l arr k1))

let split_l_l_mul (#opened:_) (#a: Type)
  (k1 k1': US.t)
  (k2: US.t{US.v k1 == US.v k1' /\ US.v k1 <= US.v k2})
  (n: US.t{US.fits (US.v k2 * US.v n)})
  (arr: array a{US.v k2 * US.v n <= A.length arr})
  : SteelGhost unit opened
  (A.varray (
    A.split_l (A.split_l arr (US.mul n k2)) (US.mul n k1)
  ))
  (fun _ -> A.varray (
    A.split_l arr (US.mul n k1')
  ))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel (A.split_l (A.split_l arr (US.mul n k2)) (US.mul n k1)) h0
    ==
    A.asel (A.split_l arr (US.mul n k1')) h1
  )
  =
  split_l_l (US.mul n k1) (US.mul n k2) arr;
  change_equal_slprop
    (A.varray (split_l arr (US.mul n k1)))
    (A.varray (split_l arr (US.mul n k1')))

// TODO: metaprogramming
let size_class16_t = r:size_class{U32.eq r.data.size 16ul}
let size_class32_t = r:size_class{U32.eq r.data.size 32ul}
let size_class64_t = r:size_class{U32.eq r.data.size 64ul}
let size_class128_t = r:size_class{U32.eq r.data.size 128ul}
let size_class256_t = r:size_class{U32.eq r.data.size 256ul}
let size_class512_t = r:size_class{U32.eq r.data.size 512ul}
let size_class1024_t = r:size_class{U32.eq r.data.size 1024ul}
let size_class2048_t = r:size_class{U32.eq r.data.size 2048ul}
let size_class4096_t = r:size_class{U32.eq r.data.size 4096ul}

//TODO: metaprogramming
noeq type size_classes_all = {
  sc16 : size_class16_t;
  sc32 : size_class32_t;
  sc64 : size_class64_t;
  sc128 : size_class128_t;
  sc256 : size_class256_t;
  sc512 : size_class512_t;
  sc1024 : size_class1024_t;
  sc2048 : size_class2048_t;
  sc4096 : size_class4096_t;
}

//TODO: metaprogramming
noextract inline_for_extraction
let init (_:unit)
  : SteelTop size_classes_all false
  (fun _ -> emp)
  (fun _ r _ -> True)
  =
  let n = 9sz in
  let md_region = mmap_cell_status (US.mul metadata_max n) in
  // sc16
  let data = init_struct n 16ul md_region in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc16 = {data; lock; region_start; region_end} in
  // sc32
  let data = init_struct (US.sub n 1sz) 32ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 1sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc32 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 1sz) 1sz) (US.sub n 2sz) (US.sub n 1sz) metadata_max md_region;
  // sc64
  let data = init_struct (US.sub n 2sz) 64ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 2sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc64 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 2sz) 1sz) (US.sub n 3sz) (US.sub n 2sz) metadata_max md_region;
  // sc128
  let data = init_struct (US.sub n 3sz) 128ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 3sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc128 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 3sz) 1sz) (US.sub n 4sz) (US.sub n 3sz) metadata_max md_region;
  // sc256
  let data = init_struct (US.sub n 4sz) 256ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 4sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc256 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 4sz) 1sz) (US.sub n 5sz) (US.sub n 4sz) metadata_max md_region;
  // sc512
  let data = init_struct (US.sub n 5sz) 512ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 5sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc512 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 5sz) 1sz) (US.sub n 6sz) (US.sub n 5sz) metadata_max md_region;
  // sc1024
  let data = init_struct (US.sub n 6sz) 1024ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 6sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc1024 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 6sz) 1sz) (US.sub n 7sz) (US.sub n 6sz) metadata_max md_region;
  // sc2048
  let data = init_struct (US.sub n 7sz) 2048ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 7sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc2048 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 7sz) 1sz) (US.sub n 8sz) (US.sub n 7sz) metadata_max md_region;
  // sc4096
  let data = init_struct (US.sub n 8sz) 4096ul
    (A.split_l md_region (US.mul metadata_max (US.sub n 8sz))) in
  let lock = L.new_lock (size_class_vprop data) in
  let region_start = RS.create_ro_array (A.split_l data.slab_region 0sz) in
  let region_end = RS.create_ro_array (A.split_r data.slab_region slab_size) in
  let sc4096 = {data; lock; region_start; region_end} in
  split_l_l_mul (US.sub (US.sub n 8sz) 1sz) (US.sub n 9sz) (US.sub n 8sz) metadata_max md_region;
  // end
  drop (A.varray
    (A.split_l md_region (US.mul metadata_max (US.sub n 9sz))));
  return {
    sc16 = sc16;
    sc32 = sc32;
    sc64 = sc64;
    sc128 = sc128;
    sc256 = sc256;
    sc512 = sc512;
    sc1024 = sc1024;
    sc2048 = sc2048;
    sc4096 = sc4096;
  }

#reset-options "--fuel 1 --ifuel 1"

#push-options "--print_implicits"

#push-options "--warn_error '-272'"
let sc_all : size_classes_all = init ()

// TODO: metaprogramming
let size_class16 : size_class16_t = sc_all.sc16
let size_class32 : size_class32_t = sc_all.sc32
let size_class64 : size_class64_t = sc_all.sc64
let size_class128 : size_class128_t = sc_all.sc128
let size_class256 : size_class256_t = sc_all.sc256
let size_class512 : size_class512_t = sc_all.sc512
let size_class1024 : size_class1024_t = sc_all.sc1024
let size_class2048 : size_class2048_t = sc_all.sc2048
let size_class4096 : size_class4096_t = sc_all.sc4096
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

val slab_malloc (bytes:U32.t)
  : Steel (array U8.t)
  emp
  (fun r -> if is_null r then emp else varray r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> not (is_null r) ==> A.length r >= U32.v bytes)

#restart-solver

#push-options "--fuel 0 --ifuel 0 --query_stats"
inline_for_extraction noextract
let slab_malloc' (sc: size_class) (bytes: U32.t)
  : Steel
  (array U8.t)
  emp (fun r -> if is_null r then emp else varray r)
  (requires fun _ ->
    U32.v bytes <= U32.v sc.data.size
  )
  (ensures fun _ r _ ->
    not (is_null r) ==> (
      A.length r == U32.v sc.data.size /\
      A.length r >= U32.v bytes
  ))
  =
  L.acquire sc.lock;
  let ptr = allocate_size_class sc.data in
  L.release sc.lock;
  return ptr
#pop-options

#restart-solver

#reset-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let slab_malloc bytes =
  if bytes `U32.lte` 16ul then (
    slab_malloc' size_class16 bytes
  ) else if bytes `U32.lte` 32ul then (
    slab_malloc' size_class32 bytes
  ) else if bytes `U32.lte` 64ul then (
    slab_malloc' size_class64 bytes
  ) else if bytes `U32.lte` 128ul then (
    slab_malloc' size_class128 bytes
  ) else if bytes `U32.lte` 256ul then (
    slab_malloc' size_class256 bytes
  ) else if bytes `U32.lte` 512ul then (
    slab_malloc' size_class512 bytes
  ) else if bytes `U32.lte` 1024ul then (
    slab_malloc' size_class1024 bytes
  ) else if bytes `U32.lte` 2048ul then (
    slab_malloc' size_class2048 bytes
  ) else if bytes `U32.lte` 4096ul then (
    slab_malloc' size_class4096 bytes
  ) else (
    return_null ()
  )
#pop-options

val slab_free (ptr:array U8.t)
  : SteelT bool
           (A.varray ptr)
           (fun b -> if b then emp else A.varray ptr)

inline_for_extraction noextract
let slab_free1 (sc: size_class) (ptr: array U8.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> A.varray ptr)
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    (if r then SAA.within_bounds
      (A.split_l sc.data.slab_region 0sz)
      ptr
      (A.split_r sc.data.slab_region slab_size) else
    True) /\
    asel ptr h1 == asel ptr h0
  )
  =
  RS.within_bounds_intro
    (A.split_l sc.data.slab_region 0sz)
    ptr
    (A.split_r sc.data.slab_region slab_size)
    sc.region_start
    sc.region_end

inline_for_extraction noextract
let slab_free2 (sc: size_class) (ptr: array U8.t)
  : Steel bool
  (A.varray ptr)
  (fun b -> if b then emp else A.varray ptr)
  (requires fun h0 ->
    SAA.within_bounds (A.split_l sc.data.slab_region 0sz) ptr (A.split_r sc.data.slab_region slab_size))
  (ensures fun h0 _ h1 -> True)
  =
  L.acquire sc.lock;
  let res = deallocate_size_class sc.data ptr in
  L.release sc.lock;
  return res

let slab_free ptr =
  if (slab_free1 size_class16 ptr) then slab_free2 size_class16 ptr
  else if (slab_free1 size_class32 ptr) then slab_free2 size_class32 ptr
  else if (slab_free1 size_class64 ptr) then slab_free2 size_class64 ptr
  else if (slab_free1 size_class128 ptr) then slab_free2 size_class128 ptr
  else if (slab_free1 size_class256 ptr) then slab_free2 size_class256 ptr
  else if (slab_free1 size_class512 ptr) then slab_free2 size_class512 ptr
  else if (slab_free1 size_class1024 ptr) then slab_free2 size_class1024 ptr
  else if (slab_free1 size_class2048 ptr) then slab_free2 size_class2048 ptr
  else if (slab_free1 size_class4096 ptr) then slab_free2 size_class4096 ptr
  else return false

let slab_getsize (ptr: array U8.t)
  : Steel US.t
  (A.varray ptr) (fun _ -> A.varray ptr)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    A.asel ptr h1 == A.asel ptr h0
  )
  =
  if (slab_free1 size_class16 ptr) then return 16sz
  else if (slab_free1 size_class32 ptr) then return 32sz
  else if (slab_free1 size_class64 ptr) then return 64sz
  else if (slab_free1 size_class128 ptr) then return 128sz
  else if (slab_free1 size_class256 ptr) then return 256sz
  else if (slab_free1 size_class512 ptr) then return 512sz
  else if (slab_free1 size_class1024 ptr) then return 1024sz
  else if (slab_free1 size_class2048 ptr) then return 2048sz
  else if (slab_free1 size_class4096 ptr) then return 4096sz
  else return 0sz
