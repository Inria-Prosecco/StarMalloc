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
module AR = Steel.ArrayRef
module R = Steel.Reference
module L = Steel.SpinLock
module AL = ArrayList
module ALG = ArrayListGen

open Prelude
open SizeClass
open SlabsCommon
open SteelVRefineDep
open SteelStarSeqUtils
open Utils2

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
val mmap_ptr_u32 (_:unit)
  : SteelT (R.ref U32.t)
    emp
    (fun r -> R.vptr r)

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
    lock : L.lock (size_class_vprop data) }

let ind_aux pred1 pred2 pred3 r idxs : vprop =
      AL.varraylist pred1 pred2 pred3 r
        (US.v (fst (fst idxs)))
        (US.v (snd (fst idxs)))
        (US.v (snd idxs))


val intro_ind_varraylist_nil (#opened:_)
  (pred1 pred2 pred3: AL.status -> prop) (r: A.array AL.cell)
  (r1 r2 r3: R.ref US.t)
  : SteelGhost unit opened
      (A.varray r `star` R.vptr r1 `star` R.vptr r2 `star` R.vptr r3)
      (fun _ -> ind_varraylist pred1 pred2 pred3 r r1 r2 r3)
      (requires fun h -> A.length r == 0 /\
        R.sel r1 h == AL.null_ptr /\
        R.sel r2 h == AL.null_ptr /\
        R.sel r3 h == AL.null_ptr
      )
      (ensures fun _ _ _ -> True)

let intro_ind_varraylist_nil pred1 pred2 pred3 r r1 r2 r3 =
  ALG.intro_arraylist_nil
    pred1 pred2 pred3
    r
    AL.null_ptr AL.null_ptr AL.null_ptr;

  let idxs = gget (R.vptr r1 `star` R.vptr r2 `star` R.vptr r3) in

  assert_norm (ind_aux pred1 pred2 pred3 r ((AL.null_ptr, AL.null_ptr), AL.null_ptr) ==
          AL.varraylist pred1 pred2 pred3 r (US.v AL.null_ptr) (US.v AL.null_ptr) (US.v AL.null_ptr));
  intro_vdep
    (R.vptr r1 `star` R.vptr r2 `star` R.vptr r3)
    (AL.varraylist pred1 pred2 pred3 r (US.v AL.null_ptr) (US.v AL.null_ptr) (US.v AL.null_ptr))
    (ind_aux pred1 pred2 pred3 r)

val intro_left_vprop_empty (#opened:_)
  (sc:sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  (r1 r2 r3: R.ref US.t)
  : SteelGhost unit opened
      (A.varray (split_l md_region 0sz) `star` R.vptr r1 `star` R.vptr r2 `star` R.vptr r3)
      (fun _ -> SlabsCommon.left_vprop sc slab_region md_bm_region md_region r1 r2 r3 0ul)
      (requires fun h ->
        R.sel r1 h == AL.null_ptr /\
        R.sel r2 h == AL.null_ptr /\
        R.sel r3 h == AL.null_ptr
      )
      (ensures fun _ _ _ -> True)

#push-options "--z3rlimit 30"
let intro_left_vprop_empty sc slab_region md_bm_region md_region r1 r2 r3 =
  change_equal_slprop
    (A.varray (split_l md_region 0sz))
    (A.varray (split_l md_region (u32_to_sz 0ul)));
  intro_ind_varraylist_nil pred1 pred2 pred3
    (A.split_l md_region (u32_to_sz 0ul))
    r1 r2 r3;

  let s = gget (ind_varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz 0ul))
      r1 r2 r3) in


  starseq_intro_empty #_
      #(pos:U32.t{U32.v pos < U32.v 0ul})
      #(SlabsCommon.t sc)
      (SlabsCommon.f sc slab_region md_bm_region 0ul (ALG.dataify (dsnd s)))
      (SlabsCommon.f_lemma sc slab_region md_bm_region 0ul (ALG.dataify (dsnd s)));

  assert (SeqUtils.init_u32_refined (U32.v 0ul) `Seq.equal` Seq.empty);

  let open FStar.Tactics in
  assert ((starseq
      #(pos:U32.t{U32.v pos < U32.v 0ul})
      #(t sc)
      (f sc slab_region md_bm_region 0ul (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0ul (ALG.dataify (dsnd s)))
      Seq.empty) ==
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 0ul s))
  by (norm [delta_only [`%left_vprop_aux]]);


  change_equal_slprop
    (starseq
      #(pos:U32.t{U32.v pos < U32.v 0ul})
      #(t sc)
      (f sc slab_region md_bm_region 0ul (ALG.dataify (dsnd s)))
      (f_lemma sc slab_region md_bm_region 0ul (ALG.dataify (dsnd s)))
      Seq.empty)
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 0ul s);

  intro_vdep
    (ind_varraylist pred1 pred2 pred3
      (A.split_l md_region (u32_to_sz 0ul))
      r1 r2 r3)
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 0ul s)
    (left_vprop_aux sc slab_region md_bm_region md_region r1 r2 r3 0ul)

val intro_right_vprop_empty (#opened:_)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array AL.cell{A.length md_region = U32.v metadata_max})
  : SteelGhost unit opened
     (A.varray (split_r slab_region 0sz) `star`
      A.varray (split_r md_bm_region 0sz) `star`
      A.varray (split_r md_region 0sz))
    (fun _ -> SlabsCommon.right_vprop slab_region md_bm_region md_region 0ul)
    (requires fun h ->
      A.asel (split_r slab_region 0sz) h `Seq.equal` Seq.create (A.length slab_region) U8.zero /\
      A.asel (split_r md_bm_region 0sz) h `Seq.equal` Seq.create (A.length md_bm_region) U64.zero)
    (ensures fun _ _ _ -> True)

let intro_right_vprop_empty slab_region md_bm_region md_region =
 change_equal_slprop
    (A.varray (A.split_r slab_region 0sz))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul 0ul page_size))));
  change_equal_slprop
    (A.varray (A.split_r md_bm_region 0sz))
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul 0ul 4ul))));
  change_equal_slprop
    (A.varray (A.split_r md_region 0sz))
    (A.varray (A.split_r md_region (u32_to_sz 0ul)));
  intro_vrefine
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul 0ul page_size)))) zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul 0ul 4ul)))) zf_u64;
  assert_norm ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul 0ul page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul 0ul 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz 0ul)) ==
    (right_vprop slab_region md_bm_region md_region 0ul));
  change_equal_slprop
    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul 0ul page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul 0ul 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz 0ul)))
    (right_vprop slab_region md_bm_region md_region 0ul)

let vrefinedep_ext
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f f': ( (t_of (vrefine v p)) -> Tot vprop))
  : Lemma (requires f == f') (ensures vrefinedep v p f == vrefinedep v p f')
  = ()

#restart-solver
#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects --fuel 0 --ifuel 0"
noextract inline_for_extraction
let init_struct (sc:sc)
  : SteelT size_class_struct
  emp
  (fun scs -> size_class_vprop scs)
  =
  intro_fits_u32 ();
  let slab_region = mmap_u8 (u32_to_sz (U32.mul metadata_max page_size)) in
  let md_bm_region = mmap_u64 (u32_to_sz (U32.mul metadata_max 4ul)) in
  let md_region = mmap_cell_status (u32_to_sz metadata_max) in

  A.ghost_split slab_region 0sz;
  A.ghost_split md_bm_region 0sz;
  A.ghost_split md_region 0sz;

  A.ghost_split (A.split_r slab_region 0sz) 0sz;

  drop (A.varray (A.split_l (A.split_r slab_region 0sz) 0sz));
  drop (A.varray (A.split_l md_bm_region 0sz));

  intro_right_vprop_empty (A.split_r slab_region 0sz) md_bm_region md_region;

  let ptr_partial = mmap_ptr_us () in
  let ptr_empty = mmap_ptr_us () in
  let ptr_full = mmap_ptr_us () in

  R.write ptr_partial AL.null_ptr;
  R.write ptr_empty AL.null_ptr;
  R.write ptr_full AL.null_ptr;

  intro_left_vprop_empty sc (A.split_r slab_region 0sz) md_bm_region md_region ptr_empty ptr_partial ptr_full;

  let md_count = mmap_ptr_u32 () in
  R.write md_count 0ul;
  intro_vrefinedep
    (R.vptr md_count)
    vrefinedep_prop
    (size_class_vprop_aux sc slab_region md_bm_region md_region ptr_empty ptr_partial ptr_full)
    (left_vprop sc (A.split_r slab_region 0sz) md_bm_region md_region
         ptr_empty ptr_partial ptr_full 0ul `star`
     right_vprop (A.split_r slab_region 0sz) md_bm_region md_region 0ul `star` A.varray (A.split_l slab_region 0sz));


  [@inline_let]
  let scs = {
    size = sc;
    partial_slabs = ptr_partial;
    empty_slabs = ptr_empty;
    full_slabs = ptr_full;
    slab_region = slab_region;
    md_bm_region = md_bm_region;
    md_region = md_region;
    md_count = md_count;
  } in

  change_slprop_rel
    (vrefinedep
      (R.vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux sc slab_region md_bm_region md_region ptr_empty ptr_partial ptr_full))
     (size_class_vprop scs)
    (fun _ _ -> True)
    (fun _ ->
      let open FStar.Tactics in
      assert (
        size_class_vprop scs ==
    vrefinedep
      (R.vptr scs.md_count)
      vrefinedep_prop
      (size_class_vprop_aux scs.size scs.slab_region scs.md_bm_region scs.md_region scs.empty_slabs scs.partial_slabs scs.full_slabs)
         ) by (norm [delta_only [`%size_class_vprop]]; trefl ())
    );

  return scs

noextract inline_for_extraction
let init (sc:sc) : SteelTop size_class false (fun _ -> emp) (fun _ _ _ -> True) =
  let data = init_struct sc in
  let lock = L.new_lock (size_class_vprop data) in
  {data; lock}

let init16 () : SteelTop size_class false (fun _ -> emp) (fun _ _ _ -> True) = init 16ul
let init32 () : SteelTop size_class false (fun _ -> emp) (fun _ _ _ -> True) = init 32ul
let init64 () : SteelTop size_class false (fun _ -> emp) (fun _ _ _ -> True) = init 64ul


// Intentional top-level effect for initialization, we temporarily disable the corresponding warning
// for these definitions
#push-options "--warn_error '-272'"
let size_class16 : size_class = init16 ()
let size_class32 : size_class = init32 ()
let size_class64 : size_class = init64 ()
#pop-options

let null_or_varray (#a:Type) (r:array a) : vprop = if is_null r then emp else varray r

inline_for_extraction noextract
let return_null () : SteelT (array U8.t) emp (fun r -> null_or_varray r)
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
  (ensures fun h0 _ h1 -> True)

let allocate_size_class scs =
  let r = SizeClass.allocate_size_class scs in
  change_equal_slprop (if is_null r then emp else varray r) (null_or_varray r);
  return r

val slab_malloc (bytes:U32.t) : SteelT (array U8.t) emp (fun r -> if is_null r then emp else varray r)

let slab_malloc bytes =
  if bytes = 0ul then
    return_null ()
  else begin
    if bytes `U32.lte` 16ul then begin
      L.acquire size_class16.lock;
      let ptr = allocate_size_class size_class16.data in
      L.release size_class16.lock;
      return ptr
    end
    else
    if bytes `U32.lte` 32ul then begin
      L.acquire size_class32.lock;
      let ptr = allocate_size_class size_class32.data in
      L.release size_class32.lock;
      return ptr

    end
    else
    if bytes `U32.lte` 64ul then begin
      L.acquire size_class64.lock;
      let ptr = allocate_size_class size_class64.data in
      L.release size_class64.lock;
      return ptr
    end
    else return_null ()
  end
