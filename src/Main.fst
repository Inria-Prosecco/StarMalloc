module Main

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

open SizeClass
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module A = Steel.Array
module AR = Steel.ArrayRef
module R = Steel.Reference
module L = Steel.SpinLock
module SL = BlobList

noeq
type size_class =
  { data : size_class_struct;
    lock : L.lock (size_class_vprop data) }

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

assume val mmap_blob (len: US.t)
  : Steel (array SL.cell)
     emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a
    )

assume val mmap_ptr_u32 (_:unit)
  : SteelT (R.ref U32.t)
    emp
    (fun r -> R.vptr r)

assume val mmap_ptr_slt (_:unit)
  : SteelT (R.ref SL.t)
    emp
    (fun r -> R.vptr r)

//TODO: move to utils
inline_for_extraction noextract
let u32_to_sz = Slabs.u32_to_sz

#restart-solver
#push-options "--z3rlimit 200 --compat_pre_typed_indexed_effects"
let init (sc:U32.t)
  : SteelT size_class_struct
  emp
  (fun scs -> size_class_vprop scs)

  =
  let open Utils2 in
  assume (US.fits_u32);
  let v : v:U32.t{U32.v v <= U32.v metadata_max == true}
    = 0ul in
  let slab_region = mmap_u8 (u32_to_sz (U32.mul metadata_max page_size)) in
  let md_bm_region = mmap_u64 (u32_to_sz (U32.mul metadata_max 4ul)) in
  let md_region = mmap_blob (u32_to_sz metadata_max) in
  A.ghost_split slab_region 0sz;
  A.ghost_split md_bm_region 0sz;
  A.ghost_split md_region 0sz;
  drop (A.varray (A.split_l slab_region 0sz));
  drop (A.varray (A.split_l md_bm_region 0sz));
  drop (A.varray (A.split_l md_region 0sz));
  change_equal_slprop
    (A.varray (A.split_r slab_region 0sz))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))));
  change_equal_slprop
    (A.varray (A.split_r md_bm_region 0sz))
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))));
  change_equal_slprop
    (A.varray (A.split_r md_region 0sz))
    (A.varray (A.split_r md_region (u32_to_sz v)));
  intro_vrefine
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))) zf_u8;
  intro_vrefine
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))) zf_u64;
  change_slprop_rel
    ((A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size)))
      `vrefine` zf_u8) `star`
    (A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul)))
      `vrefine` zf_u64) `star`
    A.varray (A.split_r md_region (u32_to_sz v)))
    (Slabs.vp_aux slab_region md_bm_region md_region v)
    (fun x y -> x == y)
    (fun _ -> admit ());
  let md_count = mmap_ptr_u32 () in
  R.write md_count v;
  SteelVRefineDep.intro_vrefinedep
    (R.vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> Slabs.vp_aux slab_region md_bm_region md_region v)
    (Slabs.vp_aux slab_region md_bm_region md_region v);

  let ptr_partial = mmap_ptr_slt () in
  let ptr_empty = mmap_ptr_slt () in
  let ptr_full = mmap_ptr_slt () in

  R.write ptr_partial SL.null_t;
  R.write ptr_empty SL.null_t;
  R.write ptr_full SL.null_t;

  SL.intro_llist_nil (Slabs.p_partial 16ul);
  SL.intro_llist_nil (Slabs.p_empty 16ul);
  SL.intro_llist_nil (Slabs.p_full 16ul);

  SL.pack_ind (Slabs.p_partial 16ul) ptr_partial SL.null_t;
  SL.pack_ind (Slabs.p_empty 16ul) ptr_empty SL.null_t;
  SL.pack_ind (Slabs.p_full 16ul) ptr_full SL.null_t;


  let scs = {
    size = 16ul;
    partial_slabs = ptr_partial;
    empty_slabs = ptr_empty;
    full_slabs = ptr_full;
    slab_region = slab_region;
    md_bm_region = md_bm_region;
    md_region = md_region;
    md_count = md_count;
  } in

  change_equal_slprop
   (SL.ind_llist (Slabs.p_partial 16ul) ptr_partial `star`
    SL.ind_llist (Slabs.p_empty 16ul) ptr_empty `star`
    SL.ind_llist (Slabs.p_full 16ul) ptr_full `star`
  SteelVRefineDep.vrefinedep
    (R.vptr md_count)
    //TODO: hideous coercion
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v -> Slabs.vp_aux slab_region md_bm_region md_region v))
  (size_class_vprop scs);

  return scs


assume
val size_class16 : size_class
assume
val size_class32 : size_class
assume
val size_class64 : size_class


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
  rewrite_slprop
    (if (Ghost.reveal (snd r)) then varray (fst r) else emp)
    (null_or_varray (fst r))
    (fun _ -> admit());
  return (fst r)

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
