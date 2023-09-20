module Mman

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module US = FStar.SizeT
module AL = ArrayList
module R = Steel.Reference

open Utils2

//TODO: TO BE REMOVED
// only used during allocator initialization
// checks that the return ptr is not null
//assume val mmap_init
//  (size: US.t)
//  : Steel (array U8.t)
//    emp
//    (fun r -> A.varray r)
//    (requires fun _ -> True)
//    (ensures fun _ ptr h1 ->
//      A.length ptr == US.v size /\
//      A.is_full_array ptr /\
//      A.asel ptr h1 == Seq.create (US.v size) U8.zero
//    )

/// 1) Initialization of the allocator
// all functions with a _init suffix
// are only meant to be used at initialization
// and fail if the underlying mmap operation fails

// mmap_u8_init returns a page-aligned array of bytes
// that is, with an alignment of at least 16 bytes
// hence the abstract property array_u8_proper_alignment here
assume val mmap_u8_init (len: US.t)
  : Steel (array U8.t)
    emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v len) U8.zero /\
      array_u8_proper_alignment a
    )

assume val mmap_u64_init (len: US.t)
  : Steel (array U64.t)
    emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a /\
      A.asel a h1 == Seq.create (US.v len) U64.zero
    )

assume val mmap_cell_status_init (len: US.t)
  : Steel (array AL.cell)
     emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a
    )

assume val mmap_ptr_us_init (_:unit)
  : SteelT (R.ref US.t)
    emp
    (fun r -> R.vptr r)

module L = Steel.SpinLock

open SizeClass
noeq
type size_class =
  {
    // The content of the sizeclass
    data : size_class_struct;
    // Mutex locking ownership of the sizeclass
    lock : L.lock (size_class_vprop data);
  }

assume val mmap_sc_init (len: US.t)
  : Steel (array size_class)
     emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a
    )

assume val mmap_sizes_init (len: US.t)
  : Steel (array sc)
     emp
    (fun a -> A.varray a)
    (fun _ -> True)
    (fun _ a h1 ->
      A.length a == US.v len /\
      A.is_full_array a
    )

// used in src/LargeAlloc.fst
// mmap_ptr_metadata

/// 2) Large allocations wrappers

open NullOrVarray

//noextract
assume val mmap_u8
  (size: US.t)
  : Steel (array U8.t)
    emp
    (fun ptr -> null_or_varray ptr)
    (requires fun _ -> True)
    (ensures fun _ ptr h1 ->
      let s : t_of (null_or_varray ptr)
        = h1 (null_or_varray ptr) in
      not (A.is_null ptr) ==> (
        A.length ptr == US.v size /\
        A.is_full_array ptr /\
        array_u8_proper_alignment ptr /\
        zf_u8 s
      )
    )

//noextract
assume val munmap_u8 (ptr: array U8.t) (size: US.t)
  : Steel unit
    (A.varray ptr)
    (fun _ -> emp)
    (requires fun _ ->
      A.length ptr == US.v size /\
      A.is_full_array ptr
    )
    (ensures fun _ _ _ -> True)

