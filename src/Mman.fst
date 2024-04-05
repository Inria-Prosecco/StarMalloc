module Mman

open Steel.Effect.Atomic
open Steel.Effect
module A = Steel.Array

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT
module AL = ArrayList
module R = Steel.Reference

open Config
open Utils2

/// 1) Initialization of the allocator
// all functions with a _init suffix
// are only meant to be used at initialization
// and fail if the underlying mmap operation fails

// POSIX spec: mmap returns a page-aligned array of bytes;
// thus, mmap_u8_init returns a page-aligned array of bytes;
// hence the postcondition array_u8_alignment page_size
assume val mmap_u8_init (len: US.t)
  : Steel (array U8.t)
    emp
    (fun r -> A.varray r)
    (fun _ -> US.v len > 0)
    (fun _ r h1 ->
      A.length r == US.v len /\
      A.is_full_array r /\
      A.asel r h1 == Seq.create (US.v len) U8.zero /\
      array_u8_alignment r page_size
    )

assume val mmap_u64_init (len: US.t)
  : Steel (array U64.t)
    emp
    (fun r -> A.varray r)
    (fun _ -> US.v len > 0)
    (fun _ r h1 ->
      A.length r == US.v len /\
      A.is_full_array r /\
      A.asel r h1 == Seq.create (US.v len) U64.zero
    )

assume val mmap_cell_status_init (len: US.t)
  : Steel (array AL.cell)
     emp
    (fun r -> A.varray r)
    (fun _ -> US.v len > 0)
    (fun _ r h1 ->
      A.length r == US.v len /\
      A.is_full_array r
    )

assume val mmap_ptr_us_init (_:unit)
  : SteelT (R.ref US.t)
    emp
    (fun r -> R.vptr r)

assume val mmap_array_us_init (len: US.t)
  : Steel (A.array US.t)
    emp
    (fun r -> A.varray r)
    (fun _ -> US.v len > 0)
    (ensures fun _ r _ ->
      A.length r == US.v len /\
      A.is_full_array r
    )

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
    (fun r -> A.varray r)
    (fun _ -> US.v len > 0)
    (fun _ r h1 ->
      A.length r == US.v len /\
      A.is_full_array r
    )

assume val mmap_sizes_init (len: US.t)
  : Steel (array sc)
     emp
    (fun r -> A.varray r)
    (fun _ -> US.v len > 0)
    (fun _ r h1 ->
      A.length r == US.v len /\
      A.is_full_array r
    )

// used in src/LargeAlloc.fst
// mmap_ptr_metadata

/// 2) Large allocations wrappers

open NullOrVarray

module FML = FStar.Math.Lemmas

open MiscArith

open FStar.Mul

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
noextract
let nearest_multiple_upper_rounding
  (n: nat)
  (multiple: nat{multiple > 0})
  : Pure nat
  (requires True)
  (ensures fun r ->
    r >= 0 /\
    r % multiple == 0 /\
    r >= n /\
    r - n < multiple
  )
  =
  if n % multiple <> 0
  then (
    let r = n - (n % multiple) + multiple in
    FML.euclidean_division_definition n multiple;
    assert (n - (n % multiple) == (n/multiple)*multiple);
    lemma_mod_mul2 (n/multiple) multiple multiple;
    assert ((n - (n % multiple)) % multiple == 0);
    lemma_mod_plus2 (n - (n % multiple)) multiple multiple;
    r
  ) else n

let rec nearest_multiple_upper_rounding_lemma
  (n: nat)
  (multiple: nat{multiple > 0})
  (k: nat)
  : Lemma
  (requires k >= n /\ k % multiple == 0)
  (ensures
    k >= nearest_multiple_upper_rounding n multiple
  )
  (decreases k)
  =
  let n' = nearest_multiple_upper_rounding n multiple in
  assert (n' >= n /\ n' % multiple == 0);
  if k < n'
  then (
    assert (n' > n);
    assert (n % multiple <> 0);
    let diff = n' - k in
    assert (0 < diff);
    assert (n' % multiple == 0);
    assert (k % multiple == 0);
    lemma_mod_add_inv k multiple;
    assert ((-k) % multiple == 0);
    lemma_mod_plus2 (-k) n' multiple;
    assert (diff % multiple == 0);
    assert (diff >= multiple);
    if diff >= multiple
    then nearest_multiple_upper_rounding_lemma n multiple (k - multiple)
    else ()
 ) else ()

noextract
let spec_mmap_actual_size (size: nat)
  : Pure nat
  (requires True)
  (ensures fun r ->
    r >= 0 /\
    r % (U32.v page_size) == 0 /\
    r >= size /\
    r - size < (U32.v page_size)
  )
  =
  nearest_multiple_upper_rounding size (U32.v page_size)

let mmap_actual_size (size: US.t)
  : Pure US.t
  (requires
    US.v size >= U32.v page_size /\
    US.fits (US.v size + U32.v page_size)
  )
  (ensures fun r ->
    US.v r == spec_mmap_actual_size (US.v size)
  )
  =
  let rem = US.rem size (u32_to_sz page_size) in
  if rem <> 0sz
  then US.add (US.sub size rem) (u32_to_sz page_size)
  else size
#pop-options

// POSIX spec: mmap returns a page-aligned array of bytes;
// thus, mmap_u8 returns a page-aligned array of bytes;
// hence the postcondition array_u8_alignment page_size
//noextract
assume val mmap_u8
  (size: US.t)
  : Steel (array U8.t)
    emp
    (fun ptr -> null_or_varray ptr)
    (requires fun _ -> US.v size > 0)
    (ensures fun _ ptr h1 ->
      let s : t_of (null_or_varray ptr)
        = h1 (null_or_varray ptr) in
      not (A.is_null ptr) ==> (
        A.length ptr == spec_mmap_actual_size (US.v size) /\
        A.is_full_array ptr /\
        array_u8_alignment ptr page_size /\
        zf_u8 s
      )
    )

// TODO: should the underlying munmap fail in a stricter manner?
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

