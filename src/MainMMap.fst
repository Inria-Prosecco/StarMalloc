module MainMMap

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module US = FStar.SizeT

open Steel.Effect
open Steel.Array

module AL = ArrayList
module R = Steel.Reference
module A = Steel.Array

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

assume val mmap_cell_status (len: US.t)
  : Steel (array (AL.cell Slabs.status))
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

assume val mmap_ptr_us (_:unit)
  : SteelT (R.ref US.t)
    emp
    (fun r -> R.vptr r)
