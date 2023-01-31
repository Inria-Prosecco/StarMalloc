module Main

module U8 = FStar.UInt8
module U32 = FStar.UInt32

open SizeClass
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module L = Steel.SpinLock

assume
val size_class16 : size_class_struct
assume
val size_class32 : size_class_struct
assume
val size_class64 : size_class_struct

assume
val size_class16_lock : L.lock (size_class_vprop size_class16)
assume
val size_class32_lock : L.lock (size_class_vprop size_class32)
assume
val size_class64_lock : L.lock (size_class_vprop size_class64)



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
      L.acquire size_class16_lock;
      let ptr = allocate_size_class size_class16 in
      L.release size_class16_lock;
      return ptr
    end
    else
    if bytes `U32.lte` 32ul then begin
      L.acquire size_class32_lock;
      let ptr = allocate_size_class size_class32 in
      L.release size_class32_lock;
      return ptr

    end
    else
    if bytes `U32.lte` 64ul then begin
      L.acquire size_class64_lock;
      let ptr = allocate_size_class size_class64 in
      L.release size_class64_lock;
      return ptr
    end
    else return_null ()
  end
