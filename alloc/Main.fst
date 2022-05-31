module Main

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32

open Impl.Core
open Impl.Mono
open Map.M

#set-options "--ide_id_info_off"

// machine representation
unfold let ptr_t = U64.t
unfold let size_t = U64.t

let a = ptr_t & size_t

let t = Impl.Core.t
let linked_tree = Impl.Core.linked_tree


inline_for_extraction noextract
let mmap (len: U64.t) (prot: I32.t)
  //= Mman.mmap 0UL len prot 33l (-1l) 0ul
  //MAP_PRIVATE instead of MAP_ANON (avoid filling the disk...)
  //34l = MAP_PRIVATE|MAP_ANON
  = Mman.mmap 0UL len prot 34l (-1l) 0ul

inline_for_extraction noextract
let munmap = Mman.munmap

let cmp (x y: U64.t & U64.t) : I64.t
  =
  let x = fst x in
  let y = fst y in
  if U64.gt x y then 1L
  else if U64.eq x y then 0L
  else -1L

//let compare_is_cmp () : Lemma
//(
//  (forall x. I64.eq (compare x x) I64.zero) /\
//  (forall x y. I64.gt (compare x y) I64.zero
//                 <==> I64.lt (compare y x) I64.zero) /\
//  (forall x  y z. I64.gte (compare x y) I64.zero /\
//                         I64.gte (compare y z) I64.zero ==>
//                         I64.gte (compare x z) I64.zero)
//) = ()
//
////let cmp : Impl.Common.cmp (ptr_t & size_t)
////  = fun x y -> compare (fst x) (fst y)
//let cmp : Impl.Common.cmp ptr_t = compare

let create_leaf = Impl.Trees.M.create_leaf
let insert = Impl.Mono.insert_avl
let delete = Impl.Mono.delete_avl
let mem = Impl.Mono.member
//let find = find

//assume val metadata_ptr: t a

let malloc (metadata: t a) (size: size_t)
//(flags: I32.t)
  : Steel (t a & ptr_t)
  (linked_tree metadata)
  (fun r -> linked_tree (fst r))
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp)
      (v_linked_tree metadata h0) /\
    Spec.size_of_tree (v_linked_tree metadata h0) < 100)
  (ensures fun h0 r h1 ->
    Spec.is_avl (spec_convert cmp)
      (v_linked_tree (fst r) h1) /\
    //v_linked_tree metadata_ptr h1
    //== Spec.insert_avl false (spec_convert cmp) metadata_ptr ()
    True)
  =
  let h0 = get () in
  Spec.height_lte_size (v_linked_tree metadata h0);
  let ptr = mmap size 3l in
  let metadata' : ref (Impl.Core.node a) = insert false cmp metadata (ptr, size) in
  let r = (metadata', ptr) in
  let _ = fst r in
  let _ = snd r in
  return r

let free (metadata: t a) (ptr: ptr_t)
  : Steel (t a)
  (linked_tree metadata)
  (fun _ -> linked_tree metadata)
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree metadata h0))
  (ensures fun _ _ _ -> True)
  =
  return metadata


//  let size = find cmp metadata (ptr, 0UL) in
//  if Some? size then (
//    let size = Some?.v size in
//    let status = munmap ptr size in
//    let metadata' = delete cmp metadata (ptr, size) in
//    return metadata'
//  ) else (
//    return metadata
//  )

//let malloc (n: U32.t) (flags: I32.t)
//  : SteelT U64.t
//  emp (fun _ -> emp)
//  =
//  let metadata = create_leaf () in
//  let ptr = malloc2 metadata n flags in
//  sladmit ();
//  return (snd ptr)


(*)
[ok] - find
[ok] - extraction with find
[ok] - basic linking with mmap/munmap
[ok] - correct arguments for mmap in order to have write permissions + RAM and not swap
[ok] - how should corresponding RAM be computed?
=> only first page is being accessed and written on, hence 131072*4096 bytes are allocated
[ok] - extract as library in order to test with LD_PRELOAD

# actually use tree to store metadata
several issues:
1) currently, AVL library rely on stdlib malloc => segfault
=> typeclasses? rewriting it with a hammer?
2) currently, hard to express global variables in F* (or am I missing something?)
=> C bindings hiding the use of a global variable when calling the F*/Steel-extracted function

# basic allocator, whats next
- force reservation of to-be-allocated pages
- trace system calls
- global variables traduction in C
