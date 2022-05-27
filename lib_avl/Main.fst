module Main

open Steel.Effect.Atomic
open Steel.Effect

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
//open Impl
open Map

#set-options "--ide_id_info_off"

// machine representation
unfold let ptr_t = U64.t
unfold let size_t = U32.t

let a = ptr_t & size_t

let t = Impl.Core.t
let linked_tree = Impl.Core.linked_tree

//noextract
//assume val mmap (size: size_t) : ptr_t
//noextract
//assume val munmap (addr: ptr_t) (size: size_t) : ptr_t

inline_for_extraction noextract
let mmap (len: U32.t) (prot: I32.t)
  //= Mman.mmap 0UL len prot 33l (-1l) 0ul
  //MAP_PRIVATE instead of MAP_ANON (avoid filling the disk...)
  //34l = MAP_PRIVATE|MAP_ANON
  = Mman.mmap 0UL len prot 34l (-1l) 0ul

inline_for_extraction noextract
let munmap = Mman.munmap

let cmp (x y: U64.t & U32.t) : I64.t
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
let create_leaf = Impl.Trees.create_leaf #(ptr_t & size_t)
let insert = insert #ptr_t #size_t
let delete = delete #ptr_t #size_t
let mem = mem #ptr_t #size_t
let find = find #ptr_t #size_t

let malloc2 (metadata: t a) (size: size_t) (flags: I32.t)
  : Steel (t a & ptr_t)
  (linked_tree metadata)
  (fun r -> linked_tree (fst r))
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (Impl.v_linked_tree metadata h0) /\
    Spec.size_of_tree (Impl.v_linked_tree metadata h0) < 100)
  (ensures fun _ _ _ -> True)
  =
  let h0 = get () in
  Spec.height_lte_size (Impl.v_linked_tree metadata h0);
  let ptr = mmap size flags in
  //let metadata' = insert false cmp metadata (ptr, size) in
  let metadata' = metadata in
  return (metadata', ptr)

let free (metadata: t a) (ptr: ptr_t)
  : Steel (t a)
  (linked_tree metadata)
  (fun r -> linked_tree r)
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (Impl.v_linked_tree metadata h0))
  (ensures fun _ _ _ -> True)
  =
  let size = find cmp metadata ptr 0ul in
  if Some? size then (
    let size = Some?.v size in
    let status = munmap ptr size in
    //let metadata' = delete cmp metadata (ptr, size) in
    let metadata' = delete cmp metadata (0UL, 0ul) in
    return metadata'
  ) else (
    return metadata
  )

let malloc (n: U32.t) (flags: I32.t)
  : SteelT U64.t
  emp (fun _ -> emp)
  =
  let metadata = create_leaf () in
  let ptr = malloc2 metadata n flags in
  sladmit ();
  return (snd ptr)


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
