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

assume val get_metadata_pure (_: unit) : t a

assume val get_metadata (_: unit) : Steel (t a)
  (linked_tree (get_metadata_pure ()))
  (fun r -> linked_tree r)
  (requires fun _ -> True)
  (ensures fun _ r _ -> get_metadata_pure () == r)

assume val set_metadata (m: t a) : Steel unit
  (linked_tree m)
  (fun _ -> linked_tree (get_metadata_pure ()))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> get_metadata_pure () == m)


let mmap (len: U64.t) (prot: I32.t)
  //= Mman.mmap 0UL len prot 33l (-1l) 0ul
  //MAP_PRIVATE instead of MAP_ANON (avoid filling the disk...)
  //34l = MAP_PRIVATE|MAP_ANON
  = Mman.mmap 0UL len prot 34l (-1l) 0ul

let munmap = Mman.munmap

let cmp (x y: U64.t & U64.t) : I64.t
  =
  let x = fst x in
  let y = fst y in
  if U64.gt x y then 1L
  else if U64.eq x y then 0L
  else -1L

let create_leaf = Impl.Trees.M.create_leaf

inline_for_extraction noextract
let insert = Impl.Mono.insert_avl

inline_for_extraction noextract
let get_size = Impl.Mono.sot_wds
//let delete = Impl.Mono.delete_avl
//let mem = Impl.Mono.member
let find = Map.M.find

//assume val metadata_ptr: t a

let malloc (size: size_t)
  : Steel (ptr_t)
  (linked_tree (get_metadata_pure ()))
  (fun _ -> linked_tree (get_metadata_pure ()))
  (requires fun h0 ->
    let metadata = get_metadata_pure () in
    Spec.is_avl (spec_convert cmp)
      (v_linked_tree metadata h0) /\
    Spec.size_of_tree (v_linked_tree metadata h0) < 100)
  (ensures fun h0 r h1 ->
    let metadata = get_metadata_pure () in
    Spec.is_avl (spec_convert cmp)
      (v_linked_tree metadata h1) /\
    //v_linked_tree metadata_ptr h1
    //== Spec.insert_avl false (spec_convert cmp) metadata_ptr ()
    True)
  =
  let metadata = get_metadata () in
  //let h0 = get () in
  //Spec.height_lte_size (v_linked_tree metadata h0);
  let ptr = mmap size 3l in
  admit ();
  let metadata' = insert false cmp metadata (ptr, size) in
  set_metadata metadata';
  return ptr

let free (ptr: ptr_t)
  : Steel (t a)
  (linked_tree (get_metadata_pure ()))
  (fun _ -> linked_tree (get_metadata_pure ()))
  (requires fun h0 ->
    let metadata = get_metadata_pure () in
    Spec.is_avl (spec_convert cmp) (v_linked_tree metadata h0))
  (ensures fun _ _ _ -> True)
  =
  let metadata = get_metadata () in
  admit ();
  let size = find cmp metadata (ptr, 0UL) in
  if Some? size then (
    let size = Some?.v size in
    let status = munmap ptr size in
    let metadata' = delete cmp metadata (ptr, size) in
    set_metadata metadata';
    return metadata'
  ) else (
    set_metadata metadata;
    return metadata
  )

let size (_:unit) : SteelT U64.t
  (linked_tree (get_metadata_pure ()))
  (fun _ -> linked_tree (get_metadata_pure ()))
  =
  let metadata = get_metadata () in
  let size = get_size metadata in
  sladmit ();
  return size





(*)
[ok] - find
[ok] - extraction with find
[ok] - basic linking with mmap/munmap
[ok] - correct arguments for mmap in order to have write permissions + RAM and not swap
[ok] - how should corresponding RAM be computed?
=> only first page is being accessed and written on, hence 131072*4096 bytes are allocated
[ok] - extract as library in order to test with LD_PRELOAD

[ok] actually use tree to store metadata
several issues:
1) currently, AVL library rely on stdlib malloc => segfault
=> typeclasses? rewriting it with a hammer?
2) currently, hard to express global variables in F* (or am I missing something?)
=> C bindings hiding the use of a global variable when calling the F*/Steel-extracted function

# basic allocator, whats next
- force reservation of to-be-allocated pages
- trace system calls
- global variables traduction in C
