module SlabsCommon2

module US = FStar.SizeT
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module G = FStar.Ghost
module FU = FStar.UInt
module L = FStar.List.Tot

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

module VR2 = SteelVRefine2
module AL = ArrayList
module ALG = ArrayListGen

open Prelude
open Constants
open Config
open Utils2

open SteelStarSeqUtils
open FStar.Mul

open Guards2
open Quarantine2

inline_for_extraction noextract
let halfp = Steel.FractionalPermission.half_perm Steel.FractionalPermission.full_perm

#push-options "--print_implicits --print_universes"
#set-options "--ide_id_info_off"

let pred1 (x: U32.t) : prop = U32.eq x 0ul == true
let pred2 (x: U32.t) : prop = U32.eq x 1ul == true
let pred3 (x: U32.t) : prop = U32.eq x 2ul == true
let pred4 (x: U32.t) : prop = U32.eq x 3ul == true
let pred5 (x: U32.t) : prop = U32.eq x 4ul == true

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred2 belongs to the second list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
val lemma_partition_and_pred_implies_mem2
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 tl5 sz5 s /\
     pred2 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd2 s)

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred3 belongs to the third list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
val lemma_partition_and_pred_implies_mem3
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 tl5 sz5 s /\
      pred3 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd3 s)

/// If the sequence is partitioned into three lists, then any
/// element satisfying pred2 belongs to the second list.
/// Note, this is only true because pred1, pred2, and pred3
/// are mutually exclusive, which is why we include this lemma
/// here instead of in the ArrayListGen library.
val lemma_partition_and_pred_implies_mem5
  (hd1 hd2 hd3 hd4 hd5 tl5 sz5:nat)
  (s:Seq.seq AL.cell)
  (idx:nat{idx < Seq.length s})
  : Lemma
    (requires
      idx <> ALG.null /\
      ALG.partition s hd1 hd2 hd3 hd4 hd5 /\
      ALG.varraylist_refine pred1 pred2 pred3 pred4 pred5
        hd1 hd2 hd3 hd4 hd5 tl5 sz5 s /\
     pred5 (ALG.get_data (Seq.index s idx)))
    (ensures ALG.mem idx hd5 s)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
let nb_pages (sc: sc_ex)
  : Tot (v:U32.t{
    U32.v sc == U32.v v * U32.v page_size /\
    U32.v v <= US.v max_sc_coef
  })
  =
  Math.Lemmas.euclidean_division_definition (U32.v sc) (U32.v page_size);
  Math.Lemmas.lemma_div_le (U32.v sc) max_sc_ex (U32.v page_size);
  let x = U32.div sc page_size in
  assert (U32.v x == U32.v sc / U32.v page_size);
  assert (U32.v sc % U32.v page_size = 0);
  Math.Lemmas.div_exact_r (U32.v sc) (U32.v page_size);
  x

let slab_region_size
  : v:US.t{
    0 < US.v v /\
    US.v v == US.v metadata_max * U32.v page_size
  }
  = US.mul metadata_max (US.of_u32 page_size)

let slab_size
  : v:US.t{0 < US.v v}
  =
  US.mul (u32_to_sz page_size) (US.mul max_sc_coef 2sz)

let metadata_max_ex
  : v:US.t{
    0 < US.v v /\
    US.v v * US.v max_sc_coef * 2 == US.v metadata_max /\
    slab_region_size = US.mul v slab_size /\
    US.fits (US.v v * US.v slab_size)
  }
  =
  US.div metadata_max (US.mul max_sc_coef 2sz)

#pop-options
#pop-options

//TODO: hiding max_sc_coef behind interface leads to issue
//this is a partial fix
//#push-options "--fuel 0 --ifuel 0 --z3rlimit 50 --split_queries no --query_stats"
//let test
//  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
//  (md_count: US.t{
//    US.v md_count < US.v metadata_max_ex /\
//    US.v (US.mul md_count slab_size) + US.v slab_size
//    ==
//    US.v (US.mul (US.add md_count 1sz) slab_size)
//  })
//  : Lemma
//  (let x = US.mul md_count slab_size in
//  US.v x < A.length slab_region /\
//  //US.v x + US.v slab_size == US.v (US.mul (US.add md_count 1sz) slab_size) /\
//  US.v x + US.v slab_size <= A.length slab_region)
//  = ()


let slab_metadata
  : Type
  = (arr_md: array bool{A.length arr_md = 1})

unfold
let blob (size_class: sc_ex)
  : Type0
  = slab_metadata &
    (arr:array U8.t{A.length arr = US.v slab_size})

let t (size_class: sc_ex) : Type0
  =
  dtuple2
    (Seq.lseq bool 1)
    (fun _ -> option (Seq.lseq U8.t (U32.v size_class)))
  &
  Seq.lseq U8.t (US.v slab_size - U32.v size_class)

/// A trivial, non-informative selector for quarantined and guard pages
inline_for_extraction noextract
val empty_t (size_class:sc_ex) : t size_class

open SteelOptUtils

let slab_vprop_aux (size_class: sc_ex)
  (arr: array U8.t{A.length arr = U32.v size_class})
  (b: bool)
  : vprop
  =
  c2 #(Seq.lseq U8.t (U32.v size_class))
    (not b)
    (A.varray arr)

let slab_vprop_aux_lemma (size_class: sc_ex)
  (arr: array U8.t{A.length arr = U32.v size_class})
  (b: bool)
  : Lemma
  (t_of (slab_vprop_aux size_class arr b)
  ==
  option (Seq.lseq U8.t (U32.v size_class))
  )
  =
  c2_t #(Seq.lseq U8.t (U32.v size_class))
    b
    (A.varray arr)


let slab_vprop (size_class: sc_ex)
  (arr: array U8.t{A.length arr = US.v slab_size})
  (arr_md: slab_metadata)
  : vprop
  =
  vdep
    (A.varray arr_md)
    (fun b -> slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index b 0))
  `star`
  guard_slab size_class (A.split_r arr (u32_to_sz size_class))
  //A.varray (A.split_r arr (u32_to_sz size_class))

#push-options "--z3rlimit 30"
let slab_vprop_lemma (size_class: sc_ex)
  (arr: array U8.t{A.length arr = US.v slab_size})
  (arr_md: slab_metadata)
  : Lemma
  (t_of (slab_vprop size_class arr arr_md)
  ==
  t size_class
  )
  =
  admit ()
  //let aux2 (a a' b c:Type) : Lemma
  //  (requires a == a' /\ b == c)
  //  (ensures dtuple2 a (fun _ -> b) == dtuple2 a' (fun _ -> c))
  //= () in
  //assert_norm (
  //  t_of (vdep
  //    (A.varray arr_md)
  //    (fun (b: Seq.lseq bool 1) ->
  //      slab_vprop_aux size_class arr (Seq.index b 0)))
  //  ==
  //  dtuple2
  //    (Seq.lseq bool (A.length arr_md))
  //    (fun b -> t_of (slab_vprop_aux size_class arr (Seq.index b 0)))
  //);
  //Classical.forall_intro (slab_vprop_aux_lemma size_class arr);
  //assert (forall (b:Seq.lseq bool 1).
  //  t_of (slab_vprop_aux size_class arr (Seq.index b 0))
  //  ==
  //  option (Seq.lseq U8.t (U32.v size_class))
  //);
  //aux2
  //  (Seq.lseq bool (A.length arr_md))
  //  (Seq.lseq bool 1)

#push-options "--z3rlimit 100 --compat_pre_typed_indexed_effects --fuel 1 --ifuel 1"
let intro_slab_vprop (#opened:_) (size_class: sc_ex)
  (arr: array U8.t{A.length arr = US.v slab_size})
  (arr_md: slab_metadata)
  (md: G.erased (Seq.lseq bool 1))
  : SteelGhost unit opened
  (
    slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index (G.reveal md) 0) `star`
    (
      A.varray arr_md `star`
      guard_slab size_class (A.split_r arr (u32_to_sz size_class))
    )
  )
  (fun _ -> slab_vprop size_class arr arr_md)
  (requires fun h0 ->
    G.reveal md == A.asel arr_md h0
  )
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop size_class arr arr_md)
      = h1 (slab_vprop size_class arr arr_md) in
    let x1 : Seq.lseq bool 1 = dfst (fst blob1) in
    x1 == A.asel arr_md h0 /\
    dsnd (fst blob1)
    == h0 (slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index (G.reveal md) 0)) /\
    can_be_split
      (
        slab_vprop_aux size_class
          (A.split_l arr (u32_to_sz size_class))
          (Seq.index (G.reveal md) 0) `star`
        (
          A.varray arr_md `star`
          guard_slab size_class (A.split_r arr (u32_to_sz size_class))
        )
      )
      (guard_slab size_class (A.split_r arr (u32_to_sz size_class))) /\
    snd blob1 == h0 (guard_slab size_class (A.split_r arr (u32_to_sz size_class))) 
  )
  =
  intro_vdep
    (A.varray arr_md)
    (slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index (G.reveal md) 0))
    (fun b -> slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index b 0));
  change_slprop_rel
    (vdep
      (A.varray arr_md)
      (fun b -> slab_vprop_aux size_class
        (A.split_l arr (u32_to_sz size_class))
        (Seq.index b 0))
    `star`
    guard_slab size_class (A.split_r arr (u32_to_sz size_class)))
    (slab_vprop size_class arr arr_md)
    (fun x y -> x == y)
    (fun _ -> admit ());
  assume (
    can_be_split
      (
        slab_vprop_aux size_class
          (A.split_l arr (u32_to_sz size_class))
          (Seq.index (G.reveal md) 0) `star`
        (
          A.varray arr_md `star`
          guard_slab size_class (A.split_r arr (u32_to_sz size_class))
        )
      )
      (guard_slab size_class (A.split_r arr (u32_to_sz size_class)))
  )

let elim_slab_vprop (#opened:_) (size_class: sc_ex)
  (arr: array U8.t{A.length arr = US.v slab_size})
  (arr_md: slab_metadata)
  : SteelGhost (G.erased (Seq.lseq bool 1)) opened
  (slab_vprop size_class arr arr_md)
  (fun b ->
    slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index b 0) `star`
    (
      A.varray arr_md `star`
      guard_slab size_class (A.split_r arr (u32_to_sz size_class))
    )
  )
  (requires fun _ -> True)
  (ensures fun h0 md h1 ->
    let blob0
      : t_of (slab_vprop size_class arr arr_md)
      = h0 (slab_vprop size_class arr arr_md) in
    let x0 : Seq.lseq bool 1 = dfst (fst blob0) in
    G.reveal md == x0 /\
    G.reveal md == A.asel arr_md h1 /\
    dsnd (fst blob0)
    == h1 (slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index md 0)) /\
    can_be_split
      (
        slab_vprop_aux size_class
          (A.split_l arr (u32_to_sz size_class))
          (Seq.index (G.reveal md) 0) `star`
        (
          A.varray arr_md `star`
          guard_slab size_class (A.split_r arr (u32_to_sz size_class))
        )
      )
      (guard_slab size_class (A.split_r arr (u32_to_sz size_class))) /\
    snd blob0 == h1 (guard_slab size_class (A.split_r arr (u32_to_sz size_class)))
  )
  =
  change_slprop_rel
    (slab_vprop size_class arr arr_md)
    (vdep
      (A.varray arr_md)
      (fun b -> slab_vprop_aux size_class
        (A.split_l arr (u32_to_sz size_class))
        (Seq.index b 0))
    `star`
    guard_slab size_class (A.split_r arr (u32_to_sz size_class)))
    (fun x y -> x == y)
    (fun _ -> admit ());
  let md = elim_vdep
    (A.varray arr_md)
    (fun b -> slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index b 0))
  in
  let b
    : G.erased (Seq.lseq bool 1)
    = G.hide (G.reveal md <: Seq.lseq bool 1) in
  sladmit ();
  //change_equal_slprop
  //  (slab_vprop_aux size_class (A.split_l arr (u32_to_sz size_class)) (Seq.index (G.reveal md) 0))
  //  (slab_vprop_aux size_class (A.split_l arr (u32_to_sz size_class)) (Seq.index (G.reveal b) 0));
  //assume (
  //  can_be_split
  //    (
  //      slab_vprop_aux size_class
  //        (A.split_l arr (u32_to_sz size_class))
  //        (Seq.index (G.reveal b) 0) `star`
  //      (
  //        A.varray arr_md `star`
  //        guard_slab size_class (A.split_r arr (u32_to_sz size_class))
  //      )
  //    )
  //    (guard_slab size_class (A.split_r arr (u32_to_sz size_class)))
  //);
  b

let is_empty (b:bool)
  : bool
  =
  not b

let is_full (b:bool)
  : bool
  =
  b

let allocate_slot (size_class: sc_ex)
  (arr: array U8.t{A.length arr = US.v slab_size})
  (md: slab_metadata)
  : Steel (array U8.t)
  (slab_vprop size_class arr md)
  (fun ptr ->
    slab_vprop size_class arr md `star`
    A.varray ptr
  )
  (requires fun h0 ->
     let blob0
     : t_of (slab_vprop size_class arr md)
     = h0 (slab_vprop size_class arr md) in
     let v0 : Seq.lseq bool 1 = dfst (fst blob0) in
     is_empty (Seq.index v0 0)
  )
  (ensures fun h0 r h1 ->
     let blob1
     : t_of (slab_vprop size_class arr md)
     = h1 (slab_vprop size_class arr md) in
     let v1 : Seq.lseq bool 1 = dfst (fst blob1) in
     is_full (Seq.index v1 0) /\
     A.length r = U32.v size_class /\
     same_base_array r arr /\
     A.offset (A.ptr_of r) == A.offset (A.ptr_of arr)
  )
  =
  assert (t_of (A.varray md) == Seq.lseq bool 1);
  let md_as_seq : G.erased (Seq.lseq bool 1)
    = elim_slab_vprop size_class arr md in
  let b = A.index md 0sz in
  A.upd md 0sz (not b);
  let md_as_seq' : G.erased (Seq.lseq bool 1)
    = G.hide (Seq.upd (G.reveal md_as_seq) 0 (not b)) in
  rewrite_slprop
    (slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index md_as_seq 0))
    (slab_vprop_aux size_class
      (A.split_l arr (u32_to_sz size_class))
      (Seq.index md_as_seq' 0) `star`
    A.varray (A.split_l arr (u32_to_sz size_class))
    )
    (fun _ -> admit ());
  intro_slab_vprop size_class arr md md_as_seq';
  let ptr = A.split_l arr (u32_to_sz size_class) in
  change_equal_slprop
    (A.varray (A.split_l arr (u32_to_sz size_class)))
    (A.varray ptr);
  return ptr

let deallocate_slot (size_class: sc_ex)
  (arr: array U8.t{A.length arr = US.v slab_size})
  (md: slab_metadata)
  (ptr: array U8.t)
  //(diff_: US.t)
  : Steel bool
  (
    A.varray ptr `star`
    slab_vprop size_class arr md
  )
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    slab_vprop size_class arr md
  )
  (requires fun h0 ->
    let diff = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of arr) in
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq bool 1 = dfst (fst blob0) in
    same_base_array arr ptr /\
    //US.v diff_ = diff /\
    diff = 0 /\
    A.length ptr == U32.v size_class /\
    is_full (Seq.index v0 0)
  )
  (ensures fun h0 b h1 ->
    let blob0 : t_of (slab_vprop size_class arr md)
      = h0 (slab_vprop size_class arr md) in
    let v0 : Seq.lseq bool 1 = dfst (fst blob0) in
    let blob1 : t_of (slab_vprop size_class arr md)
      = h1 (slab_vprop size_class arr md) in
    let v1 : Seq.lseq bool 1 = dfst (fst blob1) in
    is_empty (Seq.index v1 0) /\
    b
  )
    //(not b ==> v1 == v0))
  =
  assert (t_of (A.varray md) == Seq.lseq bool 1);
  let md_as_seq : G.erased (Seq.lseq bool 1)
    = elim_slab_vprop size_class arr md in
  let b = A.index md 0sz in
  //assert (b);
  A.upd md 0sz false;
  sladmit ();
  //let md_as_seq' : G.erased (Seq.lseq bool 1)
  //  = G.hide (Seq.upd (G.reveal md_as_seq) 0 false) in
  //rewrite_slprop
  //  (slab_vprop_aux size_class
  //    (A.split_l arr (u32_to_sz size_class))
  //    (Seq.index md_as_seq 0))
  //  (slab_vprop_aux size_class
  //    (A.split_l arr (u32_to_sz size_class))
  //    (Seq.index md_as_seq' 0) `star`
  //  A.varray (A.split_l arr (u32_to_sz size_class))
  //  )
  //  (fun _ -> admit ());
  //intro_slab_vprop size_class arr md md_as_seq';
  //let ptr = A.split_l arr (u32_to_sz size_class) in
  //change_equal_slprop
  //  (A.varray (A.split_l arr (u32_to_sz size_class)))
  //  (A.varray ptr);
  return true

#push-options "--z3rlimit 30"
/// Predicates capturing that a slab is empty, partially full, or full respectively
let p_empty (size_class: sc_ex) : blob size_class -> vprop
  =
  fun b ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|), _) -> is_empty (Seq.index s 0) == true)

let p_partial (size_class: sc_ex) : blob size_class -> vprop
  =
  //TODO
  fun b ->
    emp `vrewrite` (fun _ -> empty_t size_class)

let p_full (size_class: sc_ex) : blob size_class -> vprop
  =
  fun b ->
    slab_vprop size_class (snd b) (fst b)
    `VR2.vrefine`
    (fun ((|s,_|),_) -> is_full (Seq.index s 0) == true)

let p_guard (size_class: sc_ex) : blob size_class -> vprop
  =
  //TODO
  fun b ->
    emp `vrewrite` (fun _ -> empty_t size_class)

   // (guard_slab (snd b) `star` A.varray (fst b))
   // `vrewrite`
   // (fun _ -> empty_t sc)
    //(
    //  (guard_slab (snd b) `star` A.varray (fst b))
    //  `VR2.vrefine`
    //  (fun (_,s) -> s `Seq.equal` Seq.create 4 0UL)
    //) `vrewrite` (fun _ -> empty_t sc)

let p_quarantine (size_class: sc_ex) : blob size_class -> vprop
  =
  fun b ->
    (
      (quarantine_slab size_class
        (A.split_l (snd b) (u32_to_sz size_class)) `star`
      (A.varray (fst b) `vrefine` zf_b) `star`
      guard_slab size_class (A.split_r (snd b) (u32_to_sz size_class)))
    ) `vrewrite` (fun _ ->  empty_t size_class)

val p_empty_unpack (#opened:_)
  (sc: sc_ex)
  (b1 b2: blob sc)
  : SteelGhost unit opened
  ((p_empty sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq bool 1 = dfst (fst blob1) in
    b1 == b2 /\
    is_empty (Seq.index v1 0) /\
    h0 ((p_empty sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )

val p_full_unpack (#opened:_)
  (sc: sc_ex)
  (b1 b2: blob sc)
  : SteelGhost unit opened
  ((p_full sc) b1)
  (fun _ -> slab_vprop sc (snd b2) (fst b2))
  (requires fun _ -> b1 == b2)
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop sc (snd b2) (fst b2))
      = h1 (slab_vprop sc (snd b2) (fst b2)) in
    let v1 : Seq.lseq bool 1 = dfst (fst blob1) in
    b1 == b2 /\
    is_full (Seq.index v1 0) /\
    h0 ((p_full sc) b1)
    ==
    h1 (slab_vprop sc (snd b2) (fst b2))
  )

val p_empty_pack (#opened:_)
  (sc: sc_ex)
  (b1 b2: blob sc)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_empty sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq bool 1 = dfst (fst blob0) in
    is_empty (Seq.index v0 0) /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_empty sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

val p_full_pack (#opened:_)
  (sc: sc_ex)
  (b1 b2: blob sc)
  : SteelGhost unit opened
  (slab_vprop sc (snd b1) (fst b1))
  (fun _ -> (p_full sc) b2)
  (requires fun h0 ->
    let blob0
      : t_of (slab_vprop sc (snd b1) (fst b1))
      = h0 (slab_vprop sc (snd b1) (fst b1)) in
    let v0 : Seq.lseq bool 1 = dfst (fst blob0) in
    is_full (Seq.index v0 0) /\
    b1 == b2
  )
  (ensures fun h0 _ h1 ->
    b1 == b2 /\
    h1 ((p_full sc) b2)
    ==
    h0 (slab_vprop sc (snd b1) (fst b1))
  )

//val p_guard_pack (#opened:_)
//  (size_class:sc)
//  (b: blob)
//  : SteelGhostT unit opened
//  (guard_slab (snd b) `star` A.varray (fst b))
//  (fun _ -> p_guard size_class b)
//


//(quarantine_slab size_class
//  (A.split_l (snd b) (u32_to_sz size_class)) `star`
//A.varray (fst b) `star`
//A.varray (A.split_r (snd b) (u32_to_sz size_class)))
//`VR2.vrefine`
//(fun ((_,s),_) -> s `Seq.equal` Seq.create 1 true)

val p_quarantine_pack (#opened:_)
  (size_class:sc_ex)
  (b: blob size_class)
  : SteelGhost unit opened
  (quarantine_slab size_class (A.split_l (snd b) (u32_to_sz size_class)) `star`
    guard_slab size_class (A.split_r (snd b) (u32_to_sz size_class)) `star`
    A.varray (fst b))
  (fun _ -> p_quarantine size_class b)
  (requires fun h0 ->
    let s : Seq.lseq bool 1 = A.asel (fst b) h0 in
    is_empty (Seq.index s 0)
  )
  (ensures fun _ _ _ -> True)

val p_quarantine_unpack (#opened:_)
  (size_class:sc_ex)
  (b: blob size_class)
  : SteelGhost unit opened
  (p_quarantine size_class b)
  (fun _ ->
    quarantine_slab size_class (A.split_l (snd b) (u32_to_sz size_class)) `star`
    guard_slab size_class (A.split_r (snd b) (u32_to_sz size_class)) `star`
    A.varray (fst b)
  )
  (requires fun _ -> True)
  (ensures fun _ _ h1 ->
    let s : Seq.lseq bool 1 = A.asel (fst b) h1 in
    is_empty (Seq.index s 0)
  )

let intro_slab_vprop_empty (size_class: sc_ex)
  (arr: array U8.t{A.length arr = US.v slab_size})
  (arr_md: slab_metadata)
  : Steel unit
  (
    A.varray arr `star`
    A.varray arr_md
  )
  (fun _ -> slab_vprop size_class arr arr_md)
  (requires fun h0 ->
    is_empty (Seq.index (A.asel arr_md h0) 0)
  )
  (ensures fun h0 _ h1 ->
    let blob1
      : t_of (slab_vprop size_class arr arr_md)
      = h1 (slab_vprop size_class arr arr_md) in
    let x1 : Seq.lseq bool 1 = dfst (fst blob1) in
    x1 == A.asel arr_md h0
  )
  =
  A.ghost_split arr (u32_to_sz size_class);
  let b : G.erased (Seq.lseq bool 1)
    = gget (A.varray arr_md) in
  assert (is_empty (Seq.index (G.reveal b) 0));
  change_slprop_rel
    (A.varray (A.split_l arr (u32_to_sz size_class)))
    (some_as_vp #(Seq.lseq U8.t (U32.v size_class))
      (A.varray (A.split_l arr (u32_to_sz size_class))))
    (fun
      (x: t_of (A.varray (A.split_l arr (u32_to_sz size_class))))
      (y: t_of (some_as_vp #(Seq.lseq U8.t (U32.v size_class))
        (A.varray (A.split_l arr (u32_to_sz size_class)))))
      ->
      let x' : Seq.lseq U8.t (U32.v size_class) = x in
      let y' : option (Seq.lseq U8.t (U32.v size_class)) = y in
      y' == Some x')
    (fun m -> ());
  change_equal_slprop
    (some_as_vp #(Seq.lseq U8.t (U32.v size_class))
      (A.varray (A.split_l arr (u32_to_sz size_class))))
    (slab_vprop_aux size_class (A.split_l arr (u32_to_sz size_class)) (Seq.index (G.reveal b) 0));
  mmap_trap_guard
    size_class
    (A.split_r arr (u32_to_sz size_class))
    (US.sub slab_size (u32_to_sz size_class));
  intro_slab_vprop size_class
    arr
    arr_md
    b

//val p_empty_unpack (#opened:_)
//  (sc: sc)
//  (b1 b2: blob)
//  : SteelGhost unit opened
//  ((p_empty sc) b1)
//  (fun _ -> slab_vprop sc (snd b2) (fst b2))
//  (requires fun _ -> b1 == b2)
//  (ensures fun h0 _ h1 ->
//    let blob1
//      : t_of (slab_vprop sc (snd b2) (fst b2))
//      = h1 (slab_vprop sc (snd b2) (fst b2)) in
//    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
//    b1 == b2 /\
//    is_empty sc v1 /\
//    h0 ((p_empty sc) b1)
//    ==
//    h1 (slab_vprop sc (snd b2) (fst b2))
//  )
//
//val p_partial_unpack (#opened:_)
//  (sc: sc)
//  (b1: blob)
//  (b2: blob)
//  : SteelGhost unit opened
//  ((p_partial sc) b1)
//  (fun _ -> slab_vprop sc (snd b2) (fst b2))
//  (requires fun _ -> b1 == b2)
//  (ensures fun h0 _ h1 ->
//    let blob1
//      : t_of (slab_vprop sc (snd b2) (fst b2))
//      = h1 (slab_vprop sc (snd b2) (fst b2)) in
//    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
//    b1 == b2 /\
//    is_partial sc v1 /\
//    h0 ((p_partial sc) b1)
//    ==
//    h1 (slab_vprop sc (snd b2) (fst b2))
//  )
//
//val p_full_unpack (#opened:_)
//  (sc: sc)
//  (b1: blob)
//  (b2: blob)
//  : SteelGhost unit opened
//  ((p_full sc) b1)
//  (fun _ -> slab_vprop sc (snd b2) (fst b2))
//  (requires fun _ -> b1 == b2)
//  (ensures fun h0 _ h1 ->
//    let blob1
//      : t_of (slab_vprop sc (snd b2) (fst b2))
//      = h1 (slab_vprop sc (snd b2) (fst b2)) in
//    let v1 : Seq.lseq U64.t 4 = dfst (fst blob1) in
//    b1 == b2 /\
//    is_full sc v1 /\
//    h0 ((p_full sc) b1)
//    ==
//    h1 (slab_vprop sc (snd b2) (fst b2))
//  )
//
//val p_empty_pack (#opened:_)
//  (sc: sc)
//  (b1: blob)
//  (b2: blob)
//  : SteelGhost unit opened
//  (slab_vprop sc (snd b1) (fst b1))
//  (fun _ -> (p_empty sc) b2)
//  (requires fun h0 ->
//    let blob0
//      : t_of (slab_vprop sc (snd b1) (fst b1))
//      = h0 (slab_vprop sc (snd b1) (fst b1)) in
//    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
//    is_empty sc v0 /\
//    b1 == b2
//  )
//  (ensures fun h0 _ h1 ->
//    b1 == b2 /\
//    h1 ((p_empty sc) b2)
//    ==
//    h0 (slab_vprop sc (snd b1) (fst b1))
//  )
//
//val p_partial_pack (#opened:_)
//  (sc: sc)
//  (b1: blob)
//  (b2: blob)
//  : SteelGhost unit opened
//  (slab_vprop sc (snd b1) (fst b1))
//  (fun _ -> (p_partial sc) b2)
//  (requires fun h0 ->
//    let blob0
//      : t_of (slab_vprop sc (snd b1) (fst b1))
//      = h0 (slab_vprop sc (snd b1) (fst b1)) in
//    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
//    is_partial sc v0 /\
//    b1 == b2
//  )
//  (ensures fun h0 _ h1 ->
//    b1 == b2 /\
//    h1 ((p_partial sc) b2)
//    ==
//    h0 (slab_vprop sc (snd b1) (fst b1))
//  )
//
//val p_full_pack (#opened:_)
//  (sc: sc)
//  (b1: blob)
//  (b2: blob)
//  : SteelGhost unit opened
//  (slab_vprop sc (snd b1) (fst b1))
//  (fun _ -> (p_full sc) b2)
//  (requires fun h0 ->
//    let blob0
//      : t_of (slab_vprop sc (snd b1) (fst b1))
//      = h0 (slab_vprop sc (snd b1) (fst b1)) in
//    let v0 : Seq.lseq U64.t 4 = dfst (fst blob0) in
//    is_full sc v0 /\
//    b1 == b2
//  )
//  (ensures fun h0 _ h1 ->
//    b1 == b2 /\
//    h1 ((p_full sc) b2)
//    ==
//    h0 (slab_vprop sc (snd b1) (fst b1))
//  )
//
//val p_guard_pack (#opened:_)
//  (size_class:sc)
//  (b: blob)
//  : SteelGhostT unit opened
//  (guard_slab (snd b) `star` A.varray (fst b))
//  (fun _ -> p_guard size_class b)
//
//val p_quarantine_pack (#opened:_)
//  (size_class:sc)
//  (b: blob)
//  : SteelGhost unit opened
//  (quarantine_slab (snd b) `star` A.varray (fst b))
//  (fun _ -> p_quarantine size_class b)
//  (requires fun h0 ->
//    let s : Seq.lseq U64.t 4 = A.asel (fst b) h0 in
//    s `Seq.equal` Seq.create 4 0UL
//  )
//  (ensures fun _ _ _ -> True)
//
//val p_quarantine_unpack (#opened:_)
//  (size_class:sc)
//  (b: blob)
//  : SteelGhost unit opened
//  (p_quarantine size_class b)
//  (fun _ -> quarantine_slab (snd b) `star` A.varray (fst b))
//  (requires fun _ -> True)
//  (ensures fun _ _ h1 ->
//    let s : Seq.lseq U64.t 4 = A.asel (fst b) h1 in
//    s `Seq.equal` Seq.create 4 0UL
//  )

/// Retrieving the metadata bitmap at index [md_count] in array [md_bm_region]
inline_for_extraction noextract
val md_bm_array
  (md_bm_region: array bool)
  (md_count: US.t)
  : Pure (array bool)
  (requires
    A.length md_bm_region = US.v metadata_max_ex /\
    US.v md_count < US.v metadata_max_ex)
  (ensures fun r ->
    A.length r = 1 /\
    same_base_array r md_bm_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of md_bm_region) + US.v md_count
  )

/// Retrieving the slab at index [md_count] in the [slab_region]
inline_for_extraction noextract
val slab_array
  (slab_region: array U8.t)
  (md_count: US.t)
  : Pure (array U8.t)
  (requires
    A.length slab_region = US.v metadata_max_ex * US.v slab_size /\
    US.v md_count < US.v metadata_max_ex
  )
  (ensures fun r ->
    A.length r = US.v slab_size /\
    same_base_array r slab_region /\
    A.offset (A.ptr_of r) == A.offset (A.ptr_of slab_region) + US.v md_count * US.v slab_size
  )

val pack_slab_array (#opened:_)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_count: US.t{US.v md_count < US.v metadata_max_ex})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r slab_region (US.mul md_count slab_size)) slab_size))
    (fun _ -> A.varray (slab_array slab_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r slab_region (US.mul md_count slab_size)) slab_size) h0 ==
      A.asel (slab_array slab_region md_count) h1)

val pack_md_bm_array (#opened:_)
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_count: US.t{US.v md_count < US.v metadata_max_ex})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_bm_region md_count) 1sz))
    (fun _ -> A.varray (md_bm_array md_bm_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_bm_region md_count) 1sz) h0 ==
      A.asel (md_bm_array md_bm_region md_count) h1)

/// Retrieving the metadata status indicator at index [md_count] in array [md_region]
inline_for_extraction noextract
val md_array
  (md_region: array AL.cell)
  (md_count: US.t)
  : Pure (array AL.cell)
  (requires
    A.length md_region = US.v metadata_max_ex /\
    US.v md_count < US.v metadata_max_ex)
  (ensures fun r ->
    A.length r = 1 /\
    same_base_array r md_region /\
    True
  )

val pack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: US.t{US.v md_count < US.v metadata_max_ex})
  : SteelGhost unit opened
    (A.varray (A.split_l (A.split_r md_region md_count) 1sz))
    (fun _ -> A.varray (md_array md_region md_count))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region md_count) 1sz) h0 ==
      A.asel (md_array md_region md_count) h1)

val unpack_md_array (#opened:_)
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: US.t{US.v md_count < US.v metadata_max_ex})
  : SteelGhost unit opened
    (A.varray (md_array md_region md_count))
    (fun _ -> A.varray (A.split_l (A.split_r md_region md_count) 1sz))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel (A.split_l (A.split_r md_region md_count) 1sz) h1 ==
      A.asel (md_array md_region md_count) h0)

(** VProps related to slabs *)

// TODO: Document what the vprops represent

let f
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: Seq.lseq AL.status (US.v md_count_v))
  (i: US.t{US.v i < US.v md_count_v})
  : vprop
  =
  match Seq.index md_region_lv (US.v i) with
  | 0ul -> p_empty size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 1ul -> p_partial size_class (md_bm_array md_bm_region i, slab_array slab_region i)//should not happen
  | 2ul -> p_full size_class (md_bm_array md_bm_region i, slab_array slab_region i)
  | 3ul -> p_guard size_class (md_bm_array md_bm_region i, slab_array slab_region i)//should not happen
  | 4ul -> p_quarantine size_class (md_bm_array md_bm_region i, slab_array slab_region i)

val f_lemma
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: Seq.lseq AL.status (US.v md_count_v))
  (i: US.t{US.v i < US.v md_count_v})
  : Lemma
  (t_of (f size_class slab_region md_bm_region md_count_v md_region_lv i)
  == t size_class)

let ind_varraylist_aux2
  (r_varraylist: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  : vprop
  =
  AL.varraylist pred1 pred2 pred3 pred4 pred5 r_varraylist
    (US.v (Seq.index idxs 0))
    (US.v (Seq.index idxs 1))
    (US.v (Seq.index idxs 2))
    (US.v (Seq.index idxs 3))
    (US.v (Seq.index idxs 4))
    (US.v (Seq.index idxs 5))
    (US.v (Seq.index idxs 6))

val ind_varraylist_aux2_lemma
  (r_varraylist: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : Lemma
  (requires
    idx1 == Seq.index idxs 0 /\
    idx2 == Seq.index idxs 1 /\
    idx3 == Seq.index idxs 2 /\
    idx4 == Seq.index idxs 3 /\
    idx5 == Seq.index idxs 4 /\
    idx6 == Seq.index idxs 5 /\
    idx7 == Seq.index idxs 6
  )
  (ensures (
    let l : list US.t
      = [ idx1; idx2; idx3; idx4; idx5; idx6; idx7 ] in
    let s : Seq.seq US.t = Seq.seq_of_list l in
    List.Tot.length l == 7 /\
    Seq.length s == 7 /\
    s `Seq.equal` idxs /\
    ind_varraylist_aux2 r_varraylist idxs
    ==
    AL.varraylist pred1 pred2 pred3 pred4 pred5 r_varraylist
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4)
      (US.v idx5) (US.v idx6) (US.v idx7)
  ))

#pop-options

let ind_varraylist_aux_refinement
  (r: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  (s: t_of (ind_varraylist_aux2 r idxs))
  : prop
  =
  ALG.partition #AL.status s
    (US.v (Seq.index idxs 0))
    (US.v (Seq.index idxs 1))
    (US.v (Seq.index idxs 2))
    (US.v (Seq.index idxs 3))
    (US.v (Seq.index idxs 4))

let ind_varraylist_aux
  (r: A.array AL.cell)
  (idxs: Seq.lseq US.t 7)
  : vprop
  =
  ind_varraylist_aux2 r idxs
  `vrefine`
  ind_varraylist_aux_refinement r idxs

let ind_varraylist
  (r: A.array AL.cell)
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  : vprop
  =
  A.varray r_idxs `vdep` ind_varraylist_aux r

let left_vprop1
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  : vprop
  =
  ind_varraylist
    (A.split_l md_region md_count_v)
    r_idxs

let left_vprop2_aux
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (x: Seq.lseq AL.status (US.v md_count_v))
  : vprop
  =
  starseq
    #(pos:US.t{US.v pos < US.v md_count_v})
    #(t size_class)
    (f size_class slab_region md_bm_region md_count_v x)
    (f_lemma size_class slab_region md_bm_region md_count_v x)
    (SeqUtils.init_us_refined (US.v md_count_v))

let left_vprop2
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (x: t_of (ind_varraylist (A.split_l md_region md_count_v) r_idxs))
  : vprop
  = starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (f_lemma size_class slab_region md_bm_region md_count_v (ALG.dataify (dsnd x)))
      (SeqUtils.init_us_refined (US.v md_count_v))

let left_vprop
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (r_idxs: A.array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  =
  left_vprop1 md_region r_idxs md_count_v
  `vdep`
  left_vprop2 size_class slab_region md_bm_region md_region r_idxs md_count_v

unfold
let vrefinedep_prop (x:US.t) : prop =
  US.v x <= US.v metadata_max_ex /\
  US.v x <> AL.null

let right_vprop
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (v: US.t{US.v v <= US.v metadata_max_ex})
  : vprop
  =
  (A.varray (A.split_r slab_region (US.mul v slab_size))
    `vrefine` zf_u8) `star`
  (A.varray (A.split_r md_bm_region v)
    `vrefine` zf_b) `star`
  A.varray (A.split_r md_region v)

let size_class_vprop_aux
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (r_idxs: array US.t{A.length r_idxs = 7})
  (v: US.t{US.v v <= US.v metadata_max_ex == true})
  : vprop
  =
  left_vprop size_class
    slab_region md_bm_region md_region
    r_idxs v `star`
  right_vprop
    slab_region md_bm_region md_region v

open SteelVRefineDep

val pack_3
  (#opened:_)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx1 idx2 idx3 idx4 idx5 idx6 idx7: US.t)
  : SteelGhost unit opened
  (
    vptr md_count `star`
    A.varray r_idxs `star`
    (AL.varraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (f_lemma size_class slab_region md_bm_region md_count_v (G.reveal md_region_lv))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let gs0 = AL.v_arraylist pred1 pred2 pred3 pred4 pred5
      (A.split_l md_region md_count_v)
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5) (US.v idx6) (US.v idx7) h0 in
    let idxs0 = A.asel r_idxs h0 in
    US.v md_count_v <> AL.null /\
    sel md_count h0 == md_count_v /\
    Seq.index idxs0 0 == idx1 /\
    Seq.index idxs0 1 == idx2 /\
    Seq.index idxs0 2 == idx3 /\
    Seq.index idxs0 3 == idx4 /\
    Seq.index idxs0 4 == idx5 /\
    Seq.index idxs0 5 == idx6 /\
    Seq.index idxs0 6 == idx7 /\
    ALG.dataify gs0 `Seq.equal` G.reveal md_region_lv /\
    ALG.partition #AL.status gs0
      (US.v idx1) (US.v idx2) (US.v idx3) (US.v idx4) (US.v idx5)
  )
  (ensures fun _ _ h1 ->
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
    ) in
    md_count_v == dfst blob1)

val pack_slab_starseq
  (#opened:_)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  //(r1 r2 r3 r4 r5: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx: US.t{US.v idx < US.v md_count_v})
  (v: AL.status)
  : SteelGhost unit opened
  (
    slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx) `star`
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) v))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx))
    = h0 (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx)) in
    let md : Seq.lseq bool 1 = dfst (fst md_blob) in
    v <> 4ul /\
    v <> 3ul /\
    v <> 1ul /\
    (v == 2ul ==> is_full (Seq.index md 0)) /\
    (v == 0ul ==> is_empty (Seq.index md 0)) /\
    idx <> AL.null_ptr
  )
  (ensures fun _ _ _ -> True)

inline_for_extraction noextract
val upd_and_pack_slab_starseq_quarantine
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  (md_region_lv: G.erased (Seq.lseq AL.status (US.v md_count_v)))
  (idx: US.t{US.v idx < US.v md_count_v})
  : Steel unit
  (
    slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx) `star`
    (starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) 0 (US.v idx)) `star`
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v md_region_lv)
      (f_lemma size_class slab_region md_bm_region md_count_v md_region_lv)
      (Seq.slice (SeqUtils.init_us_refined (US.v md_count_v)) (US.v idx + 1) (Seq.length (SeqUtils.init_us_refined (US.v md_count_v)))))
  )
  (fun _ ->
    starseq
      #(pos:US.t{US.v pos < US.v md_count_v})
      #(t size_class)
      (f size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) 4ul))
      (f_lemma size_class slab_region md_bm_region md_count_v (Seq.upd md_region_lv (US.v idx) 4ul))
      (SeqUtils.init_us_refined (US.v md_count_v))
  )
  (requires fun h0 ->
    let md_blob : t_of (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx))
    = h0 (slab_vprop size_class
      (slab_array slab_region idx)
      (md_bm_array md_bm_region idx)) in
    let md : Seq.lseq bool 1 = dfst (fst md_blob) in
    is_empty (Seq.index md 0)
  )
  (ensures fun _ _ _ -> True)

val pack_right_and_refactor_vrefine_dep
  (#opened:_)
  (size_class: sc_ex)
  (slab_region: array U8.t{A.length slab_region = US.v metadata_max_ex * US.v slab_size})
  (md_bm_region: array bool{A.length md_bm_region = US.v metadata_max_ex})
  (md_region: array AL.cell{A.length md_region = US.v metadata_max_ex})
  (md_count: ref US.t)
  (r_idxs: array US.t{A.length r_idxs = 7})
  (md_count_v: US.t{US.v md_count_v <= US.v metadata_max_ex})
  : SteelGhost unit opened
  (
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
    `star`
    right_vprop slab_region md_bm_region md_region md_count_v
  )
  (fun _ ->
    vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
  )
  (requires fun h0 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
    ) in
    md_count_v == dfst blob0
  )
  (ensures fun h0 _ h1 ->
    let blob0
      = h0 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (left_vprop size_class slab_region md_bm_region md_region r_idxs)
    ) in
    let blob1
      = h1 (vrefinedep
      (vptr md_count)
      vrefinedep_prop
      (size_class_vprop_aux size_class slab_region md_bm_region md_region r_idxs)
    ) in
    dfst blob0 == dfst blob1
  )
