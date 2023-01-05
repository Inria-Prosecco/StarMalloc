module SlabsOverlay

open Utils2
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array

open Slabs

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module SL = Selectors.LList

module SM = Steel.Memory
module G = FStar.Ghost

val vrefinedep_hp
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  : Tot (SM.slprop u#1)

[@__steel_reduce__]
let vrefinedep_t
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( t_of (vrefine v p) -> Tot vprop))
  : Tot Type
  =
  dtuple2 (t_of (vrefine v p)) (fun x -> t_of (f x))

val vrefinedep_sel
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : Tot (selector (vrefinedep_t v p f) (vrefinedep_hp v p f))

[@@__steel_reduce__]
let vrefinedep'
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : Tot vprop' = {
  hp = vrefinedep_hp v p f;
  t = vrefinedep_t v p f;
  sel = vrefinedep_sel v p f;
}
[@@__steel_reduce__]
let vrefinedep
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  = VUnit (vrefinedep' v p f)

val elim_vrefinedep
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : SteelGhost (G.erased (t_of (vrefine v p))) opened
  (vrefinedep v p f)
  (fun res -> v `star` f (G.reveal res))
  (requires fun _ -> True)
  (ensures fun h res h' ->
    let (res : normal (t_of v){p res}) = res in
    p res /\
    G.reveal res == h' v /\
    (let fs : x:t_of v{p x} = h' v in
    let sn : t_of (f (G.reveal res)) = h' (f (G.reveal res)) in
    let x2 = h (vrefinedep v p f) in
    G.reveal res == fs /\
    dfst x2 == fs /\
    dsnd x2 == sn /\
    True)
  )

val intro_vrefinedep
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  (f': vprop)
  : SteelGhost unit opened
  (v `star` f')
  (fun _ -> vrefinedep v p f)
  (requires fun h ->
    p (h v) /\
    f' == f (h v))
  (ensures fun h _ h' ->
    p (h v) /\
    f' == f (h v) /\
    (let x2 = h' (vrefinedep v p f) in
    let sn : t_of f' = h f' in
    dfst x2 == h v /\
    dsnd x2 == sn)
  )

#push-options "--compat_pre_typed_indexed_effects"
#push-options "--z3rlimit 20"
let vrefinedep_idem
  (#opened:_)
  (v: vprop)
  (p: ( (t_of v) -> Tot prop))
  (f: ( (t_of (vrefine v p)) -> Tot vprop))
  : SteelGhost unit opened
  (vrefinedep v p f)
  (fun _ -> vrefinedep v p f)
  (requires fun _ -> True)
  (ensures fun h _ h' ->
    h (vrefinedep v p f)
    ==
    h' (vrefinedep v p f)
  )
  =
  //let h0 = get () in
  let x0 = gget (vrefinedep v p f) in
  let x = elim_vrefinedep v p f in
  intro_vrefinedep v p  f (f (G.reveal x));
  //let h1 = get () in
  let x1 = gget (vrefinedep v p f) in
  assert (dfst x0 == dfst x1);
  assert (dsnd x0 == dsnd x1);
  //assert (x0 == x1);
  ()
#pop-options
#pop-options

open FStar.Mul

// #push-options "--compat_pre_typed_indexed_effects --compat_pre_core 0"
// val alloc_metadata2
//   (size_class: sc)
//   (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//   (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//   (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
//   (md_count: ref U32.t)
//   : Steel (SL.t blob)
//   //: Steel unit
//   (
//     vrefinedep
//       (vptr md_count)
//       //TODO: hideous coercion
//       (fun x -> U32.v x < U32.v metadata_max == true)
//       (fun v ->
//         A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
//         A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
//         A.varray (A.split_r md_region (u32_to_sz v)))
//   )
//   (fun r ->
//     SL.llist (p_empty size_class) r `star`
//     vrefinedep
//       (vptr md_count)
//       //TODO: hideous coercion
//       (fun x -> U32.v x <= U32.v metadata_max == true)
//       (fun v ->
//         A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
//         A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
//         A.varray (A.split_r md_region (u32_to_sz v)))
//   )
//   (requires fun h0 -> True)
//   (ensures fun h0 r h1 -> True
//     //TODO FIXME: fails with this postcondition
//     // FStar.List.Tot.length (SL.v_llist (p_empty size_class) r h1) == 1
// //    /\ sel md_count h1 = U32.add (sel md_count h0) 1ul
//   )

#push-options "--compat_pre_typed_indexed_effects --z3rlimit 100"
let alloc_metadata2
  (size_class: sc)
  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
  (md_count: ref U32.t)
  : Steel (SL.t blob)
  //: Steel unit
  (
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x < U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (fun r ->
    SL.llist (p_empty size_class) r `star`
    vrefinedep
      (vptr md_count)
      //TODO: hideous coercion
      (fun x -> U32.v x <= U32.v metadata_max == true)
      (fun v ->
        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
        A.varray (A.split_r md_region (u32_to_sz v)))
  )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True
    //TODO FIXME: fails with this postcondition
    //L.length (SL.v_llist (p_empty size_class) r h1) = 1
    ///\ sel md_count h1 = U32.add (sel md_count h0) 1ul
  )
  =
  let x
    //: G.erased (x:U32.t{U32.v x < U32.v metadata_max == true})
    = elim_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x < U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz v)))
  in
  let x'
    : G.erased (x:U32.t{U32.v x < U32.v metadata_max})
    = G.hide (G.reveal x <: x:U32.t{U32.v x < U32.v metadata_max}) in
  //TODO: hideous coercion that leads to 2 change_slprop_rel
  change_equal_slprop
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal x))))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x') page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x') 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (G.reveal x'))));

  // change_slprop_rel
  //   (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x) page_size))) `star`
  //   A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x) 4ul))) `star`
  //   A.varray (A.split_r md_region (u32_to_sz (G.reveal x))))
  //   (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (G.reveal x') page_size))) `star`
  //   A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (G.reveal x') 4ul))) `star`
  //   A.varray (A.split_r md_region (u32_to_sz (G.reveal x'))))
  //   (fun x y -> x == y)
  //   (fun _ -> admit ());
  let r = alloc_metadata size_class slab_region md_bm_region md_region md_count x' in
  //TODO: hideous coercion that leads to 2 change_slprop_rel
  change_equal_slprop
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x') 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x') 1ul))))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) page_size))) `star`
    A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) 4ul))) `star`
    A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x) 1ul))));
  intro_vrefinedep
    (vptr md_count)
    (fun x -> U32.v x <= U32.v metadata_max == true)
    (fun v ->
      A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz v)))
    (A.varray (A.split_r slab_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) page_size))) `star`
      A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul (U32.add (G.reveal x) 1ul) 4ul))) `star`
      A.varray (A.split_r md_region (u32_to_sz (U32.add (G.reveal x) 1ul))));
  return (fst r)
#pop-options

//assume val alloc_metadata3
//  (size_class: sc)
//  (slab_region: array U8.t{A.length slab_region = U32.v metadata_max * U32.v page_size})
//  (md_bm_region: array U64.t{A.length md_bm_region = U32.v metadata_max * 4})
//  (md_region: array (SL.cell blob){A.length md_region = U32.v metadata_max})
//  (md_count: ref U32.t)
//  : Steel (SL.t blob)
//  //: Steel unit
//  (
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x < U32.v metadata_max == true)
//      (fun v ->
//        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
//        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
//        A.varray (A.split_r md_region (u32_to_sz v)))
//  )
//  (fun r ->
//    SL.llist (p_empty size_class) r `star`
//    vrefinedep
//      (vptr md_count)
//      (fun x -> U32.v x <= U32.v metadata_max == true)
//      (fun v ->
//        A.varray (A.split_r slab_region (u32_to_sz (U32.mul v page_size))) `star`
//        A.varray (A.split_r md_bm_region (u32_to_sz (U32.mul v 4ul))) `star`
//        A.varray (A.split_r md_region (u32_to_sz v)))
//  )
//  (requires fun h0 -> True)
//  (ensures fun h0 r h1 ->
//    //TODO FIXME: fails with this postcondition
//    //L.length (SL.v_llist (p_empty size_class) r h1) = 1
//    ///\ sel md_count h1 = U32.add (sel md_count h0) 1ul
//  )
