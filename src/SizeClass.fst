module SizeClass

module G = FStar.Ghost
module SM = Steel.Memory

//open SlabsAlloc

#reset-options "--fuel 1 --ifuel 1"
#push-options "--ide_id_info_off"

open Prelude

let slab_region_size_eq_lemma (_:unit)
  : Lemma
  (slab_region_size = US.mul metadata_max_ex slab_size)
  =
  ()

//inline_for_extraction noextract
//let slab_size : (v:US.t{US.v v == US.v metadata_max * U32.v page_size /\ US.v v > 0})
//  = US.mul metadata_max (US.of_u32 page_size)

//let size_class_vprop_sc
//  (scs: size_class_struct_sc)
//  : vprop
//  =
//  vrefinedep
//    (R.vptr scs.md_count)
//    SlabsCommon.vrefinedep_prop
//    (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
//      scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
//
//let size_class_vprop_sc_ex
//  (scs: size_class_struct_sc_ex)
//  : vprop
//  =
//  vrefinedep
//    (vptr scs.md_count)
//    SlabsCommon2.vrefinedep_prop
//    (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
//      scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)

let size_class_vprop
  (scs: size_class_struct)
  : vprop
  =
  if scs.is_extended
  then size_class_vprop_sc_ex scs
  else size_class_vprop_sc scs

let size_class_vprop_reveal _ = ()

//TODO: rename as unpack lemma
let allocate_size_class_sl_lemma1_ex
  (scs: size_class_struct_sc_ex)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (size_class_vprop_sc_ex scs)) m
  )
  (ensures
    SM.interp (hp_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon2.vrefinedep_prop
        (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
          scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    )) m /\
    sel_of (size_class_vprop_sc_ex scs) m
    ==
    sel_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon2.vrefinedep_prop
        (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
          scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

//TODO: rename as unpack lemma
let allocate_size_class_sl_lemma1
  (scs: size_class_struct_sc)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (size_class_vprop_sc scs)) m
  )
  (ensures
    SM.interp (hp_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon.vrefinedep_prop
        (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
          scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    )) m /\
    sel_of (size_class_vprop_sc scs) m
    ==
    sel_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon.vrefinedep_prop
        (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
          scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

//TODO: rename as pack lemma
let allocate_size_class_sl_lemma2_ex
  (scs: size_class_struct_sc_ex)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon2.vrefinedep_prop
        (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
          scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    )) m
  )
  (ensures
    SM.interp (hp_of (size_class_vprop_sc_ex scs)) m /\
    sel_of (size_class_vprop_sc_ex scs) m
    ==
    sel_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon2.vrefinedep_prop
        (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
          scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

//TODO: rename as pack lemma
let allocate_size_class_sl_lemma2
  (scs: size_class_struct_sc)
  (m: SM.mem)
  : Lemma
  (requires
    SM.interp (hp_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon.vrefinedep_prop
        (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
          scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    )) m
  )
  (ensures
    SM.interp (hp_of (size_class_vprop_sc scs)) m /\
    sel_of (size_class_vprop_sc scs) m
    ==
    sel_of (
      vrefinedep
        (R.vptr scs.md_count)
        SlabsCommon.vrefinedep_prop
        (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
          scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs)
    ) m
  )
  = ()

open MiscArith
#push-options "--fuel 0 --ifuel 0"
let mod_arith_lemma_applied
  (n: nat) (page_size sc align: pos)
  : Lemma
  (requires
    sc % align == 0 /\
    page_size % align == 0 /\
    (n % page_size) % sc == 0 /\
    align <= sc /\
    sc <= page_size
  )
  (ensures n % align == 0)
  =
  Math.Lemmas.euclidean_division_definition n page_size;
  assert (n % page_size == n - (n/page_size)*page_size);
  let n' = n % page_size in
  Math.Lemmas.euclidean_division_definition n' sc;
  assert (n' % sc == n' - (n'/sc)*sc);
  assert (n' % sc == 0);
  assert (n' == n'/sc*sc);
  assert (n - (n/page_size)*page_size == n'/sc*sc);
  assert (n = (n/page_size)*page_size + n'/sc*sc);
  lemma_mod_mul2 (n'/sc) sc align;
  lemma_mod_plus2 ((n/page_size)*page_size) (n'/sc*sc) align;
  assert (n % align = (n/page_size)*page_size % align);
  lemma_mod_mul2 (n/page_size) page_size align;
  lemma_mod_plus2 0 ((n/page_size)*page_size) align
#pop-options

#push-options "--fuel 0 --ifuel 0"
let mod_arith_lemma_applied2
  (n: nat) (page_size sc align: pos)
  : Lemma
  (requires
    sc % align == 0 /\
    page_size % align == 0 /\
    (n % page_size) % sc == 0 /\
    align <= sc /\
    sc <= page_size
  )
  (ensures n % align == 0)
  =
  Math.Lemmas.euclidean_division_definition n page_size;
  assert (n % page_size == n - (n/page_size)*page_size);
  let n' = n % page_size in
  Math.Lemmas.euclidean_division_definition n' sc;
  assert (n' % sc == n' - (n'/sc)*sc);
  assert (n' % sc == 0);
  assert (n' == n'/sc*sc);
  assert (n - (n/page_size)*page_size == n'/sc*sc);
  assert (n = (n/page_size)*page_size + n'/sc*sc);
  lemma_mod_mul2 (n'/sc) sc align;
  lemma_mod_plus2 ((n/page_size)*page_size) (n'/sc*sc) align;
  assert (n % align = (n/page_size)*page_size % align);
  lemma_mod_mul2 (n/page_size) page_size align;
  lemma_mod_plus2 0 ((n/page_size)*page_size) align
#pop-options

//let allocate_size_class_aux
//  (scs: size_class_struct)
//  (r: array U8.t)
//  : Lemma
//  (requires
//    (not scs.is_extended) /\
//    not (A.is_null r) ==> (
//      A.length r == U32.v (get_sc scs.size) /\
//      same_base_array r scs.slab_region /\
//      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
//      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v (get_sc scs.size)) == 0
//    )
//  )
//  (ensures
//    (not scs.is_extended) /\
//    not (A.is_null r) ==> (
//      A.length r == U32.v (get_sc scs.size) /\
//      same_base_array r scs.slab_region /\
//      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
//      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v (get_sc scs.size)) == 0 /\
//      array_u8_alignment r 16ul /\
//      ((U32.v page_size) % (U32.v (get_sc scs.size)) == 0 ==> array_u8_alignment r (get_sc scs.size))
//    )
//  )
//  =
//  if not (A.is_null r)
//  then (
//    assert (same_base_array r scs.slab_region);
//    assert (same_base_array scs.slab_region r);
//    assert (array_u8_alignment scs.slab_region page_size);
//    mod_arith_lemma_applied
//      (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
//      (U32.v page_size)
//      (U32.v (get_sc scs.size))
//      16;
//    assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % 16 == 0);
//    array_u8_alignment_lemma scs.slab_region r page_size 16ul;
//    if ((U32.v page_size) % (U32.v scs.size) = 0) then (
//      mod_arith_lemma_applied
//        (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
//        (U32.v page_size)
//        (U32.v scs.size)
//        (U32.v scs.size);
//      assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % (U32.v scs.size) == 0);
//      array_u8_alignment_lemma scs.slab_region r page_size scs.size
//    ) else ()
//  ) else ()

#restart-solver

let allocate_size_class_sc_aux
  (scs: size_class_struct_sc)
  (r: array U8.t)
  : Lemma
  (requires (
    let size = get_sc scs.size in
    not (A.is_null r) ==> (
      A.length r == U32.v size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v size) == 0
    )
  ))
  (ensures (
    let size = get_sc scs.size in
    not (A.is_null r) ==> (
      A.length r == U32.v size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v size) == 0 /\
      array_u8_alignment r 16ul /\
      ((U32.v page_size) % (U32.v size) == 0 ==> array_u8_alignment r size)
    )
  ))
  =
  let size = get_sc scs.size in
  if not (A.is_null r)
  then (
    assert (same_base_array r scs.slab_region);
    assert (same_base_array scs.slab_region r);
    assert (array_u8_alignment scs.slab_region page_size);
    mod_arith_lemma_applied
      (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
      (U32.v page_size)
      (U32.v size)
      16;
    assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % 16 == 0);
    array_u8_alignment_lemma scs.slab_region r page_size 16ul;
    if ((U32.v page_size) % (U32.v size) = 0) then (
      mod_arith_lemma_applied
        (A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region))
        (U32.v page_size)
        (U32.v size)
        (U32.v size);
      assert ((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % (U32.v size) == 0);
      array_u8_alignment_lemma scs.slab_region r page_size size
    ) else ()
  ) else ()

#restart-solver

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --compat_pre_typed_indexed_effects"
let allocate_size_class_sc scs
  =
  change_slprop_rel
    (size_class_vprop_sc scs)
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon.vrefinedep_prop
      (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let result = SlabsAlloc.allocate_slab
    (get_sc scs.size)
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count scs.slabs_idxs in
  change_slprop_rel
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon.vrefinedep_prop
      (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (size_class_vprop_sc scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  allocate_size_class_sc_aux scs result;
  return result
#pop-options

let deallocate_size_class_sc scs ptr diff
 =
  change_slprop_rel
    (size_class_vprop_sc scs)
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon.vrefinedep_prop
      (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1 scs m);
  let b = SlabsFree.deallocate_slab ptr
    (get_sc scs.size)
    scs.slab_region scs.md_bm_region scs.md_region
    scs.md_count scs.slabs_idxs diff in
  change_slprop_rel
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon.vrefinedep_prop
      (SlabsCommon.size_class_vprop_aux (get_sc scs.size)
        scs.slab_region scs.md_bm_region scs.md_region scs.slabs_idxs))
    (size_class_vprop_sc scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2 scs m);
  return b

val allocate_size_class_sc_ex
  (scs: size_class_struct_sc_ex)
  : Steel (array U8.t)
  (size_class_vprop_sc_ex scs)
  (fun r ->
    (if (A.is_null r) then emp else A.varray r) `star`
    size_class_vprop_sc_ex scs)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let sc_size = get_sc_ex scs.size in
    not (A.is_null r) ==> (
      A.length r == U32.v sc_size /\
      same_base_array r scs.slab_region /\
      A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region) >= 0 /\
      //((A.offset (A.ptr_of r) - A.offset (A.ptr_of scs.slab_region)) % U32.v page_size) % (U32.v (get_u32 scs.size)) == 0 /\
      array_u8_alignment r 16ul /\
      True
      //((U32.v page_size) % (U32.v scs.size) == 0 ==> array_u8_alignment r scs.size)
    )
  )

let allocate_size_class_sc_ex scs
  =
  change_slprop_rel
    (size_class_vprop_sc_ex scs)
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon2.vrefinedep_prop
      (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
        scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1_ex scs m);
  let result = SlabsAlloc2.allocate_slab
    (get_sc_ex scs.size)
    scs.slab_region scs.md_bm_region_b scs.md_region
    scs.md_count scs.slabs_idxs in
  change_slprop_rel
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon2.vrefinedep_prop
      (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
        scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs))
    (size_class_vprop_sc_ex scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2_ex scs m);
  //allocate_size_class_sc_aux scs result;
  assume (array_u8_alignment result 16ul);
  return result

val deallocate_size_class_sc_ex
  (scs: size_class_struct_sc_ex)
  (ptr: array U8.t)
  (diff: US.t)
  : Steel bool
  (A.varray ptr `star`
  size_class_vprop_sc_ex scs)
  (fun b ->
    (if b then emp else A.varray ptr) `star`
    size_class_vprop_sc_ex scs)
  (requires fun h0 ->
    let diff' = A.offset (A.ptr_of ptr) - A.offset (A.ptr_of scs.slab_region) in
    0 <= diff' /\
    US.v diff = diff' /\
    (diff' % U32.v page_size) % U32.v (get_u32 scs.size) == 0 /\
    A.length ptr == U32.v (get_u32 scs.size) /\
    same_base_array ptr scs.slab_region)
  (ensures fun h0 _ h1 -> True)

let deallocate_size_class_sc_ex scs ptr diff
 =
  change_slprop_rel
    (size_class_vprop_sc_ex scs)
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon2.vrefinedep_prop
      (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
        scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs))
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma1_ex scs m);
  let b = SlabsFree2.deallocate_slab ptr
    (get_sc_ex scs.size)
    scs.slab_region scs.md_bm_region_b scs.md_region
    scs.md_count scs.slabs_idxs diff in
  change_slprop_rel
    (vrefinedep
      (R.vptr scs.md_count)
      SlabsCommon2.vrefinedep_prop
      (SlabsCommon2.size_class_vprop_aux (get_sc_ex scs.size)
        scs.slab_region scs.md_bm_region_b scs.md_region scs.slabs_idxs))
    (size_class_vprop_sc_ex scs)
    (fun x y -> x == y)
    (fun m -> allocate_size_class_sl_lemma2_ex scs m);
  return b

let allocate_size_class scs
  =
  if scs.is_extended then (
    change_equal_slprop (size_class_vprop scs) (size_class_vprop_sc_ex scs);
    let r = allocate_size_class_sc_ex scs in
    change_equal_slprop (size_class_vprop_sc_ex scs) (size_class_vprop scs);
    return r
  ) else (
    change_equal_slprop (size_class_vprop scs) (size_class_vprop_sc scs);
    let r = allocate_size_class_sc scs in
    change_equal_slprop (size_class_vprop_sc scs) (size_class_vprop scs);
    return r
  )

let deallocate_size_class scs ptr diff
  =
  if scs.is_extended then (
    change_equal_slprop (size_class_vprop scs) (size_class_vprop_sc_ex scs);
    let r = deallocate_size_class_sc_ex scs ptr diff in
    change_equal_slprop (size_class_vprop_sc_ex scs) (size_class_vprop scs);
    return r
  ) else (
    change_equal_slprop (size_class_vprop scs) (size_class_vprop_sc scs);
    let r = deallocate_size_class_sc scs ptr diff in
    change_equal_slprop (size_class_vprop_sc scs) (size_class_vprop scs);
    return r
  )
