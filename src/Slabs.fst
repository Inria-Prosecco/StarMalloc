module Slabs

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module A = Steel.Array
module SM = Steel.Memory

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32
module U8 = FStar.UInt8

module G = FStar.Ghost
module FU = FStar.UInt
module L = FStar.List.Tot

module SL = Selectors.LList
module Temp = TempLock


open FStar.Mul
open Utils
open Utils2
open SlabsUtils
open SizeClass

let slab_region_len : U32.t = normalize_term (U32.mul page_size slab_max_number)
unfold let slab_region
  = r:array U8.t{A.length r = U32.v slab_region_len}

let slab_md_region_len : U32.t = normalize_term (U32.mul 40ul slab_max_number)
unfold let slab_md_region
  = r:array U8.t{A.length r = U32.v slab_md_region_len}

// C binding, no top-level Steel initialization
assume val get_slab_region (_:unit)
  : slab_region

// C binding, no top-level Steel initialization
assume val get_slab_md_region (_:unit)
  : slab_md_region

//TODO
noextract
let slab_md_bitmap_length = nb_slots (U32.uint_to_t min_sc)

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let get_free_slot_aux
  (size_class: sc)
  (bitmap: slab_metadata)
  (i: U32.t)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    U32.v i < U32.v (nb_slots size_class) / 64 /\
    U64.v (Seq.index (A.asel bitmap h0) (U32.v i)) <> 0)
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false)
  )
  =
  let h0 = get () in
  let x = A.index bitmap i in
  let r = ffs64 x in
  let bm = G.hide (Bitmap4.array_to_bv2 (A.asel bitmap h0)) in
  let idx1 = G.hide ((U32.v i) * 64) in
  let idx2 = G.hide ((U32.v i + 1) * 64) in
  assert (x == Seq.index (A.asel bitmap h0) (U32.v i));
  assert (FU.nth (U64.v x) (U64.n - 1 - U32.v r) = false);
  array_to_bv_slice (A.asel bitmap h0) (U32.v i);
  assert (FU.to_vec (U64.v x) == Seq.slice bm ((U32.v i)*64) ((U32.v i + 1)*64));
  Seq.lemma_index_slice bm ((U32.v i)*64) ((U32.v i + 1)*64) (U32.v r);
  let r' = U32.mul 64ul i in
  U32.add r r'
#pop-options

let get_free_slot (size_class: sc) (bitmap: slab_metadata)
  : Steel U32.t
  (A.varray bitmap)
  (fun _ -> A.varray bitmap)
  (requires fun h0 ->
    let s = A.asel bitmap h0 in
    has_free_slot size_class s
  )
  (ensures fun h0 r h1 ->
    A.asel bitmap h1 == A.asel bitmap h0 /\
    U32.v r < U32.v (nb_slots size_class) /\
    (let bm = Bitmap4.array_to_bv2 (A.asel bitmap h0) in
    let idx = Bitmap5.f #4 (U32.v r) in
    Seq.index bm idx = false)
  )
  =
  admit ();
  let bound = U32.div (nb_slots size_class) (U32.uint_to_t U64.n) in
  assert (U32.v bound == U32.v (nb_slots size_class) / 64);
  let x1 = A.index bitmap 0ul in
  if (U64.eq x1 0UL && U32.gt bound 1ul) then (
    let x2 = A.index bitmap 1ul in
    if (U64.eq x2 0UL && U32.gt bound 2ul) then (
      let x3 = A.index bitmap 2ul in
      if (U64.eq x3 0UL && U32.gt bound 3ul) then (
        get_free_slot_aux size_class bitmap 3ul
      ) else (
        get_free_slot_aux size_class bitmap 2ul
      )
    ) else (
      get_free_slot_aux size_class bitmap 1ul
    )
  ) else (
    get_free_slot_aux size_class bitmap 0ul
  )

let allocate_slot_aux (#opened:_)
  (size_class: sc)
  (md: slab_metadata) (arr: array U8.t{A.length arr = U32.v page_size})
  (pos: U32.t{U32.v pos < U32.v (nb_slots size_class)})
  : SteelGhostT unit opened
  (slab_vprop size_class arr 0 (U32.v (nb_slots size_class)) `star` A.varray md)
  (fun _ ->
    (slab_vprop size_class arr 0 (U32.v pos)) `star`
    A.varray (slot_array size_class arr pos) `star`
    (slab_vprop size_class arr (U32.v pos + 1) (U32.v (nb_slots size_class)) `star`
    A.varray md))
  =
  rewrite_slprop
    (slab_vprop size_class arr 0 (U32.v (nb_slots size_class)))
    ((slab_vprop size_class arr 0 (U32.v pos)) `star`
      (slab_vprop size_class arr (U32.v pos) (U32.v (nb_slots size_class))))
    (slab_vprop_sl_lemma size_class md arr
      0 (U32.v (nb_slots size_class)) (U32.v pos));
  rewrite_slprop
    (slab_vprop size_class arr (U32.v pos) (U32.v (nb_slots size_class)))
    ((slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)) `star`
    (slab_vprop size_class arr (U32.v pos + 1) (U32.v (nb_slots size_class))))
    (slab_vprop_sl_lemma size_class md arr
      (U32.v pos) (U32.v (nb_slots size_class)) (U32.v pos + 1));
  slab_vprop_singleton_lemma size_class arr pos;
  assert (
    slab_vprop size_class arr (U32.v pos) (U32.v pos + 1)
    ==
    A.varray (slot_array size_class arr pos) `star` emp
    );
  change_slprop_rel
    (slab_vprop size_class arr (U32.v pos) (U32.v pos + 1))
    (A.varray (slot_array size_class arr pos) `star` emp)
    (fun x y -> x == y)
    (fun _ -> ());
  ()

#set-options "--ide_id_info_off"

// Given a size class and a slab of this size class, return a free slot and update metadata
let allocate_slot (size_class: sc)
  (md: slab_metadata) (arr: array U8.t{A.length arr = U32.v page_size})
  : Steel
    (r:(G.erased nat & array U8.t){
      G.reveal (fst r) < U32.v (nb_slots size_class) /\
      same_base_array (snd r) arr})
  (slab_vprop size_class arr 0 (U32.v (nb_slots size_class)) `star` A.varray md)
  (fun r ->
    (slab_vprop size_class arr 0 (fst r)) `star`
    A.varray (snd r) `star`
    (slab_vprop size_class arr (fst r + 1) (U32.v (nb_slots size_class)) `star`
    A.varray md)
  )
  (requires fun h0 -> has_free_slot size_class (A.asel md h0))
  (ensures fun _ _ _ -> True)
  =
  let slot_pos = get_free_slot size_class md in
  Bitmap5.bm_set #(G.hide 4) md slot_pos;
  let slot = slot_array size_class arr slot_pos in
  array_slot_slot_array_bij size_class arr slot_pos;
  allocate_slot_aux size_class md arr slot_pos;
  change_slprop_rel
    (A.varray (slot_array size_class arr slot_pos))
    (A.varray slot)
    (fun x y -> x == y)
    (fun _ -> ());
  return (G.hide (U32.v slot_pos), slot)

let allocate_slot_kiss (size_class: sc)
  (md: slab_metadata) (arr: array U8.t{A.length arr = U32.v page_size})
  : Steel
    (r:(G.erased nat & array U8.t){
      G.reveal (fst r) < U32.v (nb_slots size_class) /\
      same_base_array (snd r) arr})
  (slab_vprop size_class arr 0 (U32.v (nb_slots size_class)) `star` A.varray md)
  (fun r -> slab_vprop size_class arr 0 (U32.v (nb_slots size_class)) `star` A.varray md)
  (requires fun h0 -> has_free_slot size_class (A.asel md h0))
  (ensures fun h0 r h1 ->
    let bm0 = Bitmap4.array_to_bv2 (A.asel md h0) in
    let bm1 = Bitmap4.array_to_bv2 (A.asel md h1) in
    let idx = Bitmap5.f #4 (G.reveal (fst r)) in
    Seq.index bm0 idx = false /\
    bm1 == Seq.upd bm0 idx true
    )
  =
  let slot_pos = get_free_slot size_class md in
  Bitmap5.bm_set #(G.hide 4) md slot_pos;
  let slot = slot_array size_class arr slot_pos in
  array_slot_slot_array_bij size_class arr slot_pos;
  //allocate_slot_aux size_class md arr slot_pos;
  //change_slprop_rel
  //  (A.varray (slot_array size_class arr slot_pos))
  //  (A.varray slot)
  //  (fun x y -> x == y)
  //  (fun _ -> ());
  return (G.hide (U32.v slot_pos), slot)

// Given a size class, return a free slot and update metadata
// TODO: refine spec
// TODO: remove assume with pure predicates inside p
//   this will yield two different versions of p

inline_for_extraction noextract
let allocate_slab_aux_1
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t slab_metadata))
  (partial_slabs empty_slabs: SL.t slab_metadata)
  : Steel (array U8.t)
  (vptr partial_slabs_ptr `star`
  SL.llist (p sc) partial_slabs `star`
  vptr empty_slabs_ptr `star`
  SL.llist (p sc) empty_slabs)
  (fun r -> SL.ind_llist (p sc) partial_slabs_ptr `star`
  SL.ind_llist (p sc) empty_slabs_ptr)
  (requires fun h0 ->
    sel partial_slabs_ptr h0 == partial_slabs /\
    sel empty_slabs_ptr h0 == empty_slabs /\
    not (SL.is_null_t empty_slabs))
  (ensures fun _ _ _ -> True)
  =
  let n_empty = SL.unpack_list (p sc) empty_slabs in
  let h = get () in
  let md = SL.get_data n_empty in
  assume (has_free_slot sc (A.asel md h));
  let r = allocate_slot_kiss sc
    (SL.get_data n_empty)
    (f (SL.get_data n_empty)) in
  let n_partial = SL.mk_cell partial_slabs (SL.get_data n_empty) in
  write empty_slabs n_partial;
  slassert (
    SL.llist (p sc) (SL.get_next n_empty) `star`
    vptr empty_slabs `star`
    (p sc) (SL.get_data n_empty)
  );
  SL.pack_list (p sc)
    empty_slabs
    partial_slabs
    (SL.get_data n_empty);
  SL.pack_ind (p sc) empty_slabs_ptr empty_slabs;
  write partial_slabs_ptr (SL.get_next n_empty);
  SL.pack_ind (p sc) partial_slabs_ptr (SL.get_next n_empty);
  return (snd r)

inline_for_extraction noextract
let allocate_slab_aux_2
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t slab_metadata))
  (partial_slabs empty_slabs: SL.t slab_metadata)
  : Steel (array U8.t)
  (vptr partial_slabs_ptr `star`
  SL.llist (p sc) partial_slabs `star`
  vptr empty_slabs_ptr `star`
  SL.llist (p sc) empty_slabs)
  (fun r -> SL.ind_llist (p sc) partial_slabs_ptr `star`
  SL.ind_llist (p sc) empty_slabs_ptr)
  (requires fun h0 ->
    sel partial_slabs_ptr h0 == partial_slabs /\
    sel empty_slabs_ptr h0 == empty_slabs /\
    not (SL.is_null_t partial_slabs))
  (ensures fun _ _ _ -> True)
  =
  assert (not (SL.is_null_t partial_slabs));
  let n_partial = SL.unpack_list (p sc) partial_slabs in
  let h = get () in
  let md = SL.get_data n_partial in
  assume (has_free_slot sc (A.asel md h));
  let r = allocate_slot_kiss sc
    (SL.get_data n_partial)
    (f (SL.get_data n_partial)) in
  SL.pack_list (p sc)
    partial_slabs
    (SL.get_next n_partial)
    (SL.get_data n_partial);
  //return (snd r, (partial_slabs, empty_slabs))
  SL.pack_ind (p sc) partial_slabs_ptr partial_slabs;
  SL.pack_ind (p sc) empty_slabs_ptr empty_slabs;
  return (snd r)

let allocate_slab
  (sc: sc)
  (partial_slabs_ptr empty_slabs_ptr: ref (SL.t slab_metadata))
  (partial_slabs empty_slabs: SL.t slab_metadata)
  : Steel (array U8.t)
  (vptr partial_slabs_ptr `star`
  SL.llist (p sc) partial_slabs `star`
  vptr empty_slabs_ptr `star`
  SL.llist (p sc) empty_slabs)
  (fun r -> SL.ind_llist (p sc) partial_slabs_ptr `star`
  SL.ind_llist (p sc) empty_slabs_ptr)
  (requires fun h0 ->
    sel partial_slabs_ptr h0 == partial_slabs /\
    sel empty_slabs_ptr h0 == empty_slabs /\
    (not (SL.is_null_t partial_slabs) \/
    not (SL.is_null_t empty_slabs)))
  (ensures fun _ _ _ -> True)
  =
  if (SL.is_null_t partial_slabs) then (
    let r = allocate_slab_aux_1 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  ) else (
    let r = allocate_slab_aux_2 sc
      partial_slabs_ptr empty_slabs_ptr
      partial_slabs empty_slabs in
    return r
  )

// Given a size, return a size_class
// TODO: improve max_sc bound
// (requires an improved Steel while loop)
let select_size_class (size: U32.t)
  : Steel sc
  emp (fun _ -> emp)
  (requires fun _ -> U32.v size <= max_sc)
  (ensures fun _ size_class _ -> U32.lte size size_class)
  =
  if U32.lte size 16ul then (
    return 16ul
  ) else if U32.lte size 32ul then (
    return 32ul
  ) else (
    return 64ul
  )

let select_size_class2 (size: U32.t)
  (sc16 sc32 sc64: ref size_class_struct)
  : Steel (ref size_class_struct & G.erased U32.t)
  (size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (fun _ -> size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (requires fun h0 ->
    (v_sc_full sc16 h0).scs_v.size == 16ul /\
    (v_sc_full sc32 h0).scs_v.size == 32ul /\
    (v_sc_full sc64 h0).scs_v.size == 64ul /\
    U32.v size <= max_sc)
  (ensures fun h0 r h1 ->
    U32.lte size (snd r))
  =

  if U32.lte size 16ul then (
    let sc_size = G.hide 16ul in
    return (sc16, sc_size)
  ) else if U32.lte size 32ul then (
    let sc_size = G.hide 32ul in
    return (sc32, sc_size)
  ) else (
    let sc_size = G.hide 64ul in
    return (sc64, sc_size)
  )

let size_classes : list sc = [16ul ; 32ul ; 64ul]

let scl_to_vprop (scl: list (ref size_class_struct))
  : vprop
  = starl (L.map (fun sc -> size_class_full sc) scl)

let f ()
  =
  assert (L.memP 16ul size_classes);
  assert_norm (L.memP 32ul size_classes);
  assert_norm (L.memP 64ul size_classes)

let rec partition_equiv_filter (#a: Type) (f: a -> Tot bool) (l: list a)
  : Lemma
  (L.partition f l == (L.filter f l, L.filter (fun x -> not (f x)) l))
  = match l with
  | [] -> ()
  | hd::tl -> partition_equiv_filter f tl

let rec count_equiv_filter (#a: eqtype) (l: list a) (x: a)
  : Lemma
  (ensures L.count x l = L.length (L.filter (fun y -> y = x) l))
  (decreases l)
  = match l with
  | [] -> ()
  | hd::tl -> count_equiv_filter tl x

let rec filter_equiv (#a: Type) (l: list a) (f1 f2: a -> Tot bool)
  : Lemma
  (requires forall x. f1 x = f2 x)
  (ensures L.filter f1 l == L.filter f2 l)
  (decreases l)
  = match l with
  | [] -> ()
  | hd::tl -> filter_equiv tl f1 f2

let filter_lemma (#a: eqtype) (l: list a) (x: a)
  : Lemma
  (requires L.count x l == 1)
  (ensures ([x], L.filter (fun y -> y <> x) l) == L.partition (fun y -> y = x) l)
  =
  let f = fun y -> y = x in
  let r = L.partition f l in
  partition_equiv_filter f l;
  L.partition_count f l x;
  assert (L.count x l == L.count x (fst r) + L.count x (snd r));
  assert (1 == L.count x (fst r) + L.count x (snd r));
  assert (L.count x (fst r) = 1 || L.count x (snd r) = 1);
  if (L.count x (snd r) = 1) then (
    L.mem_count (snd r) x;
    L.mem_memP x (snd r);
    assert (L.memP x (snd r));
    L.mem_filter (fun x -> not (f x)) (snd r) x;
    assert (not (f x));
    assert (f x)
  );
  assert (L.count x (fst r) = 1);
  count_equiv_filter l x;
  assert (L.length (fst r) = 1);
  L.mem_count (fst r) x;
  assert (L.mem x (fst r));
  assert (fst r = [x]);
  filter_equiv l (fun y -> not (y = x)) (fun y -> y <> x)

let starl_singleton (#a: Type) (f: a -> Tot vprop) (l: list a)
  : Lemma
  (requires L.length l == 1)
  (ensures starl (L.map f l) `equiv` f (L.hd l))
  =
  assert (l == [L.hd l]);
  assert (L.map f l == [f (L.hd l)]);
  let p1 = starl (L.map f l) in
  let p3 = f (L.hd l) in
  let p2 = p3 `star` emp in
  assert (starl [f (L.hd l)] == f (L.hd l) `star` emp);
  equiv_refl p1;
  assert (p1 `equiv` p2);
  cm_identity p3;
  assert ((emp `star` p3) `equiv` p3);
  star_commutative emp p3;
  assert ((emp `star` p3) `equiv` p2);
  equiv_sym (emp `star` p3) p2;
  equiv_trans
    p2
    (emp `star` p3)
    p3;
  assert (p2 `equiv` p3);
  equiv_trans p1 p2 p3

let starl_append_hd_map (#a: Type) (f: a -> vprop) (l: list a) (x: a)
  : Lemma
  (starl (L.map f (x::l)) `equiv` (f x `star` starl (L.map f l)))
  =
  let p0 = starl (L.map f (x::l)) in
  let p1 = starl (L.map f l) in
  L.map_append f [x] l;
  assert (L.map f (x::l) == L.append (L.map f [x]) (L.map f l));
  starl_append (L.map f [x]) (L.map f l);
  assert (p0 `equiv` (starl (L.map f [x]) `star` p1));
  starl_singleton f [x];
  assert (starl (L.map f [x]) `equiv` f x);
  equiv_refl p1;
  star_congruence
    (starl (L.map f [x])) p1
    (f x) p1;
  equiv_trans
    p0
    (starl (L.map f [x]) `star` p1)
    (f x `star` p1)

let rec starl_filter (#a: Type) (g: a -> bool) (f: a -> vprop) (l: list a)
  : Lemma
  (ensures (let l1, l2 = L.partition g l in
  starl (L.map f l) `equiv` (starl (L.map f l1) `star` starl (L.map f l2))))
  (decreases l)
  =
  // arbitrary permutation do not change validity of vprop
  // no need for permutation, induction should be ok
  match l with
  | [] ->
      let l1, l2 = L.partition g l in
      assert (L.map f l == []);
      L.partition_length g l;
      assert (L.map f l1 == []);
      assert (L.map f l2 == []);
      cm_identity emp;
      equiv_sym (emp `star` emp) emp

  | hd::tl ->
      let l1, l2 = L.partition g tl in
      starl_filter g f tl;
      let p0 = starl (L.map f l) in
      let p1 = starl (L.map f tl) in
      let p2 = starl (L.map f l1) in
      let p3 = starl (L.map f l2) in
      assert (p1 `equiv` (p2 `star` p3));
      starl_append_hd_map f tl hd;
      assert (p0 `equiv` (f hd `star` p1));
      equiv_refl (f hd);
      star_congruence
        (f hd) p1
        (f hd) (p2 `star` p3);
      assert ((f hd `star` p1) `equiv` (f hd `star` (p2 `star` p3)));
      if g hd then (
        star_associative (f hd) p2 p3;
        equiv_sym
          ((f hd `star` p2) `star` p3)
          (f hd `star` (p2 `star` p3));
        equiv_trans
          (f hd `star` p1)
          (f hd `star` (p2 `star` p3))
          ((f hd `star` p2) `star` p3);
        assert ((f hd `star` p1) `equiv` ((f hd `star` p2) `star` p3));
        let p2' = starl (L.map f (hd::l1)) in
        assert (hd::l1 == fst (L.partition g l));
        starl_append_hd_map f l1 hd;
        equiv_sym p2' (f hd `star` p2);
        assert ((f hd `star` p2) `equiv` p2');
        equiv_refl p3;
        star_congruence
          (f hd `star` p2) p3
          p2' p3;
        equiv_trans
          p0
          (f hd `star` (p2 `star` p3))
          (p2' `star` p3)
      ) else (
        star_commutative (f hd) (p2 `star` p3);
        equiv_trans
          (f hd `star` p1)
          (f hd `star` (p2 `star` p3))
          ((p2 `star` p3) `star` f hd);
        star_associative p2 p3 (f hd);
        equiv_refl p2;
        star_commutative p3 (f hd);
        star_congruence
          p2 (p3 `star` f hd)
          p2 (f hd `star` p3);
        equiv_trans
          (f hd `star` p1)
          ((p2 `star` p3) `star` f hd)
          (p2 `star` (p3 `star` f hd));
        equiv_trans
          (f hd `star` p1)
          (p2 `star` (p3 `star` f hd))
          (p2 `star` (f hd `star` p3));
        assert ((f hd `star` p1) `equiv` (p2 `star` (f hd `star` p3)));
        let p3' = starl (L.map f (hd::l2)) in
        assert (hd::l2 == snd (L.partition g l));
        starl_append_hd_map f l2 hd;
        equiv_sym p3' (f hd `star` p3);
        assert ((f hd `star` p3) `equiv` p3');
        equiv_refl p2;
        star_congruence
          p2 (f hd `star` p3)
          p2 p3';
        equiv_trans
          p0
          (f hd `star` p1)
          (p2 `star` p3')
      )

let starl_partition_equiv (#a: eqtype)
  (f: a -> Tot vprop)
  (l: list a)
  (x: a)
  : Lemma
  (requires L.count x l == 1)
  (ensures
    starl (L.map f l)
    `equiv`
    (f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l))))
  =
  L.mem_count l x;
  filter_lemma l x;
  starl_filter (fun y -> y = x) f l;
  let p1 = starl (L.map f l) in
  let p21 = starl (L.map f [x]) in
  let p22 = starl (L.map f (L.filter (fun y -> y <> x) l)) in
  let p31 = f x in
  let p2 = p21 `star` p22 in
  let p3 = p31 `star` p22 in
  assert (p1 `equiv` p2);
  assert_norm (L.length [x] == 1);
  starl_singleton f [x];
  equiv_refl p22;
  star_congruence
    p21 p22
    p31 p22;
  assert (p2 `equiv` p3);
  equiv_trans p1 p2 p3;
  assert (p1 `equiv` p3)

let starl_partition_unpack (#a: eqtype)
  (f: a -> Tot vprop)
  (l: list a)
  (x: a)
  (m: SM.mem)
  : Lemma
  (requires L.count x l == 1 /\
  SM.interp (hp_of (
    starl (L.map f l)
  )) m)
  (ensures SM.interp (hp_of (
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l))
  )) m)
  =
  let p1 = starl (L.map f l) in
  let p2 =
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l)) in
  starl_partition_equiv f l x;
  reveal_equiv p1 p2;
  SM.reveal_equiv (hp_of p1) (hp_of p2)

let starl_partition_pack (#a: eqtype)
  (f: a -> Tot vprop)
  (l: list a)
  (x: a)
  (m: SM.mem)
  : Lemma
  (requires L.count x l == 1 /\
  SM.interp (hp_of (
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l))
  )) m)
  (ensures SM.interp (hp_of (
    starl (L.map f l)
  )) m)
  =
  let p1 = starl (L.map f l) in
  let p2 =
    f x `star`
    starl (L.map f (L.filter (fun y -> y <> x) l)) in
  starl_partition_equiv f l x;
  equiv_sym p1 p2;
  reveal_equiv p2 p1;
  SM.reveal_equiv (hp_of p2) (hp_of p1)


(*)
let rec select_size_class3
  (scl: list (ref size_class_struct))
  (size: U32.t)
  : Steel (ref size_class_struct)
  (scl_to_vprop scl)
  (fun r ->
    size_class_full r `star`
    scl_to_vprop (L.filter (fun r2 -> r2 =!= r) scl)
  )
  (requires fun h0 -> Cons? scl)
  (ensures fun h0 r h1 ->
    not (is_null r)
  )
  =
  let r = L.hd scl in




  admit ();
  return null

let a = 42
(*)

  (fun r ->
    size_class_full r `star`
    SL.ind_llist (fun sc -> size_class_full sc) size_classes)
  (requires fun h0 ->
    Cons? (SL.v_ind_llist (fun sc -> size_class_full sc) size_classes h0))
  (ensures fun h0 r h1 ->

  )



  (size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (fun _ -> size_class_full sc16 `star` size_class_full sc32 `star` size_class_full sc64)
  (requires fun h0 ->
    (v_sc_full sc16 h0).scs_v.size == 16ul /\
    (v_sc_full sc32 h0).scs_v.size == 32ul /\
    (v_sc_full sc64 h0).scs_v.size == 64ul /\
    U32.v size <= max_sc)
  (ensures fun h0 r h1 ->
    U32.lte size (snd r))
  =

  if U32.lte size 16ul then (
    let sc_size = G.hide 16ul in
    return (sc16, sc_size)
  ) else if U32.lte size 32ul then (
    let sc_size = G.hide 32ul in
    return (sc32, sc_size)
  ) else (
    let sc_size = G.hide 64ul in
    return (sc64, sc_size)
  )



(*)
//noextract
//let size_classes : list nzn = [
//  //(* 0 *) 0;
//  (* 16 *) 16; 32; 48; 64; 80; 96; 112; 128;
//  (* 32 *) 160; 192; 224; 256;
//  (* 64 *) 320; 384; 448; 512;
//]
//
//
//noextract
//let size_class_slots : list nzn =
//  L.map nb_of_slots size_classes
//
//let f (_:unit) =
//  let v = L.nth size_class_slots 0 in
//  assert(Some?.v v == 256);
//  ()

let page_size = 4096ul

let nzn = x:U32.t{U32.v x > 0 /\ U32.v x <= U32.v page_size}
let slab = slab:array U8.t{A.length slab == U32.v page_size}

let nb_slots (x: nzn) : nzn = U32.div page_size x

let slab_metadata (size_class: nzn)
  = Seq.lseq bool (U32.v (nb_slots size_class))
