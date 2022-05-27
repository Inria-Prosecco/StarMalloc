module Map

open Steel.Effect.Atomic
open Steel.Effect

module U64 = FStar.UInt64
module I64 = FStar.Int64

open Impl

#set-options "--ide_id_info_off"

// requires:
// 1) a compare operator on values of type a
// [removed] 2) an inhabitant of type b
// TODO: requirement 2) should be removed but extraction issues
// TODO: reorganize spec/impl and add precise specs to mem+find

//unfold let map (#a #b: Type) = Impl.t (a & b)
//noextract
unfold let convert (#a #b: Type) (compare: cmp a) : cmp (a & b)
  = fun (x y: a & b) -> compare (fst x) (fst y)

let spec_convert (#a #b: Type) (compare: cmp (a & b))
  : GTot (Spec.cmp (a & b))
  //= Impl.Common.convert (convert compare)
  = Impl.Common.convert compare

let insert (#a #b: Type)
  (r: bool) (cmp: cmp (a & b)) (ptr: t (a & b))
  (new_data: a & b)
  : Steel (t (a & b))
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.size_of_tree (v_linked_tree ptr h0) < c /\
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0) /\
    v_linked_tree ptr' h1
    == Spec.insert_avl r
      (spec_convert cmp)
      (v_linked_tree ptr h0) new_data)
  =
  let h0 = get () in
  Spec.height_lte_size (v_linked_tree ptr h0);
  Impl.insert_avl r cmp ptr new_data

let delete (#a #b: Type)
  (cmp: cmp (a & b)) (ptr: t (a & b))
  (data_to_rm: a & b)
  : Steel (t (a & b))
  (linked_tree ptr)
  (fun ptr' -> linked_tree ptr')
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 ptr' h1 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0) /\
    v_linked_tree ptr' h1
    == Spec.delete_avl (spec_convert cmp)
      (v_linked_tree ptr h0)
      data_to_rm)
  =
  Impl.delete_avl cmp ptr data_to_rm

let cardinal (#a #b: Type) (ptr: t (a & b))
  : Steel (U64.t)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun _ -> True)
  (ensures fun h0 s h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
    U64.v s == Spec.sot_wds (v_linked_tree ptr h0) /\
    U64.v s == Spec.size_of_tree (v_linked_tree ptr h0))
  =
  Impl.sot_wds ptr

let rec mem (#a #b: Type) (cmp: cmp (a & b)) (ptr: t (a & b))
  (v: a)
  (b_inhab: b)
  : Steel bool
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_bst (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 b h1 ->
    v_linked_tree ptr h0 == v_linked_tree ptr h1)
  =
  if is_null_t ptr then (
    return false
  ) else (
    let node = unpack_tree ptr in
    let delta = cmp (v, b_inhab) (get_data node) in
  if I64.eq delta szero then (
    pack_tree ptr
      (get_left node) (get_right node)
      (get_size node) (get_height node);
    let r = snd (get_data node) in
    return true
  ) else (
    if I64.lt delta szero then (
      let r = mem cmp (get_left node) v b_inhab in
      pack_tree ptr
        (get_left node) (get_right node)
        (get_size node) (get_height node);
      return r
    ) else (
      let r = mem cmp (get_right node) v b_inhab in
      pack_tree ptr
        (get_left node) (get_right node)
        (get_size node) (get_height node);
      return r
    )
  ))

let rec find (#a #b: Type) (cmp: cmp (a & b)) (ptr: t (a & b))
  (v: a)
  (b_inhab: b)
  : Steel (option b)
  (linked_tree ptr)
  (fun _ -> linked_tree ptr)
  (requires fun h0 ->
    Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
  (ensures fun h0 r h1 ->
    v_linked_tree ptr h1 == v_linked_tree ptr h0)
    //Spec.is_avl (spec_convert cmp) (v_linked_tree ptr h0))
    //r == Spec.Map.find_avl #a #b (spec_convert cmp) (v_linked_tree ptr h0) v)
  =
  if is_null_t ptr then (
    null_is_leaf ptr;
    return None
  ) else (
    let node = unpack_tree ptr in
    let delta = cmp (v, b_inhab) (get_data node) in
  if I64.eq delta szero then (
    pack_tree ptr
      (get_left node) (get_right node)
      (get_size node) (get_height node);
    let r = snd (get_data node) in
    return (Some r)
  ) else (
    if I64.lt delta szero then (
      let r = find cmp (get_left node) v b_inhab in
      pack_tree ptr
        (get_left node) (get_right node)
        (get_size node) (get_height node);
      return r
    ) else (
      let r = find cmp (get_right node) v b_inhab in
      pack_tree ptr
        (get_left node) (get_right node)
        (get_size node) (get_height node);
      return r
    )
  ))

//let mem (#a #b: Type) (cmp: cmp a) (ptr: t (a & b))
//  (v: a)
//  (b_inhabitant: b)
//  : Steel bool
//  (linked_tree ptr)
//  (fun _ -> linked_tree ptr)
//  (requires fun h0 ->
//    Spec.is_bst (spec_convert cmp) (v_linked_tree ptr h0))
//  (ensures fun h0 b h1 ->
//    v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
//    Spec.is_bst (spec_convert cmp) (v_linked_tree ptr h0) /\
//    (Spec.mem (spec_convert cmp) (v_linked_tree ptr h0) (v, b_inhabitant) <==> b) /\
//    (Spec.memopt (spec_convert cmp) (v_linked_tree ptr h0) (v, b_inhabitant) <==> b))
//  =
//  Impl.member (convert cmp) ptr (v, b_inhabitant)
