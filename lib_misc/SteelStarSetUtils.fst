module SteelStarSetUtils

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module SM = Steel.Memory
module FS = FStar.FiniteSet.Base
module L = FStar.List.Tot
module G = FStar.Ghost
open SteelOptUtils

#push-options "--fuel 0 --ifuel 0"

let starl (l: list vprop)
  : vprop
  =
  SteelStarSeqUtils.starl l

let starl_set (#a: eqtype) (f: a -> vprop) (s: FS.set a)
  : vprop
  =
  starl (L.map f (FS.set_as_list s))

let starl_append (l1 l2: list vprop)
  : Lemma
  (starl (L.append l1 l2) `equiv` (starl l1 `star` starl l2))
  =
  SteelStarSeqUtils.starl_append l1 l2

let starl_set_append (#a: eqtype) (f: a -> vprop) (s1 s2: FS.set a)
  : Lemma
  (starl_set f (FS.union s1 s2)
   `equiv`
   (starl_set f s1 `star` starl_set f s2))
  =
  // more complicated but reasonable
  admit ()

let starl_set_singleton (#a: eqtype) (f: a -> vprop) (s: FS.set a)
  : Lemma
  (requires FS.cardinality s == 1)
  (ensures
    Cons? (FS.set_as_list s) /\
    starl_set f s `equiv` f (L.hd (FS.set_as_list s))
  )
  =
  // need for an equivalent of map_seq_index to map_seq for L.map
  admit ()

let starl_set_unpack (#a: eqtype) (f: a -> vprop) (s: FS.set a) (x: a)
  : Lemma
  (requires FS.mem x s)
  (ensures
    starl_set f s
    `equiv`
    (f x `star` starl_set f (FS.remove x s))
  )
  = admit ()

let starl_set_pack (#a: eqtype) (f: a -> vprop) (s: FS.set a) (x: a)
  : Lemma
  (requires not (FS.mem x s))
  (ensures
    starl_set f (FS.insert x s)
    `equiv`
    (f x `star` starl_set f s)
  )
  = admit ()

let starl_set_imp (#a: eqtype) (f: a -> vprop) (s: FS.set a) (x: a)
  : Lemma
  (requires FS.mem x s)
  (ensures
    starl_set f s
    `can_be_split`
    f x
  )
  = admit ()

let starl_set_sel_aux (#a: eqtype) (#b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (h: hmem (starl_set f s))
  (x: a)
  : Pure (G.erased b)
  (requires FS.mem x s)
  (ensures fun _ -> True)
  =
  starl_set_imp f s x;
  assert (starl_set f s `can_be_split` f x);
  can_be_split_interp
    (starl_set f s)
    (f x) h;
  f_lemma x;
  let s : selector b (hp_of (f x)) = sel_of (f x) in
  G.hide (s h)

#push-options "--fuel 1 --ifuel 1"

val map_pure
  (#a #b: Type)
  (p: a -> bool)
  (f: ((x:a) -> Pure b (requires p x) (ensures fun _ -> True)))
  (l: list a{forall (x: a). L.memP x l ==> p x})
  : Tot (list b)

let rec map_pure p f l = match l with
  | [] -> []
  | h::tl -> f h::map_pure p f tl

val map_pure_len
  (#a #b: Type)
  (p: a -> bool)
  (f: ((x:a) -> Pure b (requires p x) (ensures fun _ -> True)))
  (l: list a{forall (x: a). L.memP x l ==> p x})
  : Lemma
  (L.length (map_pure p f l) == L.length l)

let rec map_pure_len p f l = match l with
  | [] -> ()
  | h::tl -> map_pure_len p f tl

val map_pure_index
  (#a #b: Type)
  (p: a -> bool)
  (f: ((x:a) -> Pure b (requires p x) (ensures fun _ -> True)))
  (l: list a{forall (x: a). L.memP x l ==> p x})
  (n: nat{n < L.length l})
  : Lemma
  (
    map_pure_len p f l;
    L.lemma_index_memP l n;
    L.index (map_pure p f l) n == f (L.index l n)
  )

let rec map_pure_index p f l n =
  map_pure_len p f l;
  if L.length l = 0
  then ()
  else if n = 0
  then ()
  else map_pure_index p f (L.tl l) (n-1)

#pop-options

let starl_set_sel' (#a: eqtype) (#b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  : selector' (list (G.erased b)) (hp_of (starl_set f s))
  =
  fun (h:hmem (starl_set f s)) ->
    let f' = starl_set_sel_aux #a #b f f_lemma s h in
    let l = FS.set_as_list s in
    map_pure (fun x -> L.mem x l) f' l

let starl_set_sel_depends_only_on_aux (#a: eqtype) (#b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (m0: SM.hmem (hp_of (starl_set f s)))
  (m1: SM.mem{SM.disjoint m0 m1})
  (x: a)
  : Lemma
  (requires FS.mem x s)
  (ensures (
    let v1 = starl_set_sel_aux #a #b f f_lemma s m0 x in
    let v2 = starl_set_sel_aux #a #b f f_lemma s (SM.join m0 m1) x in
    v1 == v2
  ))
  =
  let m' = SM.join m0 m1 in
  let s1 = starl_set_sel' #a #b f f_lemma s m0 in
  let s2 = starl_set_sel' #a #b f f_lemma s m' in
  let l = FS.set_as_list s in
  map_pure_len (fun x -> L.mem x l)
    (starl_set_sel_aux #a #b f f_lemma s m0)
    l;
  map_pure_len (fun x -> L.mem x l)
    (starl_set_sel_aux #a #b f f_lemma s m')
    l;
  let v1 = starl_set_sel_aux #a #b f f_lemma s m0 x in
  let v2 = starl_set_sel_aux #a #b f f_lemma s m' x in
  starl_set_imp f s x;
  can_be_split_interp (starl_set f s) (f x) m0;
  can_be_split_interp (starl_set f s) (f x) m'

let starl_set_sel_depends_only_on_core_aux (#a: eqtype) (#b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (m0: SM.hmem (hp_of (starl_set f s)))
  (x: a)
  : Lemma
  (requires FS.mem x s)
  (ensures (
    let v1 = starl_set_sel_aux #a #b f f_lemma s m0 x in
    let v2 = starl_set_sel_aux #a #b f f_lemma s (SM.core_mem m0) x in
    v1 == v2
  ))
  =
  let l = FS.set_as_list s in
  map_pure_len (fun x -> L.mem x l)
    (starl_set_sel_aux #a #b f f_lemma s m0)
    l;
  map_pure_len (fun x -> L.mem x l)
    (starl_set_sel_aux #a #b f f_lemma s (SM.core_mem m0))
    l;
  let v1 = starl_set_sel_aux #a #b f f_lemma s m0 x in
  let v2 = starl_set_sel_aux #a #b f f_lemma s (SM.core_mem m0) x in
  starl_set_imp f s x;
  can_be_split_interp (starl_set f s) (f x) m0;
  can_be_split_interp (starl_set f s) (f x) (SM.core_mem m0)

let starl_set_sel_depends_only_on (#a: eqtype) (#b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (m0: SM.hmem (hp_of (starl_set f s)))
  (m1: SM.mem{SM.disjoint m0 m1})
  : Lemma
  (  starl_set_sel' #a #b f f_lemma s m0
  == starl_set_sel' #a #b f f_lemma s (SM.join m0 m1))
  =
  let m' = SM.join m0 m1 in
  let s1 = starl_set_sel' #a #b f f_lemma s m0 in
  let s2 = starl_set_sel' #a #b f f_lemma s m' in
  let f1 = starl_set_sel_aux #a #b f f_lemma s m0 in
  let f2 = starl_set_sel_aux #a #b f f_lemma s m' in
  let l = FS.set_as_list s in
  let p = fun x -> L.mem x l in
  map_pure_len p f1 l;
  map_pure_len p f2 l;
  //assume (forall x. L.mem x l ==> L.mem x l);
  //Classical.forall_intro (map_pure_index p f1 l);
  //Classical.forall_intro (map_pure_index p f2 l);
  let l1 = map_pure p f1 l in
  let l2 = map_pure p f2 l in
  assume (l1 == l2)
  //L.index_extensionality l1 l2

let starl_set_sel_depends_only_on_core (#a: eqtype) (#b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (m0: SM.hmem (hp_of (starl_set f s)))
  : Lemma
  (  starl_set_sel' #a #b f f_lemma s m0
  == starl_set_sel' #a #b f f_lemma s (SM.core_mem m0))
  =
  let s1 = starl_set_sel' #a #b f f_lemma s m0 in
  let s2 = starl_set_sel' #a #b f f_lemma s (SM.core_mem m0) in
  let f1 = starl_set_sel_aux #a #b f f_lemma s m0 in
  let f2 = starl_set_sel_aux #a #b f f_lemma s (SM.core_mem m0) in
  let l = FS.set_as_list s in
  let p = fun x -> L.mem x l in
  map_pure_len p f1 l;
  map_pure_len p f2 l;
  //assume (forall x. L.mem x l ==> L.mem x l);
  //Classical.forall_intro (map_pure_index p f1 l);
  //Classical.forall_intro (map_pure_index p f2 l);
  let l1 = map_pure p f1 l in
  let l2 = map_pure p f2 l in
  assume (l1 == l2)
  //L.index_extensionality l1 l2

let starl_set_sel (#a: eqtype) (#b: Type0)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  : selector (list (G.erased b)) (hp_of (starl_set f s))
  =
  Classical.forall_intro_2 (starl_set_sel_depends_only_on #a #b f f_lemma s);
  Classical.forall_intro (starl_set_sel_depends_only_on_core #a #b f f_lemma s);
  starl_set_sel' f f_lemma s

[@@ __steel_reduce__]
let starset' (#a: eqtype) (#b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  : vprop'
  = {
    hp = hp_of (starl_set f s);
    t = list (G.erased b);
    sel = starl_set_sel f f_lemma s
  }
unfold
let starset (#a: eqtype) (#b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  = VUnit (starset' #a #b f f_lemma s)

assume
val starset_intro_empty (#opened:_) (#a: eqtype) (#b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  : SteelGhost unit opened
  emp
  (fun _ -> starset #a #b f f_lemma s)
  (requires fun _ -> FS.cardinality s == 0)
  (ensures fun _ _ _ -> True)

assume
val starset_intro_singleton (#opened:_) (#a: eqtype) (#b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (x: a)
  : SteelGhost unit opened
  (f x)
  (fun _ -> starset #a #b f f_lemma s)
  (requires fun _ -> s `FS.equal` FS.singleton x)
  (ensures fun _ _ _ -> True)

assume
val starset_unpack (#opened:_) (#a: eqtype) (#b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (x: a)
  : SteelGhost unit opened
  (starset #a #b f f_lemma s)
  (fun _ ->
    f x `star`
    starset #a #b f f_lemma (FS.remove x s)
  )
  (requires fun _ -> FS.mem x s)
  (ensures fun _ _ _ -> True)

assume
val starset_pack (#opened:_) (#a: eqtype) (#b: Type)
  (f: a -> vprop)
  (f_lemma: (x:a -> Lemma (t_of (f x) == b)))
  (s: FS.set a)
  (x: a)
  : SteelGhost unit opened
  (
    f x `star`
    starset #a #b f f_lemma s
  )
  (fun _ -> starset #a #b f f_lemma (FS.insert x s))
  (requires fun _ -> not (FS.mem x s))
  (ensures fun _ _ _ -> True)
