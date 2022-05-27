module Unsupported_lib

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
open Extern

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

inline_for_extraction noextract
let create_ref (#a: Type0) (v: a) : SteelT (ref U.t & ref a)
  emp (fun r -> vptr (fst r) `star` vptr (snd r))
  =
  let r1 = f1 1UL in
  let r2 = f2 v in
  return (r1, r2)
