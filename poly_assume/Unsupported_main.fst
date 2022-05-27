module Unsupported_main

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

module U = FStar.UInt64
open Extern

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

let f = Unsupported_lib.create_ref #U.t

let f2 (v: U.t) : SteelT (U.t)
  emp (fun _ -> emp)
  =
  let r = f v in
  free (fst r);
  free (snd r);
  return 0UL
