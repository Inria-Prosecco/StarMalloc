module Config

open Prelude

let metadata_max = 131072ul

let alg_null = U32.v metadata_max + 1

let alg_null_sizet = US.of_u32 (U32.add metadata_max 1ul)
