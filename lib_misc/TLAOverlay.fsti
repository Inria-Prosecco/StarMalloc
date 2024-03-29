module TLAOverlay

module G = FStar.Ghost
module L = FStar.List.Tot
module US = FStar.SizeT
module TLA = Steel.TLArray

noextract
val split (#a: Type0) (x: TLA.t a) (n: nat)
  : Pure (TLA.t a & TLA.t a)
  (requires n < TLA.length x)
  (ensures fun (x1, x2) ->
    G.reveal (TLA.v x)
    == G.reveal (TLA.v x1) `L.append` G.reveal (TLA.v x2) /\
    TLA.length x1 == n /\
    TLA.length x2 == TLA.length x - n
  )

noextract
val merge (#a: Type0) (x1 x2: TLA.t a)
  : Pure (TLA.t a)
  (requires True)
  (ensures fun x ->
    G.reveal (TLA.v x)
    == G.reveal (TLA.v x1) `L.append` G.reveal (TLA.v x2)
  )

noextract
val split_lemma1 (#a: Type0) (x: TLA.t a) (n: US.t) (i: US.t)
  : Lemma
  (requires
    US.v n < TLA.length x /\
    US.v i < US.v n)
  (ensures (
    let (x1, x2) = split x (US.v n) in
    TLA.get x1 i == TLA.get x i
  ))

noextract
val split_lemma2 (#a: Type0) (x: TLA.t a) (n: US.t) (i: US.t)
  : Lemma
  (requires
    US.v n < TLA.length x /\
    US.v i >= US.v n /\
    US.v i < TLA.length x)
  (ensures (
    let (x1, x2) = split x (US.v n) in
    US.v (US.sub i n) < TLA.length x2 /\
    TLA.get x2 (US.sub i n) == TLA.get x i
  ))
