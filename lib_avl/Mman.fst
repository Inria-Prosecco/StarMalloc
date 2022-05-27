module Mman

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I32 = FStar.Int32

noextract
assume val mmap
  (addr: U64.t)
  (len: U32.t)
  (prot: I32.t)
  (flags: I32.t)
  (fildes: I32.t)
  (off: U32.t)
  : U64.t

noextract
assume val munmap (addr: U64.t) (size_t: U32.t): U32.t
