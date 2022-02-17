module Impl

include Impl.Trees
include Impl.Trees.Rotate
include Impl.BST
include Impl.AVL


open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

//module Spec = Trees
module U = FStar.UInt64
module I = FStar.Int64

open Impl.Core


/// The implementation of the Selectors.Tree interface.
/// Predicates prefixed by (**) correspond to stateful lemmas for folding and unfolding the tree predicate

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

