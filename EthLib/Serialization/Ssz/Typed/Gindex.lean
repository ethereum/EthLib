module

public import EthLib.Serialization.Ssz.Typed.Class
public import EthLib.Serialization.Ssz.Type.Paths

/-! The generalized index of a node of a typed value, named by a path through its SSZ type. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
The generalized index that a path names in the tree of every value of a type.

Each step of the path is a field, an element, or a word that a root mixes in.
-/
def SszType.getGeneralizedIndex (α : Type) [SszType α] (path : List PathStep) : Except Err Nat :=
  Ssz.getGeneralizedIndex (desc α) path

end EthLib.Serialization.Ssz
