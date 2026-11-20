module

public import EthLib.Serialization.Proofs.Ssz.Codec.BindingTrace

/-!
# Proofs: the inputs of the node hash in the root of a value

The root of a value hashes pairs of nodes, one 64-byte input at a time.

Those inputs are the messages of the tree that computes the root.

A value whose tree cannot be built has no messages.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The inputs of the binary hashes that the root of a value of a type computes.

They are the messages of its tree, and none when the tree cannot be built. -/
def valueMessages (shape : Desc) (value : Value) : List Bytes :=
  ((valueTree shape value).toOption.map (·.messages)).getD []

/-- The messages of a value whose tree is built are the messages of that tree. -/
theorem valueMessages_of_valueTree {shape : Desc} {value : Value} {tree : CommitmentTree}
    (built : valueTree shape value = .ok tree) : valueMessages shape value = tree.messages := by
  simp [valueMessages, built, Except.toOption]

end EthLib.Serialization.Ssz
