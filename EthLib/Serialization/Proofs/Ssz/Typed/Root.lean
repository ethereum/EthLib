module

public import EthLib.Serialization.Proofs.Ssz.Typed.Class
public import EthLib.Serialization.Proofs.Ssz.Codec.Binding
public import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain

/-!
# Proofs: the root of a typed SSZ value

Every lawful typed value has a 32-byte root.

Two values with one root are equal, or the two root computations contain a SHA-256 collision.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType

namespace SszType

variable {α : Type} [SszType α]

/-- The typed root is the untyped root of the value. -/
theorem hashTreeRoot_ok_iff {a : α} {root : Vector UInt8 32} :
    hashTreeRoot a = .ok root ↔ Ssz.hashTreeRoot (desc α) (toValue a) = .ok root.toArray := by
  unfold hashTreeRoot
  cases rooted : Ssz.hashTreeRoot (desc α) (toValue a) with
  | error fault => simp [bind, Except.bind]
  | ok bytes =>
    simp only [bind, Except.bind, Except.ok.injEq]
    exact toChunk_ok_iff

variable [LawfulSszType α]

/-- Every value has a root. -/
theorem hashTreeRoot_total (a : α) : ∃ root, hashTreeRoot a = .ok root := by
  obtain ⟨root, rooted, width⟩ :=
    Ssz.hashTreeRoot_total (desc α) (toValue a) LawfulSszType.wellFormed (LawfulSszType.fits a)
  exact ⟨⟨root, width⟩, hashTreeRoot_ok_iff.mpr rooted⟩

/--
Two values with one root are equal, or a search finds a SHA-256 collision.

The search compares the hash inputs of the two root computations.

It returns two different 64-byte messages with one digest, one hashed in each computation.

Every variable-size count in either value must fit the 256-bit word mixed into its root.
-/
theorem hashTreeRoot_binding {a b : α} {root : Vector UInt8 32}
    (leftSized : CommitmentSized (desc α) (toValue a))
    (rightSized : CommitmentSized (desc α) (toValue b))
    (left : hashTreeRoot a = .ok root) (right : hashTreeRoot b = .ok root) :
    a = b ∨ ∃ leftTree rightTree,
      valueTree (desc α) (toValue a) = .ok leftTree ∧
      valueTree (desc α) (toValue b) = .ok rightTree ∧
      ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
        x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  rcases Ssz.hashTreeRoot_binding LawfulSszType.wellFormed (LawfulSszType.fits a)
      (LawfulSszType.fits b) leftSized rightSized (hashTreeRoot_ok_iff.mp left)
      (hashTreeRoot_ok_iff.mp right) with same | collision
  · -- Equal untyped values read back as equal typed values.
    left
    have back := congrArg (ofValue (α := α)) same
    rw [LawfulSszType.ofValue_toValue, LawfulSszType.ofValue_toValue] at back
    exact Except.ok.inj back
  · exact .inr collision

end SszType

end EthLib.Serialization.Ssz
