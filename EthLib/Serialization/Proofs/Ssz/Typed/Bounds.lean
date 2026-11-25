module

public import EthLib.Serialization.Proofs.Ssz.Codec.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# Proofs: typed values whose encodings stay below the offset range

A value of a lawful type whose largest encoding stays below `2^32` bytes always serializes.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.SszType

variable {α : Type} [SszType α] [LawfulSszType α]

/-- A value of a lawful type whose encodings stay below `2^32` bytes serializes. -/
theorem serialize_exists_ok_of_maxSize (a : α) {bound : Nat}
    (largest : (desc α).maxSize = some bound) (small : bound < 2 ^ 32) :
    ∃ data, serialize a = .ok data := by
  -- The untyped value fits its type, so it encodes, and the typed value stands for it.
  obtain ⟨bytes, wrote⟩ :=
    serialize_fits_exists_ok_of_maxSize (LawfulSszType.fits a) largest small
  exact ⟨bytes, serialize_ok_iff.mpr wrote⟩

end EthLib.Serialization.Ssz.SszType
