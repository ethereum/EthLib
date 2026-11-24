module

public import EthLib.Consensus.Types
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic

/-!
# `Consensus.Proofs.Types`

The SSZ forms of a KZG commitment and of a versioned hash keep the laws of their bytes.

Each is a structure around its bytes, so it encodes, decodes and roots as those bytes.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

instance : LawfulSszType Cryptography.Kzg.VersionedHash :=
  .wrapper Cryptography.Kzg.VersionedHash.mk Cryptography.Kzg.VersionedHash.bytes
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType Cryptography.Kzg.KZGCommitment :=
  .wrapper Cryptography.Kzg.KZGCommitment.mk Cryptography.Kzg.KZGCommitment.bytes
    (fun _ => rfl) (fun _ => rfl)

/-- The SSZ values of commitments are the values of their bytes. -/
theorem map_toValue_kzgCommitment (commitments : List Cryptography.Kzg.KZGCommitment) :
    commitments.map SszType.toValue = (commitments.map (·.bytes)).map SszType.toValue := by
  rw [List.map_map]
  rfl

end EthLib.Consensus
