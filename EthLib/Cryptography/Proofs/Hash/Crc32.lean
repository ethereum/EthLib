module

public import EthLib.Cryptography.Hash.Crc32
public import EthLib.Cryptography.Proofs.Hash.Crc

/-!
# Proofs: CRC-32

Every message followed by its digest leaves the remainder `0xc704dd7b`.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc32

/-- The residue of the generator of CRC-32 is `0xc704dd7b`. -/
theorem residue_generator : Crc.residue generator = 0xc704dd7b := by
  decide +kernel

/-- Every message followed by its digest leaves the remainder `0xc704dd7b`. -/
theorem remainder_append_digest (data : ByteArray) :
    Crc.remainder generator (data ++ ⟨(digest data).toArray⟩) = 0xc704dd7b := by
  rw [← residue_generator]
  exact Crc.remainder_append_digest generator data

end EthLib.Cryptography.Hash.Crc32
