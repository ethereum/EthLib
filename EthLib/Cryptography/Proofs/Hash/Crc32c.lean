module

public import EthLib.Cryptography.Hash.Crc32c
public import EthLib.Cryptography.Proofs.Hash.Crc

/-!
# Proofs: CRC-32C

Every message followed by its digest leaves the remainder `0x1c2d19ed`, as RFC 3720 §12.1 states.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc32c

/-- The residue of the generator of RFC 3720 §12.1 is `0x1c2d19ed`. -/
theorem residue_generator : Crc.residue generator = 0x1c2d19ed := by
  decide +kernel

/-- RFC 3720 §12.1: every message followed by its digest leaves the remainder `0x1c2d19ed`. -/
theorem remainder_append_digest (data : ByteArray) :
    remainder (data ++ ⟨(digest data).toArray⟩) = 0x1c2d19ed := by
  rw [← residue_generator]
  exact Crc.remainder_append_digest generator data

end EthLib.Cryptography.Hash.Crc32c
