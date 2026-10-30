import EthLib.Cryptography.Proofs.Vrf.KnownAnswer

/-!
# Proofs: VRF tree known answers at index 0

One opening at the first index, its rejections, and an index out of range.
-/

namespace EthLib.Cryptography.Vrf.KnownAnswer

open EthLib.Cryptography.Vrf
open EthLib.Cryptography.Vrf.Constants

/-! ## Index 0 -/

/-- The opening at index 0. -/
def openingZero : Opening :=
  patternOpening 37 11 29 7 3

/-- The root that the opening at index 0 leads to. -/
def rootZero : Digest :=
  #v[0x6e, 0xc3, 0xc3, 0xf7, 0x50, 0x6b, 0xc5, 0x0c, 0x90, 0x60, 0x05, 0x5d, 0x06, 0x36, 0x7f, 0x44,
    0x96, 0x79, 0x67, 0x66, 0xd6, 0x84, 0x3d, 0xb8, 0xe7, 0x1f, 0x7e, 0x6b, 0xa3, 0x2b, 0x17, 0xba]

/-- The output at index 0. -/
def outputZero : Digest :=
  #v[0x8c, 0x45, 0x98, 0x4a, 0x8f, 0x20, 0x4a, 0x78, 0xf8, 0x78, 0xfe, 0x9e, 0x44, 0x60, 0x1a, 0x44,
    0xa8, 0x73, 0xa9, 0x7f, 0x66, 0x9e, 0x81, 0x6b, 0x63, 0x3e, 0x63, 0x6a, 0x44, 0x33, 0x0b, 0x93]

/-- The opening at index 0 verifies, with its output. -/
theorem verify_zero : verify rootZero 0 openingZero = some outputZero := by
  rw [Kernel.verify_eq]
  decide +kernel

/-- Over bytes, the opening at index 0 verifies, with its output. -/
theorem verifyBytes_zero :
    verifyBytes (packBytes rootZero) 0 (encodeOpening openingZero) = some outputZero := by
  rw [show (0 : Nat) = (0 : UInt32).toNat from rfl, verifyBytes_encode]
  exact verify_zero

/-- A wrong secret at index 0 is rejected. -/
theorem verify_zero_wrongSecret : verify rootZero 0 (wrongSecret openingZero) = none := by
  rw [Kernel.verify_eq]
  decide +kernel

/-- A wrong sibling at index 0 is rejected. -/
theorem verify_zero_wrongSibling : verify rootZero 0 (wrongSibling openingZero) = none := by
  rw [Kernel.verify_eq]
  decide +kernel

/-- The opening at index 0 is rejected at index 1. -/
theorem verify_zero_otherIndex : verify rootZero 1 openingZero = none := by
  rw [Kernel.verify_eq]
  decide +kernel

/-! ## Malformed input -/

/-- Index `2^32` is out of range, so even the valid opening at index 0 is rejected there. -/
theorem verifyBytes_index_out_of_range :
    verifyBytes (packBytes rootZero) (2 ^ 32) (encodeOpening openingZero) = none :=
  verifyBytes_badIndex (Nat.le_refl _)

end EthLib.Cryptography.Vrf.KnownAnswer
