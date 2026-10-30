import EthLib.Cryptography.Proofs.Vrf.KnownAnswer

/-!
# Proofs: VRF tree known answers at index `2^32 - 1`

One opening at the last index, and its rejections.
-/

namespace EthLib.Cryptography.Vrf.KnownAnswer

open EthLib.Cryptography.Vrf
open EthLib.Cryptography.Vrf.Constants

/-! ## Index `2^32 - 1` -/

/-- The opening at index `2^32 - 1`. -/
def openingLast : Opening :=
  patternOpening 13 5 31 3 1

/-- The root that the opening at index `2^32 - 1` leads to. -/
def rootLast : Digest :=
  #v[0x2c, 0x49, 0x0d, 0x4d, 0xe0, 0xe4, 0xbe, 0xa8, 0x51, 0xfa, 0xa8, 0xe5, 0x8c, 0x8d, 0x86, 0x54,
    0x89, 0x9c, 0xcd, 0x22, 0xbb, 0x10, 0xfb, 0x82, 0xcb, 0x69, 0x78, 0xd9, 0x26, 0x71, 0x25, 0x11]

/-- The output at index `2^32 - 1`. -/
def outputLast : Digest :=
  #v[0xf9, 0xe8, 0xd5, 0xc3, 0x09, 0x80, 0xce, 0x4c, 0x73, 0x33, 0x88, 0xa5, 0x30, 0x03, 0xde, 0x41,
    0x36, 0xc4, 0x4f, 0x88, 0x29, 0x39, 0x53, 0x69, 0xb1, 0x64, 0x4b, 0x22, 0x2b, 0xbf, 0xcd, 0xf9]

/-- The opening at index `2^32 - 1` verifies, with its output. -/
theorem verify_last : verify rootLast 0xFFFFFFFF openingLast = some outputLast := by
  rw [Kernel.verify_eq]
  decide +kernel

/-- Over bytes, the opening at index `2^32 - 1` verifies, with its output. -/
theorem verifyBytes_last :
    verifyBytes (packBytes rootLast) (2 ^ 32 - 1) (encodeOpening openingLast) = some outputLast := by
  rw [show 2 ^ 32 - 1 = (0xFFFFFFFF : UInt32).toNat from rfl, verifyBytes_encode]
  exact verify_last

/-- A wrong secret at index `2^32 - 1` is rejected. -/
theorem verify_last_wrongSecret : verify rootLast 0xFFFFFFFF (wrongSecret openingLast) = none := by
  rw [Kernel.verify_eq]
  decide +kernel

/-- A wrong sibling at index `2^32 - 1` is rejected. -/
theorem verify_last_wrongSibling : verify rootLast 0xFFFFFFFF (wrongSibling openingLast) = none := by
  rw [Kernel.verify_eq]
  decide +kernel

/-- The opening at index `2^32 - 1` is rejected at index `2^32 - 2`. -/
theorem verify_last_otherIndex : verify rootLast 0xFFFFFFFE openingLast = none := by
  rw [Kernel.verify_eq]
  decide +kernel

end EthLib.Cryptography.Vrf.KnownAnswer
