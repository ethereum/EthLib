module

public import EthLib.Base.Word32

/-!
# Proofs: `Word32`

Reading four bytes as a little-endian word, and writing the word back, undo each other.
-/

@[expose] public section

namespace EthLib.Base

/-- The four bytes of a word, least significant first, read back as that word. -/
theorem uint32OfBytes_uint32Byte (w : UInt32) :
    uint32OfBytes (uint32Byte w 0) (uint32Byte w 1) (uint32Byte w 2)
      (uint32Byte w 3) = w := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [uint32Byte, uint32OfBytes, UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32,
    UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
  simp +arith [hk]
  -- Bit `k` comes from byte `k / 8`, so split on the byte that holds it.
  have he := BitVec.getLsbD_eq_getElem (x := w.toBitVec) hk
  by_cases h7 : k ≤ 7
  · simp [h7, show k ≤ 15 by omega, show k ≤ 23 by omega]
  by_cases h15 : k ≤ 15
  · simp [h7, h15, show k ≤ 23 by omega, show k - 8 + 8 = k by omega, he]
  by_cases h23 : k ≤ 23
  · simp [h7, h15, h23, show k - 16 + 16 = k by omega, he]
  · simp [h7, h15, h23, show k ≤ 31 by omega, show k - 24 + 24 = k by omega, he]

/-- Each byte of a word read from four bytes is the byte at its place. -/
theorem uint32Byte_uint32OfBytes (b0 b1 b2 b3 : UInt8) :
    uint32Byte (uint32OfBytes b0 b1 b2 b3) 0 = b0 ∧
      uint32Byte (uint32OfBytes b0 b1 b2 b3) 1 = b1 ∧
      uint32Byte (uint32OfBytes b0 b1 b2 b3) 2 = b2 ∧
      uint32Byte (uint32OfBytes b0 b1 b2 b3) 3 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp +arith [uint32Byte, uint32OfBytes, show k ≤ 7 by omega, show k ≤ 15 by omega,
      show k ≤ 23 by omega, show k ≤ 31 by omega]

end EthLib.Base
