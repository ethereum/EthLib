module

public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: 16-byte values as two lanes

A digest, a randomizer, a parameter and an address are 16 bytes, held as two 64-bit lanes.

The lanes and the bytes carry the same little-endian integer.

So a sum on the lanes is the sum on the integer, and the bytes of the lanes are its bytes.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## The integer of two lanes -/

/-- The integer below `2^128` that a 16-byte value's two lanes make: `lo + 2^64 * hi`. -/
def lanesToNat (w : Lanes2) : Nat :=
  w.lo.toNat + 2 ^ 64 * w.hi.toNat

/-- Two lanes make an integer below `2^128`. -/
theorem lanesToNat_lt (w : Lanes2) : lanesToNat w < 2 ^ 128 := by
  have := w.lo.toNat_lt
  have := w.hi.toNat_lt
  unfold lanesToNat
  omega

/-- Two lanes are their integer: the low lane is its remainder by `2^64`, the high its quotient. -/
theorem lanesToNat_injective : Function.Injective lanesToNat := by
  intro a b h
  have := a.lo.toNat_lt
  have := a.hi.toNat_lt
  have := b.lo.toNat_lt
  have := b.hi.toNat_lt
  unfold lanesToNat at h
  have hlo : a.lo.toNat = b.lo.toNat := by omega
  have hhi : a.hi.toNat = b.hi.toNat := by omega
  cases a
  cases b
  simp only [EthLib.Cryptography.Hash.Keccak.Lanes2.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp hlo, UInt64.toNat_inj.mp hhi⟩

/-- The randomizer of trial `c` is `R_0 + c` modulo `2^128`, on the integers of the lanes. -/
theorem lanesToNat_trialRandomizer (w : Lanes2) (c : Nat) :
    lanesToNat (trialRandomizer w c) = (lanesToNat w + c) % 2 ^ 128 := by
  have := w.lo.toNat_lt
  have := w.hi.toNat_lt
  simp only [trialRandomizer, lanesToNat]
  split_ifs with h <;>
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, UInt64.toNat_one, UInt64.toNat_zero] at h ⊢ <;>
    omega

/-! ## The bytes of two lanes -/

/-- Byte `j` of two lanes is byte `j` of the low lane, or byte `j - 8` of the high lane. -/
theorem toNat_getElem_bytes (w : Lanes2) (j : Nat) (hj : j < 16) :
    (w.bytes[j]).toNat =
      if j < 8 then w.lo.toNat / 2 ^ (8 * j) % 256 else w.hi.toNat / 2 ^ (8 * (j - 8)) % 256 := by
  interval_cases j <;>
    simp [EthLib.Cryptography.Hash.Keccak.Lanes2.bytes, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow]

/-- The bytes of two lanes are the little-endian bytes of their integer. -/
theorem bytes_eq (w : Lanes2) : w.bytes = uintToBytes 16 (lanesToNat w) := by
  have := w.lo.toNat_lt
  apply Vector.ext
  intro j hj
  apply UInt8.toNat_inj.mp
  rw [toNat_getElem_bytes _ _ hj]
  simp only [uintToBytes, lanesToNat, Vector.getElem_ofFn, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow]
  interval_cases j <;>
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceLT, Nat.reduceSub, ite_true, ite_false] <;>
    omega

/-- The little-endian integer of the bytes of two lanes is the integer of the lanes. -/
theorem bytesToUint_bytes (w : Lanes2) : bytesToUint w.bytes = lanesToNat w := by
  rw [bytes_eq, Base.bytesToUint_uintToBytes, Nat.mod_eq_of_lt (by simpa using lanesToNat_lt w)]

/-- The bytes of the two lanes read at an offset are the 16 bytes there. -/
theorem bytes_lanes2Read (b : ByteArray) (offset : Nat) (h : offset + 16 ≤ b.size) :
    (Hash.Keccak.Lanes2.read b offset).bytes = readBytes b offset 16 h := by
  apply Vector.ext
  intro j hj
  have hread : (readBytes b offset 16 h)[j] = Base.byteAt b (offset + j) := by
    simp only [Base.readBytes_eq_ofFn_data, Vector.getElem_ofFn, Base.byteAt,
      dite_eq_left_of_eq_true (eq_true (show offset + j < b.size by omega))]
    rfl
  -- Byte `j` is byte `j mod 8` of the lane that holds it, read from the buffer.
  rw [hread, Hash.Keccak.getElem_lanes2_bytes _ _ hj]
  simp only [Hash.Keccak.Lanes2.read]
  split
  · rw [Hash.Keccak.getD_bytesOfLane_laneAt _ _ _ (by omega), Nat.mod_eq_of_lt ‹_›]
  · rw [Hash.Keccak.getD_bytesOfLane_laneAt _ _ _ (by omega)]
    congr 1
    omega

/-- The scheme's name as one lane has the name's 8 bytes. -/
theorem bytesOfLane_seedTagLane : Hash.Keccak.Internal.bytesOfLane SEED_TAG_LANE = SEED_TAG := by
  decide

/-- Two lanes with the same bytes are the same lanes. -/
theorem bytes_injective : Function.Injective EthLib.Cryptography.Hash.Keccak.Lanes2.bytes := by
  intro a b h
  have := congrArg bytesToUint h
  rw [bytesToUint_bytes, bytesToUint_bytes] at this
  exact lanesToNat_injective this

end EthLib.Cryptography.Xmss
