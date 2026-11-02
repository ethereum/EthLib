module

public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Base.Proofs.U256

/-!
# Proofs: `Evm.Instructions.Bitwise`

- BYTE reads one base-256 digit of the word.
- SHL, SHR and SAR agree with the shifts of `BitVec`, for every shift up to 2^256 - 1.

The known answers at the end are the test cases of [EIP-145](https://eips.ethereum.org/EIPS/eip-145#test-cases).
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base

/-- BYTE `i` of a word is its digit of weight `256^(31 - i)`. -/
theorem toNat_getByte (byteIndex word : U256) (h : byteIndex.toNat < 32) :
    (getByte byteIndex word).toNat = word.toNat / 2 ^ ((31 - byteIndex.toNat) * 8) % 256 := by
  simp only [getByte, show ¬ byteIndex.toNat ≥ 32 by omega, ↓reduceIte, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

/-- SHL is `BitVec.shiftLeft`, which also gives 0 from 256 bits on. -/
theorem bitwiseShl_eq (shift value : U256) : bitwiseShl shift value = value <<< shift.toNat := by
  unfold bitwiseShl
  split
  · rfl
  · exact (BitVec.shiftLeft_eq_zero (by omega)).symm

/-- SHR is `BitVec.ushiftRight`, which also gives 0 from 256 bits on. -/
theorem bitwiseShr_eq (shift value : U256) : bitwiseShr shift value = value >>> shift.toNat := by
  unfold bitwiseShr
  split
  · rfl
  · exact (BitVec.ushiftRight_eq_zero (by omega)).symm

/-- SAR is `BitVec.sshiftRight`, which also fills every bit with the sign from 256 bits on. -/
theorem bitwiseSar_eq (shift value : U256) : bitwiseSar shift value = value.sshiftRight shift.toNat := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight]
  simp only [bitwiseSar, U256.toSigned_eq_toInt, U256.fromSigned]
  split
  · -- The shifted integer is the reading of a word, so reducing it changes nothing.
    rw [BitVec.toInt_ofInt, ← BitVec.toInt_sshiftRight, BitVec.toInt_bmod_cancel]
  · -- A word in two's complement lies in [-2^255, 2^255), so dividing by 2^shift gives 0 or -1.
    rename_i hs
    have hlo := BitVec.le_toInt value
    have hhi := BitVec.toInt_lt (x := value)
    have hpow : 2 ^ 256 ≤ 2 ^ shift.toNat := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Int.shiftRight_eq_div_pow]
    have hpow' : (2 : Int) ^ 256 ≤ ((2 ^ shift.toNat : Nat) : Int) := by exact_mod_cast hpow
    push_cast at hpow'
    by_cases hv : value.toInt ≥ 0
    · simp only [hv, ↓reduceIte]
      exact (Int.ediv_eq_zero_of_lt hv (by simp at hhi; omega)).symm
    · simp only [hv, ↓reduceIte, BitVec.toInt_allOnes]
      exact (Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by simp at hlo; omega)).symm

/-! ## Known answers

Each line is one test case of EIP-145, as `shift`, `value` and the result.
-/

/-- Byte 31 is the least significant. -/
example : getByte 31 0xabcd = 0xcd := by decide

/-- Byte 32 is out of range. -/
example : getByte 32 (BitVec.allOnes 256) = 0 := by decide

/-! ### SHL -/

example : bitwiseShl 0x00 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000001 := by decide
example : bitwiseShl 0x00 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseShl 0x01 0x0000000000000000000000000000000000000000000000000000000000000000 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShl 0x01 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000002 := by decide
example : bitwiseShl 0x01 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe := by decide
example : bitwiseShl 0x01 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe := by decide
example : bitwiseShl 0xff 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x8000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShl 0xff 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x8000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShl 0x0100 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShl 0x0100 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShl 0x0101 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide

/-! ### SHR -/

example : bitwiseShr 0x00 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000001 := by decide
example : bitwiseShr 0x00 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseShr 0x01 0x0000000000000000000000000000000000000000000000000000000000000000 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShr 0x01 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShr 0x01 0x8000000000000000000000000000000000000000000000000000000000000000 = 0x4000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShr 0x01 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseShr 0xff 0x8000000000000000000000000000000000000000000000000000000000000000 = 0x0000000000000000000000000000000000000000000000000000000000000001 := by decide
example : bitwiseShr 0xff 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x0000000000000000000000000000000000000000000000000000000000000001 := by decide
example : bitwiseShr 0x0100 0x8000000000000000000000000000000000000000000000000000000000000000 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShr 0x0100 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseShr 0x0101 0x8000000000000000000000000000000000000000000000000000000000000000 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide

/-! ### SAR -/

example : bitwiseSar 0x00 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000001 := by decide
example : bitwiseSar 0x00 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseSar 0x01 0x0000000000000000000000000000000000000000000000000000000000000000 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseSar 0x01 0x0000000000000000000000000000000000000000000000000000000000000001 = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseSar 0x01 0x8000000000000000000000000000000000000000000000000000000000000000 = 0xc000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseSar 0x01 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseSar 0xf8 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x000000000000000000000000000000000000000000000000000000000000007f := by decide
example : bitwiseSar 0xfe 0x4000000000000000000000000000000000000000000000000000000000000000 = 0x0000000000000000000000000000000000000000000000000000000000000001 := by decide
example : bitwiseSar 0xfe 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x0000000000000000000000000000000000000000000000000000000000000001 := by decide
example : bitwiseSar 0xff 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseSar 0xff 0x8000000000000000000000000000000000000000000000000000000000000000 = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseSar 0xff 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseSar 0x0100 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0x0000000000000000000000000000000000000000000000000000000000000000 := by decide
example : bitwiseSar 0x0100 0x8000000000000000000000000000000000000000000000000000000000000000 = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseSar 0x0100 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide
example : bitwiseSar 0x0101 0x8000000000000000000000000000000000000000000000000000000000000000 = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by decide

end EthLib.Execution.Evm.Instructions
