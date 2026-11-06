module

public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Base.Proofs.U256

/-!
# Proofs: `Evm.Instructions.Bitwise`

- AND, OR and XOR act on the bits of the integers, and NOT gives `2^256 - 1 - x`.
- SHL multiplies the integer by `2^shift` modulo 2^256, and SHR divides it by `2^shift`.
- BYTE reads one base-256 digit of the word.
- SHL, SHR and SAR agree with the bit vector shifts, for every shift up to 2^256 - 1.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- AND is the bitwise and of the integers. -/
theorem toNat_bitwiseAnd (x y : U256) : (bitwiseAnd x y).toNat = x.toNat &&& y.toNat :=
  BitVec.toNat_and x y

/-- OR is the bitwise or of the integers. -/
theorem toNat_bitwiseOr (x y : U256) : (bitwiseOr x y).toNat = x.toNat ||| y.toNat :=
  BitVec.toNat_or x y

/-- XOR is the bitwise exclusive or of the integers. -/
theorem toNat_bitwiseXor (x y : U256) : (bitwiseXor x y).toNat = x.toNat ^^^ y.toNat :=
  BitVec.toNat_xor x y

/-- NOT is 2^256 - 1 minus the integer. -/
theorem toNat_bitwiseNot (x : U256) : (bitwiseNot x).toNat = 2 ^ 256 - 1 - x.toNat :=
  BitVec.toNat_not

/-- BYTE `i` of a word is its digit of weight `256^(31 - i)`. -/
theorem toNat_getByte (byteIndex word : U256) (h : byteIndex.toNat < 32) :
    (getByte byteIndex word).toNat = word.toNat / 2 ^ ((31 - byteIndex.toNat) * 8) % 256 := by
  simp only [getByte, show ¬ byteIndex.toNat ≥ 32 by omega, ↓reduceIte, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

/-- SHL is the bit vector shift left, which also gives 0 from 256 bits on. -/
theorem bitwiseShl_eq (shift value : U256) : bitwiseShl shift value = value <<< shift.toNat := by
  unfold bitwiseShl
  split
  · rfl
  · exact (BitVec.shiftLeft_eq_zero (by omega)).symm

/-- SHR is the unsigned bit vector shift right, which also gives 0 from 256 bits on. -/
theorem bitwiseShr_eq (shift value : U256) : bitwiseShr shift value = value >>> shift.toNat := by
  unfold bitwiseShr
  split
  · rfl
  · exact (BitVec.ushiftRight_eq_zero (by omega)).symm

/-- SAR is the signed bit vector shift right.

It also fills every bit with the sign from 256 bits on. -/
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

/-- CLZ counts the leading zeros of the word, as core `BitVec` counts them. -/
theorem countLeadingZeros_eq_clz (x : U256) : countLeadingZeros x = x.clz := by
  by_cases hx : x = 0#256
  · subst hx
    rw [BitVec.clz_eq_iff_eq_zero.mpr rfl]
    decide
  · have hx0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
    have lo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide) hx
    have hi := BitVec.toNat_lt_two_pow_sub_clz (x := x)
    -- A nonzero word has a one bit, so it has fewer than 256 leading zeros.
    have hc : x.clz.toNat < 256 := by
      apply Nat.lt_of_not_le
      intro h
      rw [show 256 - x.clz.toNat = 0 by omega, Nat.pow_zero] at hi
      omega
    -- The highest one bit is at position `255 - clz x`.
    have log : x.toNat.log2 = 255 - x.clz.toNat := by
      apply Nat.le_antisymm
      · have := (Nat.log2_lt hx0).mpr hi
        omega
      · exact (Nat.le_log2 hx0).mpr lo
    apply BitVec.eq_of_toNat_eq
    simp only [countLeadingZeros, bitLength, hx0, ite_false, log, BitVec.toNat_ofNat]
    omega

/-- CLZ is 256 for zero, and `256 - (log2 x + 1)` otherwise, as EIP-7939 states. -/
theorem toNat_countLeadingZeros (x : U256) :
    (countLeadingZeros x).toNat = if x = 0 then 256 else 255 - x.toNat.log2 := by
  have : x.toNat < 2 ^ 256 := x.isLt
  by_cases hx : x = 0
  · subst hx
    decide
  · have hx0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
    have := (Nat.log2_lt hx0).mpr this
    simp only [countLeadingZeros, bitLength, hx0, ite_false, hx, BitVec.toNat_ofNat]
    omega

/-- SHL multiplies by a power of 2, reduced modulo 2^256. -/
theorem toNat_bitwiseShl (shift value : U256) :
    (bitwiseShl shift value).toNat = value.toNat * 2 ^ shift.toNat % 2 ^ 256 := by
  rw [bitwiseShl_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- SHR divides by a power of 2, rounding down. -/
theorem toNat_bitwiseShr (shift value : U256) :
    (bitwiseShr shift value).toNat = value.toNat / 2 ^ shift.toNat := by
  rw [bitwiseShr_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end EthLib.Execution.Evm
