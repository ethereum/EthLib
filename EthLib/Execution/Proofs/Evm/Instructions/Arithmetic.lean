module

public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Base.Proofs.U256
public import EthLib.Execution.Proofs.Evm.PowMod

/-!
# Proofs: `Evm.Instructions.Arithmetic`

- ADD, SUB and MUL give the sum, the difference and the product, reduced modulo 2^256.
- Each division and remainder agrees with the bit vector operation, apart from the divisor 0.
- ADDMOD, MULMOD and EXP return the exact value, reduced once.
- SIGNEXTEND is the sign extension of the low bytes, as a bit vector.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- ADD is the sum of the operands, reduced modulo 2^256. -/
theorem toNat_add (x y : U256) : (add x y).toNat = (x.toNat + y.toNat) % 2 ^ 256 :=
  BitVec.toNat_add x y

/-- SUB is the difference of the operands, reduced modulo 2^256. -/
theorem toNat_sub (x y : U256) : (sub x y).toNat = (2 ^ 256 - y.toNat + x.toNat) % 2 ^ 256 :=
  BitVec.toNat_sub x y

/-- MUL is the product of the operands, reduced modulo 2^256. -/
theorem toNat_mul (x y : U256) : (mul x y).toNat = x.toNat * y.toNat % 2 ^ 256 :=
  BitVec.toNat_mul x y

/-- Truncated division is the sign of the product times the quotient of the absolute values. -/
private theorem tdiv_eq_sign_mul (x y : Int) : x.tdiv y = (x * y).sign * ((x.natAbs / y.natAbs : Nat) : Int) := by
  have h := Int.sign_mul_natAbs (x.tdiv y)
  rw [Int.natAbs_tdiv, Int.sign_tdiv, ← Int.sign_mul] at h
  rw [← h]
  split
  · -- A quotient of 0 has sign 0.
    rename_i hlt
    rw [Nat.div_eq_of_lt hlt]
    simp
  · rfl

/-- The truncated remainder is the sign of the dividend times the remainder of absolute values. -/
private theorem tmod_eq_sign_mul (x y : Int) : x.tmod y = x.sign * ((x.natAbs % y.natAbs : Nat) : Int) := by
  have h := Int.sign_mul_natAbs (x.tmod y)
  rw [Int.natAbs_tmod, Int.sign_tmod] at h
  rw [← h]
  split
  · -- A remainder of 0 has sign 0.
    rename_i hdvd
    have : x.natAbs % y.natAbs = 0 := Nat.mod_eq_zero_of_dvd (Int.natAbs_dvd_natAbs.mpr hdvd)
    simp [this]
  · rfl

/-- DIV is unsigned bit vector division, which also gives 0 for a divisor of 0. -/
theorem div_eq (x y : U256) : div x y = x / y := by
  unfold div
  split
  · rename_i h
    simp [h]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)

/-- DIV of two words below `2^256` is the quotient of their numbers. -/
theorem div_ofNat {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    div (BitVec.ofNat 256 a) (BitVec.ofNat 256 b) = BitVec.ofNat 256 (a / b) := by
  rw [div_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)).symm

/-- MOD is the unsigned bit vector remainder, except for a divisor of 0.

There the bit vector remainder returns the dividend. -/
theorem mod_eq (x y : U256) : mod x y = if y = 0 then 0 else x % y := by
  unfold mod
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_umod]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)

/-- SDIV is signed bit vector division, including the divisor 0 and the quotient of -2^255 by -1. -/
theorem sdiv_eq (x y : U256) : sdiv x y = x.sdiv y := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv]
  simp only [sdiv, U256.toSigned_eq_toInt, U256.fromSigned]
  split
  · rename_i h
    simp [h]
  split
  · -- -2^255 / -1 = 2^255, which wraps to -2^255.
    rename_i _ h
    rw [h.1, h.2, BitVec.toInt_ofInt]
    decide
  · rw [BitVec.toInt_ofInt, tdiv_eq_sign_mul]

/-- SMOD is the signed bit vector remainder, except for a divisor of 0.

There the bit vector remainder returns the dividend. -/
theorem smod_eq (x y : U256) : smod x y = if y = 0 then 0 else x.srem y := by
  simp only [smod, U256.toSigned_eq_toInt, U256.fromSigned]
  have hy : y.toInt = 0 ↔ y = 0 := by
    constructor
    · intro h
      exact BitVec.eq_of_toInt_eq (by simpa using h)
    · intro h
      simp [h]
  by_cases h : y = 0
  · simp [h]
  · simp only [h, ↓reduceIte, show ¬ y.toInt = 0 from fun h' => h (hy.mp h')]
    rw [← tmod_eq_sign_mul, ← BitVec.toInt_srem, BitVec.ofInt_toInt]

/-- ADDMOD reduces the exact sum, which can exceed 2^256, and does not wrap it first. -/
theorem toNat_addmod (x y z : U256) :
    (addmod x y z).toNat = if z = 0 then 0 else (x.toNat + y.toNat) % z.toNat := by
  unfold addmod
  split
  · rfl
  · rename_i h
    have hz : 0 < z.toNat := Nat.pos_of_ne_zero (fun h' => h (BitVec.eq_of_toNat_eq h'))
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hz) z.isLt)

/-- MULMOD reduces the exact product, which can exceed 2^256, and does not wrap it first. -/
theorem toNat_mulmod (x y z : U256) :
    (mulmod x y z).toNat = if z = 0 then 0 else (x.toNat * y.toNat) % z.toNat := by
  unfold mulmod
  split
  · rfl
  · rename_i h
    have hz : 0 < z.toNat := Nat.pos_of_ne_zero (fun h' => h (BitVec.eq_of_toNat_eq h'))
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hz) z.isLt)

/-- EXP is the power modulo 2^256. -/
theorem toNat_exp (base exponent : U256) : (exp base exponent).toNat = base.toNat ^ exponent.toNat % 2 ^ 256 := by
  rw [exp, BitVec.toNat_ofNat, powMod_eq, Nat.mod_mod]

/-- For `byteNum <= 31`, SIGNEXTEND is the sign extension of the low `byteNum + 1` bytes. -/
theorem signextend_eq (byteNum value : U256) (h : byteNum.toNat ≤ 31) :
    signextend byteNum value = (value.setWidth (8 * (byteNum.toNat + 1))).signExtend 256 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  simp only [signextend, show ¬ byteNum.toNat > 31 by omega, ↓reduceIte, BitVec.toNat_setWidth]
  -- Name the width, between 8 and 256 bits, and the low bytes, below `2^width`.
  generalize hw : 8 * (byteNum.toNat + 1) = w
  have hw256 : 2 ^ w ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
  have hlow : value.toNat % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)
  generalize value.toNat % 2 ^ w = low at *
  have hhalf : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  split <;> rename_i hc <;> simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
  · -- Sign bit 0: the low bytes alone.
    simp only [show ¬ 2 ^ (w - 1) ≤ low by omega, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega), Nat.add_zero]
  · -- Sign bit 1: the low bytes, with every higher bit set.
    simp only [show 2 ^ (w - 1) ≤ low by omega, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

end EthLib.Execution.Evm
