module

/-!
# Proofs: masks and digits of a bit vector

A mask of the `k` low bits keeps the integer modulo `2^k`.

Its complement rounds the integer down to a multiple of `2^k`.

A shift right by `s` then a mask of `k` bits reads the bits from `s` up.

With `s = 8 i` and `k = 8`, it reads byte `i`.

Two vectors with no common one bit add as integers when they are joined by an or.
-/

@[expose] public section

namespace EthLib.Base.BitVec

/-- A mask of the `k` low bits keeps the integer modulo `2^k`, for every `k`. -/
theorem toNat_and_ofNat_two_pow_sub_one {w : Nat} (x : BitVec w) (k : Nat) :
    (x &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.testBit_and, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < w
  · by_cases hk : i < k <;> simp [hi, hk]
  · -- Bits from `w` up are 0 in a vector of width `w`.
    have : x.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega)
        (by omega)))
    simp [hi, this]

/-- Two vectors with no common one bit add as integers when joined by an or. -/
theorem toNat_or_of_and_eq_zero {w : Nat} {x y : BitVec w} (h : x &&& y = 0#w) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  rw [← BitVec.add_eq_or_of_and_eq_zero x y h, BitVec.toNat_add_of_and_eq_zero h]

/-- The complement of a mask of the `k` low bits rounds the integer down to a multiple of `2^k`. -/
theorem toNat_and_not_ofNat_two_pow_sub_one {w : Nat} (x : BitVec w) (k : Nat) :
    (x &&& ~~~BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat / 2 ^ k * 2 ^ k := by
  -- The low bits and the high bits of `x` share no bit, and together they give `x` back.
  have disjoint : (x &&& BitVec.ofNat w (2 ^ k - 1)) &&& (x &&& ~~~BitVec.ofNat w (2 ^ k - 1)) =
      0#w := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases x[i] <;> cases (BitVec.ofNat w (2 ^ k - 1))[i] <;> rfl
  have whole : (x &&& BitVec.ofNat w (2 ^ k - 1)) ||| (x &&& ~~~BitVec.ofNat w (2 ^ k - 1)) =
      x := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases x[i] <;> cases (BitVec.ofNat w (2 ^ k - 1))[i] <;> rfl
  have sum := congrArg BitVec.toNat whole
  rw [toNat_or_of_and_eq_zero disjoint, toNat_and_ofNat_two_pow_sub_one] at sum
  have := Nat.mod_add_div x.toNat (2 ^ k)
  rw [Nat.mul_comm] at this
  omega

/-- A shift right by `s` then a mask of `k` bits keeps the `k` integer bits from bit `s` up. -/
theorem toNat_ushiftRight_and_ofNat_two_pow_sub_one {w : Nat} (x : BitVec w) (s k : Nat) :
    ((x >>> s) &&& BitVec.ofNat w (2 ^ k - 1)).toNat = x.toNat / 2 ^ s % 2 ^ k := by
  rw [toNat_and_ofNat_two_pow_sub_one, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A shift right then a mask is the extraction of the same bits, set back to width `w`. -/
theorem ushiftRight_and_ofNat_two_pow_sub_one {w : Nat} (x : BitVec w) (s k : Nat) :
    (x >>> s) &&& BitVec.ofNat w (2 ^ k - 1) = (x.extractLsb' s k).setWidth w := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ushiftRight_and_ofNat_two_pow_sub_one, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  -- The digit is at most the integer, which is below `2^w`.
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt))).symm

/-- Byte `i`, from the least significant end, is the base 256 digit of weight `256^i`. -/
theorem toNat_ushiftRight_and_0xff {w : Nat} (x : BitVec w) (i : Nat) :
    ((x >>> (8 * i)) &&& 0xff#w).toNat = x.toNat / 256 ^ i % 256 := by
  rw [show (0xff#w) = BitVec.ofNat w (2 ^ 8 - 1) from rfl,
    toNat_ushiftRight_and_ofNat_two_pow_sub_one, Nat.pow_mul]

/-- The extraction of byte `i` is the base 256 digit of weight `256^i`. -/
theorem toNat_extractLsb'_byte {w : Nat} (x : BitVec w) (i : Nat) :
    (x.extractLsb' (8 * i) 8).toNat = x.toNat / 256 ^ i % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

end EthLib.Base.BitVec
