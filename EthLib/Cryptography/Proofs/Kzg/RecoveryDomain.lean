import EthLib.Cryptography.Proofs.Kzg.RecoveryCoset

/-!
# Proofs: missing cells are roots of the vanishing polynomial

Cells live in bit-reversed order, while FFT positions are in natural order.

This file connects the two orders.

So every FFT position that belongs to a missing cell is a root of the vanishing polynomial.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

/-- Cell-level bit reversal selects the low seven bits of the natural FFT index. -/
theorem reverseBits_cellOfRoot (j : Nat) :
    reverseBits (reverseBits j FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL)
      CELLS_PER_EXT_BLOB = j % CELLS_PER_EXT_BLOB := by
  change reverseBits (reverseBits j (2 ^ 13) / 2 ^ 6) (2 ^ 7) = j % 2 ^ 7
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_reverseBits, Nat.testBit_mod_two_pow]
  by_cases ht : t < 7
  · rw [ite_eq_left ht, Nat.testBit_div_two_pow, testBit_reverseBits,
      ite_eq_left (by omega)]
    simp only [decide_eq_true ht, Bool.true_and]
    congr 1
    omega
  · rw [ite_eq_right ht]
    simp [ht]

/-- The extended-domain generator maps to the cell-domain generator by a 64th power. -/
theorem domainRoot_extended_pow_cell :
    domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ FIELD_ELEMENTS_PER_CELL =
      domainRoot CELLS_PER_EXT_BLOB := by
  unfold domainRoot
  rw [Bls.Fr.hpow_eq_pow, Bls.Fr.hpow_eq_pow]
  have h1 : (Fr.ofNat ((BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_EXT_BLOB)).val =
      (BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_EXT_BLOB := by decide
  have h2 : (Fr.ofNat ((BLS_MODULUS - 1) / CELLS_PER_EXT_BLOB)).val =
      (BLS_MODULUS - 1) / CELLS_PER_EXT_BLOB := by decide
  rw [h1, h2]
  have hpow (x : Fr) (a b : Nat) : (x ^ a) ^ b = x ^ (a * b) := (pow_mul x a b).symm
  rw [hpow]
  congr 1

/-- Natural FFT roots have the cell powers expected by the vanishing-polynomial constructor. -/
theorem extendedRoot_cellPower (j : Nat) :
    Fr.powNat (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ j) FIELD_ELEMENTS_PER_CELL =
      (computeRootsOfUnity CELLS_PER_EXT_BLOB)[reverseBits
        (reverseBits j FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL)
        CELLS_PER_EXT_BLOB]! := by
  rw [reverseBits_cellOfRoot]
  have hj : j % CELLS_PER_EXT_BLOB < (computeRootsOfUnity CELLS_PER_EXT_BLOB).size := by
    rw [size_computeRootsOfUnity]
    exact Nat.mod_lt _ (by decide)
  rw [getElem!_pos (computeRootsOfUnity CELLS_PER_EXT_BLOB) _ hj,
    getElem_computeRootsOfUnity, Bls.Fr.powNat_eq_pow]
  have hp (x : Fr) (a b : Nat) : (x ^ a) ^ b = (x ^ b) ^ a := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hp, domainRoot_extended_pow_cell]
  have hω : domainRoot CELLS_PER_EXT_BLOB ^ CELLS_PER_EXT_BLOB = (1 : Fr) :=
    (isPrimitiveRoot_domainRoot
      (Nat.dvd_of_mod_eq_zero (by decide) : CELLS_PER_EXT_BLOB ∣ BLS_MODULUS - 1)).pow_eq_one
  have hadd (x : Fr) (a b : Nat) : x ^ (a + b) = x ^ a * x ^ b := pow_add x a b
  have hmul (x : Fr) (a b : Nat) : x ^ (a * b) = (x ^ a) ^ b := pow_mul x a b
  conv_lhs => rw [← Nat.mod_add_div j CELLS_PER_EXT_BLOB]
  rw [hadd, hmul, hω]
  have hone (n : Nat) : (1 : Fr) ^ n = 1 := one_pow n
  rw [hone]
  exact mul_one _

/-- An erased cell's natural-order FFT positions are zeros of the constructed vanishing polynomial. -/
theorem constructVanishingPolynomial_missing_root
    {missing : Array CellIndex} {z : PolynomialCoeff}
    (hz : constructVanishingPolynomial missing = .ok z) (j : Nat)
    (hm : reverseBits j FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL ∈ missing.toList) :
    evalPolyAt z (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ j) = Fr.zero :=
  constructVanishingPolynomial_eval_eq_zero hz hm (extendedRoot_cellPower j)

end EthLib.Cryptography.Kzg
