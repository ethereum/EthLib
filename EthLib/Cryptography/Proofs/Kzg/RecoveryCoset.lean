import EthLib.Cryptography.Proofs.Kzg.VanishingNonzero
import EthLib.Cryptography.Proofs.Kzg.FftEvaluation

/-!
# Proofs: the recovery coset avoids every root

Recovery divides by the vanishing polynomial `Z` on a shifted copy of the domain.

`Z` is zero on missing positions of the unshifted domain.

The shift is a generator of the whole multiplicative group, so no shifted point is a root of unity of the domain.

So `Z` is nonzero at every shifted point, and no division is by zero.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

private theorem fr_mul_pow (a b : Fr) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := mul_pow a b n
private theorem fr_pow_mul (a : Fr) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := pow_mul a m n
private theorem fr_one_pow (n : Nat) : (1 : Fr) ^ n = 1 := one_pow n
private theorem fr_mul_one (a : Fr) : a * 1 = a := mul_one a

/-- The recovery shift is a generator of the full scalar multiplicative group. -/
theorem isPrimitiveRoot_recoveryShift :
    IsPrimitiveRoot (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) (BLS_MODULUS - 1) := by
  have h := Bls.Fr.isPrimitiveRoot_ofNat_seven_pow (dvd_refl (Fr.modulus - 1))
  rw [Nat.div_self (by decide : 0 < Fr.modulus - 1), Bls.Fr.hpow_eq_pow] at h
  -- The generator and the group order differ from `h` only by closed arithmetic.
  convert h using 2 <;> decide

/-- Every point on the recovery coset lies outside the extended roots-of-unity domain. -/
theorem recoveryCoset_pow_ne_one (i : Nat) :
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY * domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) ^
      FIELD_ELEMENTS_PER_EXT_BLOB ≠ (1 : Fr) := by
  have hω : domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ FIELD_ELEMENTS_PER_EXT_BLOB = (1 : Fr) := (isPrimitiveRoot_domainRoot
    (Nat.dvd_of_mod_eq_zero (by decide) : FIELD_ELEMENTS_PER_EXT_BLOB ∣ BLS_MODULUS - 1)).pow_eq_one
  have hg := isPrimitiveRoot_recoveryShift.pow_ne_one_of_pos_of_lt
    (by decide : FIELD_ELEMENTS_PER_EXT_BLOB ≠ 0)
    (by decide : FIELD_ELEMENTS_PER_EXT_BLOB < BLS_MODULUS - 1)
  rw [fr_mul_pow, ← fr_pow_mul, Nat.mul_comm i FIELD_ELEMENTS_PER_EXT_BLOB, fr_pow_mul, hω,
    fr_one_pow, fr_mul_one]
  exact hg

/-- Raising a recovery-coset point to the cell width never gives a reduced-domain root. -/
theorem recoveryCoset_cellPower_ne_root (i j : Nat) :
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY * domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) ^
      FIELD_ELEMENTS_PER_CELL ≠ domainRoot CELLS_PER_EXT_BLOB ^ j := by
  intro h
  have hp := congrArg (fun x : Fr => x ^ CELLS_PER_EXT_BLOB) h
  have hω : domainRoot CELLS_PER_EXT_BLOB ^ CELLS_PER_EXT_BLOB = (1 : Fr) := (isPrimitiveRoot_domainRoot
    (Nat.dvd_of_mod_eq_zero (by decide) : CELLS_PER_EXT_BLOB ∣ BLS_MODULUS - 1)).pow_eq_one
  rw [← fr_pow_mul, ← fr_pow_mul, Nat.mul_comm j CELLS_PER_EXT_BLOB, fr_pow_mul (domainRoot CELLS_PER_EXT_BLOB), hω, fr_one_pow] at hp
  exact recoveryCoset_pow_ne_one i hp

/-- The vanishing polynomial used for recovery is nonzero throughout its shifted coset. -/
theorem constructVanishingPolynomial_recoveryCoset_ne_zero
    {missing : Array CellIndex} {p : PolynomialCoeff}
    (hp : constructVanishingPolynomial missing = .ok p) (i : Nat) :
    evalPolyAt p
      (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY * domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) ≠ 0 := by
  obtain ⟨q, hq, he⟩ := evalPolyAt_constructVanishingPolynomial hp
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY * domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i)
  rw [he]
  apply vanishingPolynomialcoeff_eval_ne_zero hq
  rw [Array.toList_map]
  intro hm
  obtain ⟨m, _, hm⟩ := List.mem_map.mp hm
  have hj : BitReversal.reverseBits m CELLS_PER_EXT_BLOB <
      (computeRootsOfUnity CELLS_PER_EXT_BLOB).size := by
    rw [size_computeRootsOfUnity]
    exact BitReversal.reverseBits_lt_two_pow m 7
  rw [getElem!_pos (computeRootsOfUnity CELLS_PER_EXT_BLOB)
    (BitReversal.reverseBits m CELLS_PER_EXT_BLOB) hj, getElem_computeRootsOfUnity] at hm
  apply recoveryCoset_cellPower_ne_root i (BitReversal.reverseBits m CELLS_PER_EXT_BLOB)
  rw [← Bls.Fr.powNat_eq_pow]
  exact hm.symm

/-- Every actual denominator array entry used in recovery is nonzero. -/
theorem getElem!_recovery_denominator_ne_zero
    {missing : Array CellIndex} {p : PolynomialCoeff}
    (hp : constructVanishingPolynomial missing = .ok p)
    (i : Nat) (hi : i < FIELD_ELEMENTS_PER_EXT_BLOB) :
    (cosetFftField p (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false)[i]! ≠ 0 := by
  rw [getElem!_cosetFftField_eval (k := 13)
    (ω := domainRoot FIELD_ELEMENTS_PER_EXT_BLOB)
    (isPrimitiveRoot_domainRoot (Nat.dvd_of_mod_eq_zero (by decide))) p
    (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB)
    (size_constructVanishingPolynomial hp) (size_computeRootsOfUnity _)
    (fun j hj => by
      rw [getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) j
        (by rw [size_computeRootsOfUnity]; exact hj), getElem_computeRootsOfUnity]) i hi]
  exact constructVanishingPolynomial_recoveryCoset_ne_zero hp i

end EthLib.Cryptography.Kzg
