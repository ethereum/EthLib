import EthLib.Cryptography.Proofs.Kzg.RecoveryFlatten
import EthLib.Cryptography.Proofs.Kzg.RecoveryProduct

/-!
# Proofs: the masked product identity

Call `E` the flattened evaluations, with zeros where cells are missing.

Call `P` the source polynomial and `Z` the vanishing polynomial of the missing positions.

```text
    known position:     E = P,   so  E * Z = P * Z
    missing position:   Z = 0,   so  E * Z = 0 = P * Z
```

So `E * Z` and `P * Z` agree at all 8192 points of the domain.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

/-- The exact zero-filled, bit-reversed-order evaluation array used in recovery. -/
def recoveryFlatten (indices : Array CellIndex) (cells : Array CosetEvals) : Array Fr :=
  (Array.range indices.size).foldl
    (fun a k => writeRecoveryCell a indices[k]! cells[k]!)
    (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)

/-- The exact missing-cell list used in recovery. -/
def recoveryMissing (indices : Array CellIndex) : Array CellIndex :=
  (Array.range CELLS_PER_EXT_BLOB).filter fun ci => !indices.contains ci

/-- Provided cell entries are evaluations of the source polynomial in cell/bit-reversed order. -/
def RecoverySamplesMatch (p : PolynomialCoeff) (indices : Array CellIndex) (cells : Array CosetEvals) : Prop :=
  ∀ k < indices.size, ∀ j < FIELD_ELEMENTS_PER_CELL,
    (cells[k]!)[j]! = evalPolyAt p
      (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^
        reverseBits (indices[k]! * FIELD_ELEMENTS_PER_CELL + j) FIELD_ELEMENTS_PER_EXT_BLOB)

@[simp] theorem size_recoveryFlatten (indices : Array CellIndex) (cells : Array CosetEvals) :
    (recoveryFlatten indices cells).size = FIELD_ELEMENTS_PER_EXT_BLOB := by
  unfold recoveryFlatten
  rw [← Array.foldl_toList, Array.toList_range]
  have hs (n : Nat) :
      ((List.range n).foldl (fun a k => writeRecoveryCell a indices[k]! cells[k]!)
        (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)).size = FIELD_ELEMENTS_PER_EXT_BLOB := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simpa only [List.foldl_cons, List.foldl_nil, size_writeRecoveryCell] using ih
  exact hs _

/-- Covered positions in the natural-order recovery array equal source evaluations. -/
theorem recoveryFlatten_known
    {p : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hmatch : RecoverySamplesMatch p indices cells)
    (i : Nat) (hi : i < FIELD_ELEMENTS_PER_EXT_BLOB)
    (hknown : ∃ k < indices.size,
      indices[k]! = reverseBits i FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL) :
    (bitReversalPermutation (recoveryFlatten indices cells))[i]! =
      evalPolyAt p (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) := by
  rw [getElem!_pos (bitReversalPermutation (recoveryFlatten indices cells)) i (by
      rw [size_bitReversalPermutation, size_recoveryFlatten]; exact hi),
    getElem_bitReversalPermutation, size_recoveryFlatten]
  unfold recoveryFlatten
  rw [← Array.foldl_toList, Array.toList_range,
    getElem!_flatten_prefix indices cells _
      (fun m => evalPolyAt p (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ reverseBits m FIELD_ELEMENTS_PER_EXT_BLOB))
      hmatch indices.size (Nat.le_refl _) _ (by
        rw [Array.size_replicate]
        exact reverseBits_lt_two_pow i 13), ite_eq_left hknown]
  have hback : reverseBits (reverseBits i FIELD_ELEMENTS_PER_EXT_BLOB) FIELD_ELEMENTS_PER_EXT_BLOB = i :=
    reverseBits_reverseBits (k := 13) hi
  rw [hback]

/-- Uncovered natural-order positions belong to the exact missing-cell list. -/
theorem recoveryMissing_of_not_known (indices : Array CellIndex) (i : Nat)
    (hunknown : ¬ ∃ k < indices.size,
      indices[k]! = reverseBits i FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL) :
    reverseBits i FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL ∈ (recoveryMissing indices).toList := by
  let ci := reverseBits i FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL
  have hci : ci < CELLS_PER_EXT_BLOB := by
    have hrev := reverseBits_lt_two_pow i 13
    change reverseBits i (2 ^ 13) / 64 < 128
    omega
  have hnot : ci ∉ indices.toList := by
    intro hmem
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hmem
    apply hunknown
    refine ⟨k, by simpa using hk, ?_⟩
    rw [getElem!_pos indices k (by simpa using hk)]
    exact he
  simp only [recoveryMissing, Array.toList_filter, Array.toList_range, List.mem_filter,
    List.mem_range]
  refine ⟨hci, ?_⟩
  simpa using hnot

/-- The executable masked evaluation array times the vanishing polynomial agrees with P·Z. -/
theorem recovery_masked_product
    {p z : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hmatch : RecoverySamplesMatch p indices cells)
    (i : Nat) (hi : i < FIELD_ELEMENTS_PER_EXT_BLOB) :
    evalPolyAt z (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) *
      (bitReversalPermutation (recoveryFlatten indices cells))[i]! =
    evalPolyAt p (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) *
      evalPolyAt z (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) := by
  by_cases hknown : ∃ k < indices.size,
      indices[k]! = reverseBits i FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL
  · rw [recoveryFlatten_known hmatch i hi hknown]
    exact mul_comm _ _
  · rw [constructVanishingPolynomial_missing_root hz i (recoveryMissing_of_not_known indices i hknown)]
    exact (Fin.zero_mul _).trans (Fin.mul_zero _).symm

end EthLib.Cryptography.Kzg
