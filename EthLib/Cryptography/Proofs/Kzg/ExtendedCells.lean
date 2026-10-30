module

public import EthLib.Cryptography.Proofs.Kzg.ExtendedFft
public import EthLib.Cryptography.Proofs.Kzg.CoefficientPadding
public import EthLib.Cryptography.Proofs.Kzg.Cells
-- The successful computation is simplified with the public monad laws.
import Batteries.Lean.LawfulMonad
import Init.Control.Lawful.Instances

/-!
# Proofs: extended evaluations and cells via FFT

The Fulu sampling specification evaluates a polynomial across each cell coset with Horner's rule.

See `consensus-specs` `specs/fulu/polynomial-commitments-sampling.md` at `8a3df1d79d70000801407e33d660171be9cd06d1`.

`extendedEvaluations` pads to 8192 coefficients, runs one forward FFT, and bit-reverses the output.

`cellsOfExtendedEvaluations` cuts those 8192 values into 128 blocks of 64 elements and encodes each cell.

```text
    polynomialCoeff  --pad to 8192-->  FFT  --brp-->  extendedEvaluations
                                                           |
                                   slice [64*k .. 64*(k+1)) = coset.map(Horner)
```

This file proves:

- `evaluatePolynomialcoeff` equals the monomial sum `evalPolyAt`.
- Every 64-element slice of `extendedEvaluations` equals `coset.map (evaluatePolynomialcoeff polynomialCoeff)`.
- Every cell of `cellsOfExtendedEvaluations (extendedEvaluations polynomialCoeff)` matches that encoding.
- On a valid blob, `computeCells` returns 128 cells matching that encoding.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

private theorem fr_pow_zero (a : Fr) : a ^ 0 = 1 := pow_zero a
private theorem fr_mul_one (a : Fr) : a * 1 = a := mul_one a

/-- Element `i` of `bitReversalPermutation seq` is element `reverseBits i seq.size` of `seq`. -/
theorem getElem!_bitReversalPermutation {α : Type _} [Inhabited α] (seq : Array α) (i : Nat)
    (hi : i < seq.size) :
    (bitReversalPermutation seq)[i]! = seq[reverseBits i seq.size]! := by
  have hi' : i < (bitReversalPermutation seq).size := by
    rwa [size_bitReversalPermutation]
  rw [getElem!_pos (bitReversalPermutation seq) i hi',
    getElem_bitReversalPermutation]

/-! ## Horner's rule equals monomial evaluation -/

/-- After `k` steps from the top, Horner's accumulator sums the top `k` terms.

```text
    step 0     : 0
    step k + 1 : acc_k * z + p[n - 1 - k] = sum_{i < k + 1} p[n - 1 - k + i] * z^i
```
-/
private theorem horner_foldl_eq_sum (p : PolynomialCoeff) (z : Fr) (k : Nat) (hk : k ≤ p.size) :
    ((List.range k).foldl (fun y i => y * z + p[p.size - 1 - i]!) Fr.zero) =
      ∑ j ∈ Finset.range k, p[p.size - k + j]! * z ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
    -- Split off the constant term j = 0 in the target sum of length k + 1.
    rw [Finset.sum_range_succ']
    -- Multiply the length-k sum by z, shifting every power z^j to z^(j + 1).
    rw [Finset.sum_mul]
    have hshift :
        (∑ x ∈ Finset.range k, p[p.size - k + x]! * z ^ x * z) =
          ∑ x ∈ Finset.range k, p[p.size - (k + 1) + (x + 1)]! * z ^ (x + 1) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      have hidx : p.size - k + x = p.size - (k + 1) + (x + 1) := by omega
      rw [hidx, pow_succ]
      exact Bls.Fr.mul_assoc _ _ _
    rw [hshift]
    have h0 : p.size - (k + 1) + 0 = p.size - 1 - k := by omega
    rw [h0, fr_pow_zero, fr_mul_one]

/-- `evaluatePolynomialcoeff` computes the monomial sum `evalPolyAt`. -/
theorem evaluatePolynomialcoeff_eq_evalPolyAt (p : PolynomialCoeff) (z : Fr) :
    evaluatePolynomialcoeff p z = evalPolyAt p z := by
  unfold evaluatePolynomialcoeff
  dsimp only
  rw [← Array.foldl_toList, Array.toList_range, horner_foldl_eq_sum p z p.size (Nat.le_refl _)]
  rw [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.sub_self, Nat.zero_add]

/-! ## Padding in `extendedEvaluations` -/

/-- Appending `n - p.size` zeros agrees with `padCoefficients n p` when `p.size <= n`. -/
theorem append_replicate_zero_eq_padCoefficients (n : Nat) (p : PolynomialCoeff) (hp : p.size ≤ n) :
    p ++ Array.replicate (n - p.size) Fr.zero = padCoefficients n p := by
  apply Array.ext
  · simp [hp]
  · intro i hi1 hi2
    rw [← getElem!_pos (padCoefficients n p) i hi2, getElem!_padCoefficients n p hp i]
    by_cases hip : i < p.size
    · rw [Array.getElem_append_left hip, getElem!_pos p i hip]
    · rw [Array.getElem_append_right (Nat.le_of_not_lt hip), Array.getElem_replicate,
        getElem!_neg p i hip]
      rfl

/-! ## Pointwise and cell-slice characterization of `extendedEvaluations` -/

/-- `extendedEvaluations` produces `FIELD_ELEMENTS_PER_EXT_BLOB` values. -/
@[simp] theorem size_extendedEvaluations (polynomialCoeff : PolynomialCoeff)
    (hp : polynomialCoeff.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) :
    (extendedEvaluations polynomialCoeff).size = FIELD_ELEMENTS_PER_EXT_BLOB := by
  unfold extendedEvaluations
  rw [append_replicate_zero_eq_padCoefficients FIELD_ELEMENTS_PER_EXT_BLOB polynomialCoeff hp,
    size_bitReversalPermutation, size_fftField, size_padCoefficients]

/-- Entry `m` of `extendedEvaluations` evaluates `polynomialCoeff` at `(rootsOfUnityBrp 8192)[m]!`. -/
theorem getElem!_extendedEvaluations (polynomialCoeff : PolynomialCoeff)
    (hp : polynomialCoeff.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB)
    (m : Nat) (hm : m < FIELD_ELEMENTS_PER_EXT_BLOB) :
    (extendedEvaluations polynomialCoeff)[m]! =
      evaluatePolynomialcoeff polynomialCoeff (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[m]! := by
  let f := fftField (padCoefficients FIELD_ELEMENTS_PER_EXT_BLOB polynomialCoeff)
    (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false
  have hfsz : f.size = FIELD_ELEMENTS_PER_EXT_BLOB := by
    simp [f]
  have hrev_lt : reverseBits m FIELD_ELEMENTS_PER_EXT_BLOB < FIELD_ELEMENTS_PER_EXT_BLOB :=
    reverseBits_lt_two_pow m 13
  have hbeq : (extendedEvaluations polynomialCoeff)[m]! = (bitReversalPermutation f)[m]! := by
    unfold extendedEvaluations
    rw [append_replicate_zero_eq_padCoefficients FIELD_ELEMENTS_PER_EXT_BLOB polynomialCoeff hp]
  rw [hbeq, getElem!_bitReversalPermutation f m (by rwa [hfsz]), hfsz]
  -- Evaluate the forward FFT entry at the bit-reversed index.
  have hfft := getElem!_fftField_extended
    (padCoefficients FIELD_ELEMENTS_PER_EXT_BLOB polynomialCoeff)
    (size_padCoefficients _ _)
    (reverseBits m FIELD_ELEMENTS_PER_EXT_BLOB) hrev_lt
  rw [hfft, evalPolyAt_padCoefficients _ _ hp, ← evaluatePolynomialcoeff_eq_evalPolyAt]
  -- Match the evaluation point with `rootsOfUnityBrp`.
  have hdom : (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[m]! =
      domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ reverseBits m FIELD_ELEMENTS_PER_EXT_BLOB := by
    rw [rootsOfUnityBrp, getElem!_bitReversalPermutation _ m (by
        rw [size_computeRootsOfUnity]; exact hm),
      size_computeRootsOfUnity,
      getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) _ (by
        rw [size_computeRootsOfUnity]; exact hrev_lt),
      getElem_computeRootsOfUnity]
  rw [hdom]

/-- Block `cellIndex` of `extendedEvaluations` equals `coset.map (evaluatePolynomialcoeff polynomialCoeff)`. -/
theorem extract_extendedEvaluations_eq_coset_map
    {polynomialCoeff : PolynomialCoeff} {cellIndex : CellIndex} {coset : Coset}
    (hp : polynomialCoeff.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB)
    (hcoset : cosetForCell cellIndex = .ok coset) :
    (extendedEvaluations polynomialCoeff).extract
        (cellIndex * FIELD_ELEMENTS_PER_CELL)
        ((cellIndex + 1) * FIELD_ELEMENTS_PER_CELL) =
      coset.map (evaluatePolynomialcoeff polynomialCoeff) := by
  have hci : cellIndex < CELLS_PER_EXT_BLOB :=
    cosetForCell_ok_iff.mp ⟨coset, hcoset⟩
  obtain ⟨c', hc', hcsz, hcelem⟩ := cosetForCell_ok_of_lt hci
  have hceq : coset = c' := Except.ok.inj (hcoset.symm.trans hc')
  subst hceq
  have hext_sz : (extendedEvaluations polynomialCoeff).size = FIELD_ELEMENTS_PER_EXT_BLOB :=
    size_extendedEvaluations polynomialCoeff hp
  have hstop_le : (cellIndex + 1) * FIELD_ELEMENTS_PER_CELL ≤ FIELD_ELEMENTS_PER_EXT_BLOB :=
    Nat.mul_le_mul_right FIELD_ELEMENTS_PER_CELL (Nat.succ_le_of_lt hci)
  apply Array.ext
  · rw [Array.size_extract, Array.size_map, hext_sz, hcsz, Nat.min_eq_left hstop_le,
      Nat.succ_mul, Nat.add_sub_cancel_left]
  · intro j hj1 hj2
    have hj : j < FIELD_ELEMENTS_PER_CELL := by
      rwa [Array.size_map, hcsz] at hj2
    rw [Array.getElem_extract, Array.getElem_map]
    have hm_lt : cellIndex * FIELD_ELEMENTS_PER_CELL + j < FIELD_ELEMENTS_PER_EXT_BLOB :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj (cellIndex * FIELD_ELEMENTS_PER_CELL))
        (Nat.succ_mul cellIndex FIELD_ELEMENTS_PER_CELL ▸ hstop_le)
    have hm_sz : cellIndex * FIELD_ELEMENTS_PER_CELL + j < (extendedEvaluations polynomialCoeff).size := by
      rwa [hext_sz]
    rw [← getElem!_pos (extendedEvaluations polynomialCoeff) _ hm_sz,
      getElem!_extendedEvaluations polynomialCoeff hp _ hm_lt]
    have hc_pos : coset[j]' (by rwa [Array.size_map] at hj2) = coset[j]! :=
      (getElem!_pos coset j (by rw [hcsz]; exact hj)).symm
    rw [hc_pos, hcelem j hj, Nat.mul_comm FIELD_ELEMENTS_PER_CELL cellIndex]

/-! ## `cellsOfExtendedEvaluations` and `computeCells` -/

/-- `cellsOfExtendedEvaluations` produces `CELLS_PER_EXT_BLOB` cells. -/
@[simp] theorem size_cellsOfExtendedEvaluations (evals : Array Fr) :
    (cellsOfExtendedEvaluations evals).size = CELLS_PER_EXT_BLOB := by
  simp [cellsOfExtendedEvaluations]

/-- Cell `cellIndex` of `cellsOfExtendedEvaluations (extendedEvaluations f)` matches the per-cell encoding. -/
theorem getElem!_cellsOfExtendedEvaluations_extendedEvaluations
    {polynomialCoeff : PolynomialCoeff} {cellIndex : CellIndex} {coset : Coset}
    (hp : polynomialCoeff.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB)
    (hcoset : cosetForCell cellIndex = .ok coset) :
    (cellsOfExtendedEvaluations (extendedEvaluations polynomialCoeff))[cellIndex]! =
      cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff)) := by
  have hci : cellIndex < CELLS_PER_EXT_BLOB :=
    cosetForCell_ok_iff.mp ⟨coset, hcoset⟩
  unfold cellsOfExtendedEvaluations
  rw [getElem!_pos _ cellIndex (by simp [hci]), Array.getElem_map, Array.getElem_range]
  rw [extract_extendedEvaluations_eq_coset_map hp hcoset]

/-- `polynomialEvalToCoeff` preserves array length. -/
@[simp] theorem size_polynomialEvalToCoeff (poly : Polynomial) :
    (polynomialEvalToCoeff poly).size = poly.size := by
  simp [polynomialEvalToCoeff, size_bitReversalPermutation]

/-- On a valid blob, `computeCells` returns 128 cells matching the per-cell Horner encoding. -/
theorem computeCells_ok_spec {blob : Blob} {poly : Polynomial}
    (hblob : blobToPolynomial blob = .ok poly) :
    ∃ cells,
      computeCells blob = pure cells ∧
      cells.size = CELLS_PER_EXT_BLOB ∧
      ∀ cellIndex coset, cosetForCell cellIndex = .ok coset →
        cells[cellIndex]! =
          cosetEvalsToCell (coset.map (evaluatePolynomialcoeff (polynomialEvalToCoeff poly))) := by
  have hbsize : blob.size = BYTES_PER_BLOB := by
    by_contra hne
    have herr := (blobToPolynomial_error_badBlobSize blob blob.size).mpr ⟨hne, rfl⟩
    rw [hblob] at herr
    cases herr
  have hp_le : (polynomialEvalToCoeff poly).size ≤ FIELD_ELEMENTS_PER_EXT_BLOB := by
    rw [size_polynomialEvalToCoeff, size_blobToPolynomial blob poly hblob]
    decide
  refine ⟨cellsOfExtendedEvaluations (extendedEvaluations (polynomialEvalToCoeff poly)),
    ?_, size_cellsOfExtendedEvaluations _, fun cellIndex coset hcoset =>
      getElem!_cellsOfExtendedEvaluations_extendedEvaluations hp_le hcoset⟩
  unfold computeCells
  rw [ite_eq_right (not_not.mpr hbsize)]
  change (ExceptT.mk (pure (blobToPolynomial blob)) >>= fun polynomial =>
    pure (cellsOfExtendedEvaluations (extendedEvaluations (polynomialEvalToCoeff polynomial)))) = _
  rw [hblob]
  -- Read the successful lift as a pure `KzgM` value before applying its bind law.
  change (pure poly >>= fun polynomial =>
    pure (cellsOfExtendedEvaluations (extendedEvaluations (polynomialEvalToCoeff polynomial)))) = _
  simp only [pure_bind]

end EthLib.Cryptography.Kzg
