module

public import EthLib.Cryptography.Proofs.Kzg.Fk20Proofs

/-!
# Proofs: recovery from computed cells

Compute the cells and proofs of a polynomial given by 4096 coefficients.

Keep at least half of the cells, in strictly ascending order of their indices.

Then recovery from the kept cells returns every cell and every proof.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

/-- The values of a polynomial on the coset of a cell, read from its extended evaluations. -/
def computedCosetEvals (p : PolynomialCoeff) (cellIndex : CellIndex) : CosetEvals :=
  (extendedEvaluations p).extract (cellIndex * FIELD_ELEMENTS_PER_CELL)
    ((cellIndex + 1) * FIELD_ELEMENTS_PER_CELL)

private theorem size_computedCosetEvals {p : PolynomialCoeff} {cellIndex : CellIndex}
    (hp : p.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) (hci : cellIndex < CELLS_PER_EXT_BLOB) :
    (computedCosetEvals p cellIndex).size = FIELD_ELEMENTS_PER_CELL := by
  have hstop : (cellIndex + 1) * FIELD_ELEMENTS_PER_CELL ≤ FIELD_ELEMENTS_PER_EXT_BLOB :=
    Nat.mul_le_mul_right FIELD_ELEMENTS_PER_CELL (Nat.succ_le_of_lt hci)
  unfold computedCosetEvals
  rw [Array.size_extract, size_extendedEvaluations p hp, Nat.min_eq_left hstop, Nat.succ_mul]
  omega

/-- Each computed cell decodes to the values of the polynomial on its coset. -/
theorem cellToCosetEvals_fk20Cell (setup : TrustedSetup) {p : PolynomialCoeff}
    {cellIndex : CellIndex} (hp : p.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB)
    (hci : cellIndex < CELLS_PER_EXT_BLOB) :
    cellToCosetEvals (fk20CellsAndProofs setup p).1[cellIndex]! =
      .ok (computedCosetEvals p cellIndex) := by
  have hcell : (fk20CellsAndProofs setup p).1[cellIndex]! =
      cosetEvalsToCell (computedCosetEvals p cellIndex) := by
    change (cellsOfExtendedEvaluations (extendedEvaluations p))[cellIndex]! = _
    unfold cellsOfExtendedEvaluations
    rw [getElem!_pos _ cellIndex (by simp [hci]), Array.getElem_map, Array.getElem_range]
    rfl
  rw [hcell, cellToCosetEvals_cosetEvalsToCell _ (size_computedCosetEvals hp hci)]

/-- Entry `j` of the computed values of a cell is the polynomial at its point of the domain. -/
theorem getElem!_computedCosetEvals {p : PolynomialCoeff} {cellIndex : CellIndex} {j : Nat}
    (hp : p.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) (hci : cellIndex < CELLS_PER_EXT_BLOB)
    (hj : j < FIELD_ELEMENTS_PER_CELL) :
    (computedCosetEvals p cellIndex)[j]! = evalPolyAt p
      (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^
        reverseBits (cellIndex * FIELD_ELEMENTS_PER_CELL + j) FIELD_ELEMENTS_PER_EXT_BLOB) := by
  have hm : cellIndex * FIELD_ELEMENTS_PER_CELL + j < FIELD_ELEMENTS_PER_EXT_BLOB := by
    have : cellIndex * FIELD_ELEMENTS_PER_CELL + FIELD_ELEMENTS_PER_CELL ≤
        FIELD_ELEMENTS_PER_EXT_BLOB := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right FIELD_ELEMENTS_PER_CELL (Nat.succ_le_of_lt hci)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) this
  have hsize := size_computedCosetEvals hp hci
  rw [getElem!_pos _ j (by rw [hsize]; exact hj)]
  unfold computedCosetEvals
  rw [Array.getElem_extract, ← getElem!_pos _ _ (by rw [size_extendedEvaluations p hp]; exact hm),
    getElem!_extendedEvaluations p hp _ hm, evaluatePolynomialcoeff_eq_evalPolyAt,
    rootsOfUnityBrp, getElem!_bitReversalPermutation _ _ (by
      rw [size_computeRootsOfUnity]; exact hm),
    size_computeRootsOfUnity, getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) _
      (by rw [size_computeRootsOfUnity]; exact reverseBits_lt_two_pow _ 13),
    getElem_computeRootsOfUnity]

/-- Recovery from at least half of the computed cells returns every cell and every proof.

The kept cells come in strictly ascending order of their indices, each below 128. -/
theorem recoverCellsAndKzgProofs_fk20 (setup : TrustedSetup) {p : PolynomialCoeff}
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB) {cellIndices : Array CellIndex}
    (hmin : CELLS_PER_EXT_BLOB / 2 ≤ cellIndices.size)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hasc : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = false) :
    recoverCellsAndKzgProofs setup cellIndices
        (cellIndices.map fun i => (fk20CellsAndProofs setup p).1[i]!) =
      .ok (fk20CellsAndProofs setup p) := by
  have hle : p.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB := by rw [hp]; decide
  have hlt : ∀ i ∈ cellIndices, i < CELLS_PER_EXT_BLOB := by
    intro i hi
    by_contra hge
    have : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true :=
      Array.any_eq_true'.mpr ⟨i, hi, decide_eq_true (Nat.le_of_not_lt hge)⟩
    rw [hbound] at this
    cases this
  refine recoverCellsAndKzgProofs_ok_eq setup hp (Array.size_map ..) hmin hbound hasc
    (cosetsEvals := cellIndices.map (computedCosetEvals p)) ?_ ?_
  · rw [Array.mapM_eq_mapM_toList, Array.toList_map, List.mapM_map]
    rw [Base.mapM_eq_ok_map (f := cellToCosetEvals ∘ fun i => (fk20CellsAndProofs setup p).1[i]!)
      (g := computedCosetEvals p) fun i hi =>
        cellToCosetEvals_fk20Cell setup hle (hlt i (Array.mem_def.mpr hi))]
    simp only [Functor.map, Except.map]
    rw [← Array.toList_map, Array.toArray_toList]
  · intro k hk j hj
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map,
      getElem!_pos cellIndices k hk]
    exact getElem!_computedCosetEvals hle (hlt _ (Array.getElem_mem hk)) hj

end EthLib.Cryptography.Kzg
