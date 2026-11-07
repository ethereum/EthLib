module

public import EthLib.Cryptography.Proofs.Kzg.RecoveryMasked
public import EthLib.Cryptography.Proofs.Kzg.CoefficientPadding
public import EthLib.Cryptography.Proofs.Kzg.ExtendedFft
public import EthLib.Cryptography.Proofs.Kzg.RecoveryCapacity
public import EthLib.Cryptography.Proofs.Bls.FrBatchInverse

/-!
# Proofs: recovery returns the source polynomial

This file is the end point of the recovery proofs.

Take at least 64 distinct cells that match a polynomial `P` with 4096 coefficients.

Then recovery returns `P`.

- The cells are flattened, with zeros for the missing cells, into `E`.
- On the 8192-point domain, `E * Z` equals `P * Z`.
- The inverse FFT gives the coefficients of `P * Z`.
- A coset FFT, a pointwise division by `Z` and an inverse coset FFT give `P`.
- The result is truncated to 4096 coefficients.
-/


@[expose] public section

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr

private theorem array_ext_bang {a b : Array Fr} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  apply Array.ext hs
  intro i hi hj
  exact (getElem!_pos a i hi).symm.trans ((h i hi).trans (getElem!_pos b i hj))

private theorem getElem!_ofFn_fr (n : Nat) (f : Fin n → Fr) (i : Nat) (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by rw [Array.size_ofFn]; exact hi)]
  exact Array.getElem_ofFn _

/-- The exact evaluation-form numerator used by recovery. -/
def recoveryNumerator (indices : Array CellIndex) (cells : Array CosetEvals) (z : PolynomialCoeff) : Array Fr :=
  Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
    (fftField z (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))[i.val]! *
      (bitReversalPermutation (recoveryFlatten indices cells))[i.val]!

/-- The actual masked numerator is the FFT of the bounded product polynomial. -/
theorem recoveryNumerator_eq_fft
    {p z q : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hmatch : RecoverySamplesMatch p indices cells)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    recoveryNumerator indices cells z = fftField q (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false := by
  apply array_ext_bang
  · simp only [recoveryNumerator, Array.size_ofFn, size_fftField, hqsize]
  · intro i hi
    have hiN : i < FIELD_ELEMENTS_PER_EXT_BLOB := by simpa only [recoveryNumerator, Array.size_ofFn] using hi
    rw [getElem!_fftField_extended q hqsize i hiN, hqeval]
    unfold recoveryNumerator
    rw [getElem!_ofFn_fr _ _ i hiN,
      getElem!_fftField_extended z (size_constructVanishingPolynomial hz) i hiN]
    exact recovery_masked_product hz hmatch i hiN

/-- Inverse FFT of the actual masked numerator yields the bounded product coefficients. -/
theorem recoveryNumerator_inverse
    {p z q : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hmatch : RecoverySamplesMatch p indices cells)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    fftField (recoveryNumerator indices cells z)
      (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true = q := by
  rw [recoveryNumerator_eq_fft hz hmatch hqsize hqeval]
  exact fftField_extended_roundtrip q hqsize

/-- The exact shifted pointwise quotient used by recovery. -/
def recoveryQuotient (q z : PolynomialCoeff) : Array Fr :=
  Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
    (cosetFftField q (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))[i.val]! /
      (cosetFftField z (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))[i.val]!

private theorem field_mul_div_cancel {F : Type*} [Field F] (a b : F) (hb : b ≠ 0) :
    a * b / b = a := mul_div_cancel_right₀ a hb

/-- Nonzero shifted denominators make the actual quotient the coset FFT of the padded source. -/
theorem recoveryQuotient_eq_cosetFft
    {p z q : PolynomialCoeff} {indices : Array CellIndex}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    recoveryQuotient q z =
      cosetFftField (padCoefficients FIELD_ELEMENTS_PER_EXT_BLOB p)
        (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false := by
  apply array_ext_bang
  · simp only [recoveryQuotient, Array.size_ofFn, size_cosetFftField, size_padCoefficients]
  · intro i hi
    have hiN : i < FIELD_ELEMENTS_PER_EXT_BLOB := by simpa only [recoveryQuotient, Array.size_ofFn] using hi
    rw [getElem!_cosetFftField_extended _ (size_padCoefficients _ _) i hiN,
      evalPolyAt_padCoefficients _ p (by rw [hp]; decide)]
    unfold recoveryQuotient
    rw [getElem!_ofFn_fr _ _ i hiN,
      getElem!_cosetFftField_extended q hqsize i hiN,
      getElem!_cosetFftField_extended z (size_constructVanishingPolynomial hz) i hiN, hqeval]
    exact field_mul_div_cancel _ _ (constructVanishingPolynomial_recoveryCoset_ne_zero hz i)

/-- After exact numerator reconstruction, inverse coset FFT and truncation recover the source. -/
theorem recoveryQuotient_inverse_extract
    {p z q : PolynomialCoeff} {indices : Array CellIndex}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    (cosetFftField (recoveryQuotient q z) (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true).extract
      0 FIELD_ELEMENTS_PER_BLOB = p := by
  rw [recoveryQuotient_eq_cosetFft hz hp hqsize hqeval,
    cosetFftField_extended_roundtrip _ (size_padCoefficients _ _), ← hp]
  exact extract_padCoefficients _ p (by rw [hp]; decide)

/-- Multiplying by batch inverses is dividing, entry by entry. -/
private theorem ofFn_mul_batchInverse (a b : Array Fr) (n : Nat) (hb : b.size = n) :
    (Array.ofFn (n := n) fun i => a[i.val]! * (Fr.batchInverse b)[i.val]!) =
      Array.ofFn (n := n) fun i => a[i.val]! / b[i.val]! := by
  congr 1
  funext i
  have hi : i.val < b.size := hb ▸ i.isLt
  rw [Fr.batchInverse_eq_map, getElem!_pos (b.map Fr.inverse) i.val (by simpa using hi), Array.getElem_map,
    ← getElem!_pos b i.val hi]
  rfl

/-- Writing a cell with an index of 128 or more leaves the flattened array unchanged. -/
private theorem writeRecoveryCell_of_le (acc : Array Fr) (ci : CellIndex) (cell : CosetEvals)
    (hacc : acc.size = FIELD_ELEMENTS_PER_EXT_BLOB) (hci : CELLS_PER_EXT_BLOB ≤ ci) :
    writeRecoveryCell acc ci cell = acc := by
  unfold writeRecoveryCell
  refine Array.foldl_induction (motive := fun _ a => a = acc) rfl (fun j a ha => ?_)
  subst ha
  have hc : FIELD_ELEMENTS_PER_CELL = 64 := rfl
  have hb : CELLS_PER_EXT_BLOB = 128 := rfl
  apply Array.setIfInBounds_eq_of_size_le
  have h1 : FIELD_ELEMENTS_PER_EXT_BLOB ≤ ci * FIELD_ELEMENTS_PER_CELL := by
    rw [hc, show FIELD_ELEMENTS_PER_EXT_BLOB = 8192 from rfl]
    rw [hb] at hci
    omega
  rw [hacc]
  exact Nat.le_add_right_of_le h1

/-- One cell of the flattening, written on a vector, is the write of the proofs. -/
private theorem toArray_foldl_cell (acc : Vector Fr FIELD_ELEMENTS_PER_EXT_BLOB) (ci : CellIndex)
    (cell : CosetEvals) (hci : ci < CELLS_PER_EXT_BLOB) :
    ((Array.finRange FIELD_ELEMENTS_PER_CELL).foldl (init := acc) fun acc j =>
      acc.set (ci * FIELD_ELEMENTS_PER_CELL + j.val)
        (if hj : j.val < cell.size then cell[j.val] else Fr.zero)
        (cell_slot_lt hci j.isLt)).toArray =
      writeRecoveryCell acc.toArray ci cell := by
  rw [← Array.foldl_hom Vector.toArray
    (g₂ := fun a (j : Fin FIELD_ELEMENTS_PER_CELL) =>
      a.set! (ci * FIELD_ELEMENTS_PER_CELL + j.val) cell[j.val]!)]
  · unfold writeRecoveryCell
    refine (foldl_finRange_eq_foldl_range _
      (fun (a : Array Fr) (j : Nat) => a.set! (ci * FIELD_ELEMENTS_PER_CELL + j) cell[j]!)
      (fun _ _ => rfl) _).trans ?_
    rw [← Array.foldl_toList, Array.toList_range]
  · intro x j
    rw [Vector.toArray_set, Array.set!_eq_setIfInBounds,
      Array.setIfInBounds_def,
      dite_eq_left (by rw [Vector.size_toArray]; exact cell_slot_lt hci j.isLt)]
    congr 1

/-- The flattening of the specification is the flattening of the proofs. -/
private theorem toArray_foldl_flatten (indices : Array CellIndex) (cells : Array CosetEvals)
    (hlen : cells.size = indices.size) :
    ((indices.zip cells).foldl (init := Vector.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
      fun acc (ci, cell) =>
        if hci : ci < CELLS_PER_EXT_BLOB then
          (Array.finRange FIELD_ELEMENTS_PER_CELL).foldl (init := acc) fun acc j =>
            acc.set (ci * FIELD_ELEMENTS_PER_CELL + j.val)
              (if hj : j.val < cell.size then cell[j.val] else Fr.zero) (cell_slot_lt hci j.isLt)
        else acc).toArray =
      recoveryFlatten indices cells := by
  have hzip : indices.zip cells =
      (Array.range indices.size).map fun k => (indices[k]!, cells[k]!) := by
    apply Array.ext (by simp [hlen])
    intro k h1 h2
    simp only [Array.size_zip, hlen, Nat.min_self] at h1
    simp [getElem!_pos indices k h1, getElem!_pos cells k (by omega)]
  rw [← Array.foldl_hom Vector.toArray
    (g₂ := fun a (p : CellIndex × CosetEvals) => writeRecoveryCell a p.1 p.2)]
  · rw [hzip, Array.foldl_map]
    rfl
  · rintro x ⟨ci, cell⟩
    dsimp only
    split
    · rename_i hci
      exact (toArray_foldl_cell x ci cell hci).symm
    · rename_i hci
      exact writeRecoveryCell_of_le _ _ _ (by simp) (Nat.le_of_not_lt hci)

/-- A pointwise product of two arrays of length `n` is the product read entry by entry. -/
private theorem zipWith_mul_eq_ofFn (a b : Array Fr) (n : Nat) (ha : a.size = n)
    (hb : b.size = n) :
    Array.zipWith (· * ·) a b = Array.ofFn (n := n) fun i => a[i.val]! * b[i.val]! := by
  apply Array.ext (by simp [ha, hb])
  intro i h1 h2
  simp only [Array.size_zipWith, ha, hb, Nat.min_self] at h1
  rw [Array.getElem_zipWith, Array.getElem_ofFn, getElem!_pos a i (by omega),
    getElem!_pos b i (by omega)]

/-- Unfolding the actual implementation yields exactly the verified numerator/quotient pipeline. -/
theorem recoverPolynomialcoeff_eq_pipeline
    {indices : Array CellIndex} {cells : Array CosetEvals} {z : PolynomialCoeff}
    (hlen : cells.size = indices.size)
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z) :
    recoverPolynomialcoeff indices cells = .ok
      ((cosetFftField
        (recoveryQuotient
          (fftField (recoveryNumerator indices cells z)
            (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true) z)
        (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true).extract 0 FIELD_ELEMENTS_PER_BLOB) := by
  have hzs := size_constructVanishingPolynomial hz
  unfold recoveryMissing at hz
  unfold recoverPolynomialcoeff
  rw [ite_eq_right (by omega : ¬ cells.size ≠ indices.size)]
  simp only [Bind.bind, Except.bind, hz, pure, Except.pure]
  rw [toArray_foldl_flatten indices cells hlen,
    zipWith_mul_eq_ofFn (fftField z (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))
      (bitReversalPermutation (recoveryFlatten indices cells)) FIELD_ELEMENTS_PER_EXT_BLOB
      (by rw [size_fftField, hzs]) (by rw [size_bitReversalPermutation, size_recoveryFlatten]),
    zipWith_mul_eq_ofFn _ (Fr.batchInverse (cosetFftField z (computeRootsOfUnity _)))
      FIELD_ELEMENTS_PER_EXT_BLOB (by simp)
      (by rw [Fr.batchInverse_eq_map, Array.size_map, size_cosetFftField, hzs])]
  unfold recoveryQuotient recoveryNumerator
  rw [ofFn_mul_batchInverse _ _ _ (by rw [size_cosetFftField, hzs])]

/-- Exact executable recovery correctness.

Take consistent samples with at most half the cells missing.

They reconstruct the original 4096-coefficient polynomial.

All FFT/product/division properties are proved above.

The hypotheses specify only the supplied data. -/
theorem recoverPolynomialcoeff_correct
    {p : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hlen : cells.size = indices.size)
    (hmissing : (recoveryMissing indices).size ≤ CELLS_PER_EXT_BLOB / 2)
    (hmatch : RecoverySamplesMatch p indices cells) :
    recoverPolynomialcoeff indices cells = .ok p := by
  have hlt : (recoveryMissing indices).size < CELLS_PER_EXT_BLOB :=
    lt_of_le_of_lt hmissing (by decide)
  obtain ⟨z, hz, _, _⟩ := constructVanishingPolynomial_ok_of_lt hlt
  obtain ⟨q, hqsize, hqeval⟩ := exists_recovery_product hz hmissing hp
  rw [recoverPolynomialcoeff_eq_pipeline hlen hz,
    recoveryNumerator_inverse hz hmatch hqsize hqeval,
    recoveryQuotient_inverse_extract hz hp hqsize hqeval]

/-- Recovery for the ordinary valid-input contract: at least 64 distinct in-range cells. -/
theorem recoverPolynomialcoeff_correct_of_valid_indices
    {p : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hlen : cells.size = indices.size)
    (hnd : indices.toList.Nodup)
    (hbound : ∀ ci ∈ indices.toList, ci < CELLS_PER_EXT_BLOB)
    (hhalf : CELLS_PER_EXT_BLOB / 2 ≤ indices.size)
    (hmatch : RecoverySamplesMatch p indices cells) :
    recoverPolynomialcoeff indices cells = .ok p :=
  recoverPolynomialcoeff_correct hp hlen
    (recoveryMissing_size_le_half indices hnd hbound hhalf) hmatch

/-- Produce the selected input cells by evaluating the original coefficient polynomial. -/
def polynomialRecoverySamples (p : PolynomialCoeff) (indices : Array CellIndex) : Array CosetEvals :=
  indices.map fun ci => Array.ofFn fun j : Fin FIELD_ELEMENTS_PER_CELL =>
    evalPolyAt p (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^
      reverseBits (ci * FIELD_ELEMENTS_PER_CELL + j.val) FIELD_ELEMENTS_PER_EXT_BLOB)

theorem polynomialRecoverySamples_match (p : PolynomialCoeff) (indices : Array CellIndex) :
    RecoverySamplesMatch p indices (polynomialRecoverySamples p indices) := by
  intro k hk j hj
  unfold polynomialRecoverySamples
  rw [getElem!_pos _ k (by simpa only [Array.size_map] using hk), Array.getElem_map,
    getElem!_ofFn_fr _ _ j hj, getElem!_pos indices k hk]

/-- Sample any at-least-half subset of the valid cells, and execute recovery.

The result is exactly the original bounded-degree polynomial coefficient vector. -/
theorem recoverPolynomialcoeff_samples_correct
    (p : PolynomialCoeff) (indices : Array CellIndex)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hnd : indices.toList.Nodup)
    (hbound : ∀ ci ∈ indices.toList, ci < CELLS_PER_EXT_BLOB)
    (hhalf : CELLS_PER_EXT_BLOB / 2 ≤ indices.size) :
    recoverPolynomialcoeff indices (polynomialRecoverySamples p indices) = .ok p :=
  recoverPolynomialcoeff_correct_of_valid_indices hp
    (Array.size_map) hnd hbound hhalf (polynomialRecoverySamples_match p indices)

end EthLib.Cryptography.Kzg
