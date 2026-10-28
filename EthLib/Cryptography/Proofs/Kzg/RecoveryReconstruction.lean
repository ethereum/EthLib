import EthLib.Cryptography.Proofs.Kzg.RecoveryMasked
import EthLib.Cryptography.Proofs.Kzg.CoefficientPadding
import EthLib.Cryptography.Proofs.Kzg.ExtendedFft
import EthLib.Cryptography.Proofs.Kzg.RecoveryCapacity
import EthLib.Cryptography.Proofs.Bls.FrBatchInverse

/-!
# Proofs: recovery returns the source polynomial

The endpoint of the recovery proofs.

Given at least 64 distinct cells that match a polynomial with 4096 coefficients, recovery returns that polynomial.

```text
    cells (at least 64 of 128)
      |  flatten, with zeros for missing cells
      v
    E * Z on the 8192-point domain       (equals P * Z there)
      |  inverse FFT
      v
    coefficients of P * Z
      |  coset FFT, divide by Z pointwise, inverse coset FFT
      v
    coefficients of P, truncated to 4096
```
-/


namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

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
  unfold recoveryQuotient recoveryNumerator recoveryFlatten writeRecoveryCell
  unfold recoveryMissing at hz
  unfold recoverPolynomialcoeff
  rw [ite_eq_right (by omega : ¬ cells.size ≠ indices.size)]
  simp only [Bind.bind, Except.bind, hz, pure, Except.pure]
  rw [ofFn_mul_batchInverse _ _ _ (by rw [size_cosetFftField, size_constructVanishingPolynomial hz])]

/-- Exact executable recovery correctness: consistent samples with at most half the cells
missing reconstruct the original 4096-coefficient polynomial. All FFT/product/division
properties are proved above; the hypotheses specify only the supplied data. -/
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

/-- Sampling any at-least-half subset of the valid cells and executing recovery returns
exactly the original bounded-degree polynomial coefficient vector. -/
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
