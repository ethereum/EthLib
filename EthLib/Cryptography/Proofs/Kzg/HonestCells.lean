module

public import EthLib.Cryptography.Proofs.Kzg.PeerDasCodeword
public import EthLib.Cryptography.Proofs.Kzg.Fk20Proofs
public import EthLib.Cryptography.Proofs.Kzg.Verify

/-!
# Proofs: the cells and proofs of a blob are valid openings

A cell of index `j` holds values `e` on its coset, with shift `h`.

Its opening for a commitment is valid at the secret `τ` when three conditions hold.

- The commitment and the proof decode to points that represent scalars `c` and `w`.
- The cell decodes to the values `e`.
- Let `I` interpolate `e` on the coset; then `c - I(τ) = w (τ^64 - h^64)`.

This file shows that the cells and proofs that the code computes for a blob are valid openings.

The setup is any well-formed setup of `τ`, so the setup of the PeerDAS games is one of them.

- The commitment represents `f(τ)`, for the polynomial `f` of the blob.
- The proof of cell `j` represents `q(τ)`, where `q` is the quotient of `f` by `X^64 - h^64`.
- The remainder of that division takes the values of the cell on its coset.
  It has degree below 64, so it is the polynomial that interpolates the cell.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr Polynomial

-- Core's power instance on `Fin` hides Mathlib's power on `Fr`, as in `Proofs.Bls.FrZMod`.
attribute [-instance] Fin.instNatPow

/-- **A valid opening of one cell, at the secret `τ`.**

The cell index is below 128, and the cell decodes to values `e`.

The commitment and the proof pass KZG validation, as points that represent `c` and `w`.

Let `I` interpolate `e` on the coset of the cell, with shift `h`.

Then `c - I(τ) = w (τ^64 - h^64)`. -/
def CellOpeningValid (τ : Fr) (commitment : Bytes48) (cellIndex : CellIndex) (cell : Cell)
    (proof : Bytes48) : Prop :=
  cellIndex < CELLS_PER_EXT_BLOB ∧ ∃ e C c P w, cellToCosetEvals cell = .ok e ∧
    validateKzgG1Point commitment = .ok C ∧ G1.Represents C c ∧
    validateKzgG1Point proof = .ok P ∧ G1.Represents P w ∧
    c - (cellInterpolant cellIndex e).eval τ =
      w * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL)

/-- The sum of the first monomial points times coefficients represents their polynomial at `τ`.

The coefficients are at most 4096, the number of monomial points. -/
theorem represents_msm_monomial {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {q : PolynomialCoeff} (hq : q.size ≤ FIELD_ELEMENTS_PER_BLOB) :
    G1.Represents (G1.msm (s.g1Monomial.toArray.extract 0 q.size) q)
      ((coefficientPolynomial q).eval τ) := by
  have hsz : (s.g1Monomial.toArray.extract 0 q.size).size = q.size := by
    rw [Array.size_extract, Vector.size_toArray, Nat.min_eq_left hq, Nat.sub_zero]
  have h := G1.represents_msm (scalars := q) (a := fun j => τ ^ j) hsz fun j hj => by
    have hj' : j < q.size := hsz ▸ hj
    rw [getElem!_pos _ j hj, Array.getElem_extract]
    simpa using hs.monomial_g1 ⟨j, Nat.lt_of_lt_of_le hj' hq⟩
  rw [hsz] at h
  rwa [eval_coefficientPolynomial, evalPolyAt_eq_sum]

/-- The values of a polynomial on the coset of a cell. -/
noncomputable def cellValues (f : Fr[X]) (cellIndex : Nat) : CosetEvals :=
  Array.ofFn fun m : Fin FIELD_ELEMENTS_PER_CELL => f.eval (cellPoint cellIndex m)

/-- A symbol of the codeword decodes to the values of its polynomial on the coset. -/
theorem cellToCosetEvals_codewordCell (f : Fr[X]) (cellIndex : Nat) :
    cellToCosetEvals (codewordCell f cellIndex) = .ok (cellValues f cellIndex) :=
  cellToCosetEvals_cosetEvalsToCell _ (Array.size_ofFn)

/-- A remainder where the divisor vanishes is the dividend. -/
private theorem eq_of_eq_mul_sub_self_add {R : Type} [CommRing R] {a q r t : R}
    (h : a = q * (t - t) + r) : r = a := by
  rw [h, sub_self, mul_zero, zero_add]

/-- The division identity, with the divisor replaced by its value. -/
private theorem sub_eq_mul_of_eq_mul_add {R : Type} [CommRing R] {a q r d t : R}
    (h : a = q * d + r) (hd : d = t) : a - r = q * t := by
  rw [h, hd, add_sub_cancel_right]

/-- **The division identity of an honest cell proof.**

Let `f` be the polynomial of `a`, and let the division of `a` by `X^64 - h^64` return `q`.

Here `h` is the shift of a cell below 128.

Then `f(τ) - I(τ) = q(τ) (τ^64 - h^64)`, where `I` interpolates `f` on the coset of the cell. -/
theorem eval_sub_cellInterpolant {a q : PolynomialCoeff} {cellIndex : Nat}
    (hci : cellIndex < CELLS_PER_EXT_BLOB)
    (hdiv : dividePolynomialcoeff a (binomialVanishing FIELD_ELEMENTS_PER_CELL
      (cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL)) = .ok q) (τ : Fr) :
    (coefficientPolynomial a).eval τ -
        (cellInterpolant cellIndex (cellValues (coefficientPolynomial a) cellIndex)).eval τ =
      (coefficientPolynomial q).eval τ *
        (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL) := by
  set b := binomialVanishing FIELD_ELEMENTS_PER_CELL
    (cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL)
  have hn : 0 < FIELD_ELEMENTS_PER_CELL := by decide
  have hbsz : b.size = FIELD_ELEMENTS_PER_CELL + 1 := size_binomialVanishing _ _
  have hlead : b[b.size - 1]! ≠ 0 := by
    rw [hbsz, Nat.add_sub_cancel, getElem!_binomialVanishing _ _ _ (by omega),
      ite_eq_right (Nat.ne_of_gt hn), ite_eq_left rfl]
    decide
  obtain ⟨r, hid, hhigh⟩ := dividePolynomialcoeff_quotient_remainder_spec (by omega) hlead hdiv
  have hb : ∀ x, evalPolyAt b x = x ^ FIELD_ELEMENTS_PER_CELL -
      cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL := evalPolyAt_binomialVanishing hn _
  -- The remainder has degree below 64.
  have hrdeg : (coefficientPolynomial r).degree < (Finset.range FIELD_ELEMENTS_PER_CELL).card := by
    rw [Finset.card_range, Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_coefficientPolynomial]
    exact hhigh m (by rw [hbsz]; omega)
  -- On the coset, the remainder takes the values of `f`, since `X^64 - h^64` vanishes there.
  have hrI : coefficientPolynomial r =
      cellInterpolant cellIndex (cellValues (coefficientPolynomial a) cellIndex) := by
    refine Lagrange.eq_interpolate_of_eval_eq _ (cellPoint_injOn hci) hrdeg fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    have hx := hid (cellPoint cellIndex m)
    rw [hb, cellPoint_pow hci hm'] at hx
    rw [cellValues, getElem!_pos _ m (by simpa using hm'), Array.getElem_ofFn,
      eval_coefficientPolynomial, eval_coefficientPolynomial]
    exact eq_of_eq_mul_sub_self_add hx
  rw [← hrI, eval_coefficientPolynomial, eval_coefficientPolynomial, eval_coefficientPolynomial]
  exact sub_eq_mul_of_eq_mul_add (hid τ) (hb τ)

/-- A point that represents a scalar has order dividing `r`. -/
theorem modulus_smul_of_represents {P : G1} {a : Fr} (h : G1.Represents P a) :
    Fr.modulus • G1.toPoint P = 0 := by
  rw [h.2, G1.toPoint_mul_generator, G1.ofFr, ← mul_nsmul', mul_nsmul,
    G1.modulus_smul_generator, nsmul_zero]

/-- The commitment to a blob represents the value of the polynomial of the blob at `τ`. -/
theorem represents_blobCommitment {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {blob : Blob} {poly : Kzg.Polynomial} (hblob : blobToPolynomial blob = .ok poly) :
    G1.Represents (G1.msm s.g1LagrangeBrp.toArray poly) ((blobPolynomial poly).eval τ) := by
  have h := represents_lagrange_msm hs (τ := τ) (size_blobToPolynomial blob poly hblob)
  rwa [interpolant_eq_of_eval (natDegree_blobPolynomial_lt hblob)
    fun i => (eval_blobPolynomial hblob i).symm] at h

/-- **The cells and proofs of a blob are valid openings for its commitment.**

Take any well-formed setup of the secret `τ`, and a blob.

Let the code compute the commitment of the blob, and its cells and proofs.

Then cell `j` and proof `j` are a valid opening of cell index `j`, for every `j` below 128. -/
theorem cellOpeningValid_computeCellsAndKzgProofs {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {blob : Blob} {commitment : Bytes48} {cells : Array Cell}
    {proofs : Array Bytes48} (hC : blobToKzgCommitment s blob = .ok commitment)
    (hP : computeCellsAndKzgProofs s blob = .ok (cells, proofs)) {j : Nat}
    (hj : j < CELLS_PER_EXT_BLOB) :
    CellOpeningValid τ commitment j cells[j]! proofs[j]! := by
  cases hblob : blobToPolynomial blob with
  | error e =>
    rw [computeCellsAndKzgProofs, hblob] at hP
    cases hP
  | ok poly =>
    rw [blobToKzgCommitment_eq_ok s hblob] at hC
    obtain rfl := Except.ok.inj hC
    rw [computeCellsAndKzgProofs_ok_eq s hblob] at hP
    set fc := polynomialEvalToCoeff poly
    have hfc : fc.size = FIELD_ELEMENTS_PER_BLOB := by
      rw [size_polynomialEvalToCoeff, size_blobToPolynomial blob poly hblob]
    obtain ⟨coset, hcoset, -, -⟩ := cosetForCell_ok_of_lt hj
    obtain ⟨V, q, hV, hdiv, -, -, hproof⟩ := computeCellsAndKzgProofs_blob_spec hblob hs.valid
      (fun t ht => modulus_smul_of_represents (a := τ ^ t) (by
        have hm := hs.monomial_g1 ⟨t, by omega⟩
        rw [getElem!_pos _ t (by rw [Vector.size_toArray]; omega), Vector.getElem_toArray]
        exact hm)) hcoset
    rw [vanishingPolynomialcoeff_cosetForCell hcoset] at hV
    obtain rfl := Except.ok.inj hV
    have hq : q = toeplitzQuotient fc FIELD_ELEMENTS_PER_CELL
        (cellShift j ^ FIELD_ELEMENTS_PER_CELL) :=
      Except.ok.inj (hdiv.symm.trans (dividePolynomialcoeff_binomialVanishing (by decide)
        (hfc ▸ by decide) _))
    have hqsz : q.size ≤ FIELD_ELEMENTS_PER_BLOB := by
      rw [hq, size_toeplitzQuotient, hfc]
      omega
    -- The cells are those of the cell computation, so they form the codeword.
    have hcc : computeCells blob = .ok (fk20CellsAndProofs s fc).1 := by
      unfold computeCells
      rw [hblob]
      rfl
    rw [computeCells_eq_codewordCell hblob] at hcc
    have hcs : (fk20CellsAndProofs s fc).1 = cells := congrArg Prod.fst (Except.ok.inj hP)
    have hps : (fk20CellsAndProofs s fc).2 = proofs := congrArg Prod.snd (Except.ok.inj hP)
    subst hcs hps
    have hcell : (fk20CellsAndProofs s fc).1[j]! = codewordCell (blobPolynomial poly) j := by
      rw [← Except.ok.inj hcc, getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj),
        Array.getElem_ofFn]
    obtain ⟨C, hCv, hCr⟩ := validateKzgG1Point_compressG1 (represents_blobCommitment hs hblob)
    obtain ⟨P, hPv, hPr⟩ := validateKzgG1Point_compressG1 (represents_msm_monomial hs hqsz)
    refine ⟨hj, cellValues (blobPolynomial poly) j, C, _, P, _, ?_, hCv, hCr, ?_, hPr,
      eval_sub_cellInterpolant hj hdiv τ⟩
    · rw [hcell]
      exact cellToCosetEvals_codewordCell _ _
    · rw [hproof]
      exact hPv

end EthLib.Cryptography.Kzg
