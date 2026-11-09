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

Give each point the scalar that it represents, as a function of its bytes.

Then a batch of valid openings has a zero error polynomial.

Conversely, let the batch check return a verdict, with a zero error polynomial.

Then every entry is valid.

The batch check of cells accepts every batch of valid openings.

So the batch check accepts the cells and proofs of blobs, and so does the verifier of the games.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (array_mapM_ok array_mapM_exists_ok)
open EthLib.Cryptography.Bls (G1 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr Polynomial

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

/-! ## Valid openings and the error polynomial -/

/-- **A batch of valid openings has a zero error polynomial.**

Take a batch with one commitment, one cell index, one cell and one proof per entry.

Let each entry be a valid opening at `τ`.

Then the error polynomial of the batch is zero, where each point has the scalar of its bytes. -/
theorem errorPoly_eq_zero_of_cellOpeningValid {τ : Fr} {y : CellBatchInput}
    (h₁ : y.cells.size = y.commitments.size) (h₃ : y.cellIndices.size = y.commitments.size)
    (hv : ∀ k < y.commitments.size,
      CellOpeningValid τ y.commitments[k]! y.cellIndices[k]! y.cells[k]! y.proofs[k]!) :
    y.toCellBatch.errorPoly τ scalarOf scalarOf = 0 := by
  obtain ⟨evals, hev⟩ := array_mapM_exists_ok (f := cellToCosetEvals) (xs := y.cells)
    fun x hx => by
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hx
      obtain ⟨-, e, -, -, -, -, he, -⟩ := hv k (h₁ ▸ hk)
      exact ⟨e, by rw [← getElem!_pos _ k hk]; exact he⟩
  obtain ⟨hesz, hevk⟩ := array_mapM_ok hev
  obtain ⟨-, hdidx, -⟩ := dedupCommitments_spec y.commitments
  refine (cellErrorPoly_eq_zero_iff τ _ _ _ _ _).mpr fun k hk => ?_
  have hk' : k < y.commitments.size := h₃ ▸ hk
  obtain ⟨-, e, C, a, W, w, he, hCv, hCr, hWv, hWr, hval⟩ := hv k hk'
  have hkc : k < y.cells.size := h₁ ▸ hk'
  have hke : k < evals.size := by omega
  have hek : evals[k]! = e := by
    rw [getElem!_pos evals k hke]
    rw [getElem!_pos y.cells k hkc] at he
    exact Except.ok.inj ((hevk k hkc hke).symm.trans he)
  simp only [CellBatchInput.toCellBatch, decodeCells_of_ok hev, hek, (hdidx k hk').2,
    scalarOf_eq hCv hCr, scalarOf_eq hWv hWr]
  exact hval

/-- **A batch with a zero error polynomial holds only valid openings.**

Let the batch check of cells return a verdict.

Let the error polynomial of the batch be zero, where each point has the scalar of its bytes.

Then every entry of the batch is a valid opening at `τ`. -/
theorem cellOpeningValid_of_errorPoly_eq_zero {s : TrustedSetup} {τ : Fr} {y : CellBatchInput}
    {b : Bool}
    (h : verifyCellKzgProofBatch s y.commitments y.cellIndices y.cells y.proofs = .ok b)
    (hz : y.toCellBatch.errorPoly τ scalarOf scalarOf = 0) {k : Nat}
    (hk : k < y.commitments.size) :
    CellOpeningValid τ y.commitments[k]! y.cellIndices[k]! y.cells[k]! y.proofs[k]! := by
  obtain ⟨h₁, h₂, h₃, hci, evals, hev, -⟩ := verifyCellKzgProofBatch_eq_ok h
  obtain ⟨hvc, hvp⟩ := validates_of_verifyCellKzgProofBatch h
  obtain ⟨-, hdidx, -⟩ := dedupCommitments_spec y.commitments
  obtain ⟨hesz, hevk⟩ := array_mapM_ok hev
  have hvck := hvc y.commitments[k]! (getElem!_pos y.commitments k hk ▸ Array.getElem_mem hk)
  have hvpk := hvp y.proofs[k]! (getElem!_pos y.proofs k (h₂ ▸ hk) ▸ Array.getElem_mem (h₂ ▸ hk))
  obtain ⟨C, hC⟩ := exists_validateKzgG1Point_of_validateKzgG1 hvck
  obtain ⟨P, hP⟩ := exists_validateKzgG1Point_of_validateKzgG1 hvpk
  have hv := (cellErrorPoly_eq_zero_iff τ _ _ _ _ _).mp hz k (by
    simp only [CellBatchInput.toCellBatch]
    omega)
  simp only [CellBatchInput.toCellBatch, decodeCells_of_ok hev, (hdidx k hk).2] at hv
  have hkc : k < y.cells.size := by omega
  have hke : k < evals.size := by omega
  have hevk' := hevk k hkc hke
  rw [← getElem!_pos y.cells k hkc, ← getElem!_pos evals k hke] at hevk'
  exact ⟨hci k (by omega), evals[k]!, C, _, P, _, hevk', hC,
    represents_scalarOf hvck (uncompressG1_of_validateKzgG1Point hC), hP,
    represents_scalarOf hvpk (uncompressG1_of_validateKzgG1Point hP), hv⟩

/-! ## The batch check accepts valid openings -/

/-- **On valid openings, the batch check of cells returns a verdict.**

Take a batch with one commitment, one cell index, one cell and one proof per entry.

Let each entry be a valid opening at `τ`.

Then the batch check of cells returns a verdict, with no error.

Its commitments and proofs pass KZG validation. -/
theorem exists_ok_of_cellOpeningValid {s : TrustedSetup} {τ : Fr} {y : CellBatchInput}
    (h₁ : y.cells.size = y.commitments.size) (h₂ : y.proofs.size = y.commitments.size)
    (h₃ : y.cellIndices.size = y.commitments.size)
    (hv : ∀ k < y.commitments.size,
      CellOpeningValid τ y.commitments[k]! y.cellIndices[k]! y.cells[k]! y.proofs[k]!) :
    (∃ b, verifyCellKzgProofBatch s y.commitments y.cellIndices y.cells y.proofs = .ok b) ∧
      (∀ x ∈ y.commitments, validateKzgG1 x = true) ∧ ∀ x ∈ y.proofs, validateKzgG1 x = true := by
  -- Each entry of an array of the batch is the entry of some index.
  have hmem : ∀ {α : Type} [Inhabited α] {xs : Array α}, xs.size = y.commitments.size →
      ∀ x ∈ xs, ∃ k < y.commitments.size, xs[k]! = x := fun hsz x hx => by
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hx
    exact ⟨k, hsz ▸ hk, getElem!_pos _ k hk⟩
  have hbs : ∀ x ∈ y.commitments, validateKzgG1 x = true := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := hmem rfl x hx
    obtain ⟨-, _, _, _, _, _, -, hC, -⟩ := hv k hk
    exact validateKzgG1_of_validateKzgG1Point hC
  have hps : ∀ x ∈ y.proofs, validateKzgG1 x = true := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := hmem h₂ x hx
    obtain ⟨-, _, _, _, _, _, -, -, -, hP, -⟩ := hv k hk
    exact validateKzgG1_of_validateKzgG1Point hP
  refine ⟨verifyCellKzgProofBatch_exists_ok h₁ h₂ h₃ (fun i hi => ?_) hbs hps fun x hx => ?_,
    hbs, hps⟩
  · obtain ⟨k, hk, rfl⟩ := hmem h₃ i hi
    exact (hv k hk).1
  · obtain ⟨k, hk, rfl⟩ := hmem h₁ x hx
    obtain ⟨-, e, -, -, -, -, he, -⟩ := hv k hk
    exact ⟨e, he⟩

/-- **The batch check of cells accepts valid openings.**

Assume a well-formed setup of the secret `τ`.

Take a batch with one commitment, one cell index, one cell and one proof per entry.

Let each entry be a valid opening at `τ`.

Then the batch check of cells accepts.

The commitments may repeat, as when several cells come from one blob. -/
theorem verifyCellKzgProofBatch_of_cellOpeningValid {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {bs : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {ps : Array Bytes48} (h₁ : cells.size = bs.size)
    (h₂ : ps.size = bs.size) (h₃ : cellIndices.size = bs.size)
    (hv : ∀ k < bs.size, CellOpeningValid τ bs[k]! cellIndices[k]! cells[k]! ps[k]!) :
    verifyCellKzgProofBatch s bs cellIndices cells ps = .ok true := by
  let y : CellBatchInput := ⟨bs, cellIndices, cells, ps⟩
  obtain ⟨⟨b, hb⟩, hbs, hps⟩ := exists_ok_of_cellOpeningValid (s := s) (y := y) h₁ h₂ h₃ hv
  have hz : y.toCellBatch.errorPoly τ scalarOf scalarOf = 0 :=
    errorPoly_eq_zero_of_cellOpeningValid h₁ h₃ hv
  have hroot := (verifyCellKzgProofBatch_ok_iff_root hs y
    (fun k hk _ hu => represents_scalarOf
      (hbs y.commitments[k]! (getElem!_pos y.commitments k hk ▸ Array.getElem_mem hk)) hu)
    (fun k hk _ hu => represents_scalarOf
      (hps y.proofs[k]! (getElem!_pos y.proofs k hk ▸ Array.getElem_mem hk)) hu) hb).mpr
    (by rw [hz, Polynomial.eval_zero])
  rw [hb, hroot]

/-- **The batch check of cells accepts the cells and proofs of blobs.**

Assume a well-formed setup of the secret `τ`.

Take a batch where each entry comes from a blob.

The commitment of the entry is the commitment of its blob.

The cell and the proof of the entry are those of its cell index, below 128.

Then the batch check of cells accepts. -/
theorem verifyCellKzgProofBatch_computeCellsAndKzgProofs
    {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ) {bs : Array Bytes48}
    {cellIndices : Array CellIndex} {cells : Array Cell} {ps : Array Bytes48}
    (h₁ : cells.size = bs.size) (h₂ : ps.size = bs.size) (h₃ : cellIndices.size = bs.size)
    (hblobs : ∀ k < bs.size, ∃ blob cs qs, blobToKzgCommitment s blob = .ok bs[k]! ∧
      computeCellsAndKzgProofs s blob = .ok (cs, qs) ∧ cellIndices[k]! < CELLS_PER_EXT_BLOB ∧
      cells[k]! = cs[cellIndices[k]!]! ∧ ps[k]! = qs[cellIndices[k]!]!) :
    verifyCellKzgProofBatch s bs cellIndices cells ps = .ok true := by
  refine verifyCellKzgProofBatch_of_cellOpeningValid hs h₁ h₂ h₃ fun k hk => ?_
  obtain ⟨blob, cs, qs, hC, hP, hj, hcell, hproof⟩ := hblobs k hk
  rw [hcell, hproof]
  exact cellOpeningValid_computeCellsAndKzgProofs hs hC hP hj

/-! ## One cell -/

/-- **An opening of one cell verifies exactly when it is valid.**

Assume a well-formed setup of the secret `τ`.

The verifier of the games accepts an opening for a commitment exactly when it is valid at `τ`. -/
theorem CellOpening.verifies_iff {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitment : Bytes48} {o : CellOpening} :
    o.Verifies s commitment ↔ CellOpeningValid τ commitment o.cellIndex o.cell o.proof := by
  constructor
  · intro h
    obtain ⟨hci, e, C, c, P, w, he, hC, hc, hP, hw, hval⟩ := h.valid hs
    obtain ⟨hvc, hvp⟩ := validateKzgG1_of_verifyCellKzgProofBatch h
    obtain ⟨C', hC'⟩ := exists_validateKzgG1Point_of_validateKzgG1 hvc
    obtain ⟨P', hP'⟩ := exists_validateKzgG1Point_of_validateKzgG1 hvp
    have hCC : C' = C := Except.ok.inj ((uncompressG1_of_validateKzgG1Point hC').symm.trans hC)
    have hPP : P' = P := Except.ok.inj ((uncompressG1_of_validateKzgG1Point hP').symm.trans hP)
    subst hCC hPP
    exact ⟨hci, e, C', c, P', w, he, hC', hc, hP', hw, hval⟩
  · intro h
    refine verifyCellKzgProofBatch_of_cellOpeningValid hs rfl rfl rfl fun k hk => ?_
    obtain rfl : k = 0 := by simpa using hk
    exact h

/-- **The verifier of the games accepts the cells and proofs of a blob.**

Take the setup of the games for the secret `τ`.

Let the code compute the commitment of a blob, and its cells and proofs, with this setup.

Then the opening of cell `j` by cell `j` and proof `j` verifies, for every `j` below 128. -/
theorem CellOpening.verifies_computeCellsAndKzgProofs (τ : Fr)
    {blob : Blob} {commitment : Bytes48} {cells : Array Cell} {proofs : Array Bytes48}
    (hC : blobToKzgCommitment (TrustedSetup.ofPowers (setupPowers τ)) blob = .ok commitment)
    (hP : computeCellsAndKzgProofs (TrustedSetup.ofPowers (setupPowers τ)) blob =
      .ok (cells, proofs)) {j : Nat} (hj : j < CELLS_PER_EXT_BLOB) :
    (⟨j, cells[j]!, proofs[j]!⟩ : CellOpening).Verifies (TrustedSetup.ofPowers (setupPowers τ))
      commitment :=
  (CellOpening.verifies_iff (wellFormed_ofPowers τ)).mpr
    (cellOpeningValid_computeCellsAndKzgProofs (wellFormed_ofPowers τ) hC hP hj)

end EthLib.Cryptography.Kzg
