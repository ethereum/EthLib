module

public import EthLib.Cryptography.Proofs.Kzg.PeerDasGames
public import EthLib.Cryptography.Proofs.Kzg.ExtendedCells
public import EthLib.Cryptography.Proofs.Kzg.CoefficientPolynomial
public import EthLib.Cryptography.Proofs.Kzg.Evaluation

/-!
# Proofs: the cells of a blob are the codeword of its polynomial

The games of position-binding and code-binding speak about a codeword.

Symbol `j` of the codeword of a polynomial `f` holds the values of `f` on the coset of cell `j`.

This file shows that the cells the code computes for a blob are that codeword.

- A blob holds 4096 values, one at each point of the blob domain.
- One polynomial of degree below 4096 takes these values: the polynomial of the blob.
- Each of the 128 cells of the blob is the symbol of the codeword of that polynomial.

So no adversary wins code-binding with cells that the code computes for one blob.

That fact is about the cells only.

The commitment and the proofs are arbitrary, so it says nothing about whether the openings verify.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr Polynomial

-- Core's power instance on `Fin` hides Mathlib's power on `Fr`, as in `Proofs.Bls.FrZMod`.
attribute [-instance] Fin.instNatPow

/-- The polynomial of the values of a blob: its coefficients are their inverse FFT. -/
noncomputable def blobPolynomial (poly : Kzg.Polynomial) : Fr[X] :=
  coefficientPolynomial (polynomialEvalToCoeff poly)

/-- The polynomial of a blob has degree below 4096. -/
theorem natDegree_blobPolynomial_lt {blob : Blob} {poly : Kzg.Polynomial}
    (h : blobToPolynomial blob = .ok poly) :
    (blobPolynomial poly).natDegree < FIELD_ELEMENTS_PER_BLOB := by
  have hsz : (polynomialEvalToCoeff poly).size = FIELD_ELEMENTS_PER_BLOB := by
    rw [size_polynomialEvalToCoeff, size_blobToPolynomial blob poly h]
  have hlt := natDegree_coefficientPolynomial_lt (p := polynomialEvalToCoeff poly)
    (by rw [hsz]; decide)
  rwa [hsz] at hlt

/-- **The polynomial of a blob takes its values.**

At point `i` of the blob domain, it takes value `i` of the decoded blob. -/
theorem eval_blobPolynomial {blob : Blob} {poly : Kzg.Polynomial}
    (h : blobToPolynomial blob = .ok poly) (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    (blobPolynomial poly).eval (evalDomain i) = poly[i.val]! := by
  have hsz : poly.size = 2 ^ 12 := size_blobToPolynomial blob poly h
  have hω :=
    isPrimitiveRoot_domainRoot (order := 2 ^ 12) field_elements_per_blob_dvd_modulus_sub_one
  have hrs : (computeRootsOfUnity (2 ^ 12)).size = 2 ^ 12 := size_computeRootsOfUnity _
  have hroots : ∀ k < 2 ^ 12, (computeRootsOfUnity (2 ^ 12))[k]! = domainRoot (2 ^ 12) ^ k :=
    fun k hk => by rw [getElem!_pos _ k (by rw [hrs]; exact hk), getElem_computeRootsOfUnity]
  have hbsz : (bitReversalPermutation poly).size = 2 ^ 12 := by
    rw [size_bitReversalPermutation, hsz]
  have hrev : reverseBits i.val (2 ^ 12) < 2 ^ 12 := reverseBits_lt_two_pow _ 12
  -- The forward FFT of the coefficients returns the values, in bit-reversed order.
  have hfwd := getElem!_fftField_eval hω (polynomialEvalToCoeff poly) _
    (by rw [size_polynomialEvalToCoeff, hsz]) hrs hroots _ hrev
  have hround : fftField (polynomialEvalToCoeff poly) (computeRootsOfUnity (2 ^ 12)) false =
      bitReversalPermutation poly :=
    fftField_inv_fftField hω _ _ hbsz hrs hroots
  rw [hround, getElem!_bitReversalPermutation poly _ (by rw [hsz]; exact hrev), hsz,
    reverseBits_reverseBits i.isLt] at hfwd
  rw [blobPolynomial, eval_coefficientPolynomial, evalDomain,
    getElem_rootsOfUnityBrp field_elements_per_blob_eq_two_pow]
  exact hfwd.symm

/-- **The cells of a blob are the codeword of its polynomial.**

On a blob that decodes, the cell computation returns 128 cells.

Cell `j` is symbol `j` of the codeword of the polynomial of the blob. -/
theorem computeCells_eq_codewordCell {blob : Blob} {poly : Kzg.Polynomial}
    (h : blobToPolynomial blob = .ok poly) :
    computeCells blob = .ok (Array.ofFn fun j : Fin CELLS_PER_EXT_BLOB =>
      codewordCell (blobPolynomial poly) j.val) := by
  obtain ⟨cells, hc, hsz, hcell⟩ := computeCells_ok_spec h
  refine hc.trans (congrArg Except.ok (Array.ext (by rw [hsz, Array.size_ofFn]) ?_))
  intro j hj _
  obtain ⟨coset, hcoset, hcsz, hcelem⟩ := cosetForCell_ok_of_lt (hsz ▸ hj)
  rw [Array.getElem_ofFn, ← getElem!_pos cells j hj, hcell j coset hcoset, codewordCell]
  refine congrArg cosetEvalsToCell (Array.ext (by simp [hcsz]) fun m hm _ => ?_)
  have hm' : m < FIELD_ELEMENTS_PER_CELL := by simpa [hcsz] using hm
  rw [Array.getElem_map, Array.getElem_ofFn, ← getElem!_pos coset m (by simpa using hm),
    hcelem m hm', evaluatePolynomialcoeff_eq_evalPolyAt, ← eval_coefficientPolynomial,
    cellPoint, Nat.mul_comm]
  rfl

/-- **Cells that the code computes for one blob do not win code-binding.**

Take any openings at cell indices below 128, whose cells are those of one blob.

The bound makes each index name one of the 128 cells; an accepted opening satisfies it.

Then the polynomial of the blob agrees with every opened cell.

So the openings fail the winning condition of code-binding, whatever the setup.

The commitment and the proofs are arbitrary: nothing follows about whether the openings verify. -/
theorem not_codeBindingWins_of_computeCells {blob : Blob} {cells : Array Cell}
    (h : computeCells blob = .ok cells) (s : TrustedSetup) (commitment : Bytes48)
    {os : List CellOpening} (hos : ∀ o ∈ os, o.cellIndex < CELLS_PER_EXT_BLOB ∧
      o.cell = cells[o.cellIndex]!) :
    ¬CodeBindingWins s (commitment, os) := by
  cases hp : blobToPolynomial blob with
  | error e =>
    rw [computeCells, hp] at h
    cases h
  | ok poly =>
    rw [computeCells_eq_codewordCell hp] at h
    obtain rfl := Except.ok.inj h
    refine fun hw => hw.2.2 ⟨blobPolynomial poly, natDegree_blobPolynomial_lt hp, fun o ho => ?_⟩
    obtain ⟨hlt, hcell⟩ := hos o ho
    rw [hcell, getElem!_pos _ _ (by rw [Array.size_ofFn]; exact hlt), Array.getElem_ofFn]

end EthLib.Cryptography.Kzg
