module

public import EthLib.Cryptography.Proofs.Kzg.BlobBindingGame

/-!
# Proofs: the blob-binding equation and the concrete verifier

`BlobBatchInput.toOpeningBatch` fixes each individual challenge to `computeChallenge`.

It also fixes each value to the decoded blob's evaluation.

The batch challenge is then the concrete `computeVerifyKzgProofBatchChallenge`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.BlobBinding

open EthLib.Cryptography.Bls (Fr G1)
open Polynomial
open scoped EthLib.Cryptography.Bls.Fr

/-- Evaluating the symbolic error gives the scalar error used by the batch verifier. -/
theorem eval_batchErrorAt (openings : List Opening) (r τ : Fr) :
    (batchErrorAt openings r).eval τ =
      ∑ i : Fin openings.length,
        openingError τ (openings[i].commitment.polynomial.eval τ) openings[i].y
          (openings[i].proof.polynomial.eval τ) openings[i].z * r ^ i.val := by
  induction openings with
  | nil => simp
  | cons o openings ih =>
    simp only [batchErrorAt_cons, eval_add, eval_mul, eval_C, ih, List.length_cons,
      Fin.sum_univ_succ, Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ,
      Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
    rw [Finset.mul_sum]
    have ho : o.error.eval τ = openingError τ (o.commitment.polynomial.eval τ) o.y
        (o.proof.polynomial.eval τ) o.z := by
      simp [Opening.error, eval_blobOpeningError_at, openingError]
    rw [ho]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

private theorem getElem!_map_toArray {α β : Type} [Inhabited β]
    (f : α → β) (xs : List α) (i : Fin xs.length) :
    (xs.map f).toArray[i.val]! = f xs[i] := by
  rw [getElem!_pos _ _ (by simp)]
  simp

/-- Valid algebraic annotations give the concrete scalar of their point encoding. -/
theorem AlgebraicPoint.scalarOf_eq {τ : Fr} {point : AlgebraicPoint}
    (hv : validateKzgG1 point.bytes = true) (ha : point.Valid τ) :
    scalarOf point.bytes = point.polynomial.eval τ := by
  obtain ⟨P, hP⟩ := exists_validateKzgG1Point_of_validateKzgG1 hv
  exact Kzg.scalarOf_eq hP (ha P hP)

/-- The game equation equals the concrete blob-batch error at the same challenges. -/
theorem eval_batchErrorAt_eq_errorPoly {τ : Fr} {y : BlobBatchInput}
    {openings : List Opening}
    (hbatch : Opening.toBatch openings = y.toOpeningBatch)
    (hv : ∀ o ∈ openings,
      validateKzgG1 o.commitment.bytes = true ∧ validateKzgG1 o.proof.bytes = true)
    (ha : ∀ o ∈ openings, o.commitment.Valid τ ∧ o.proof.Valid τ) (r : Fr) :
    (batchErrorAt openings r).eval τ = (y.errorPoly τ scalarOf scalarOf).eval r := by
  have hc := congrArg OpeningBatch.commitments hbatch
  have hz := congrArg OpeningBatch.zs hbatch
  have hy := congrArg OpeningBatch.ys hbatch
  have hp := congrArg OpeningBatch.proofs hbatch
  simp only [Opening.toBatch, OpeningData.toBatch, List.map_map, Function.comp_def,
    Opening.data, BlobBatchInput.toOpeningBatch] at hc hz hy hp
  rw [eval_batchErrorAt, BlobBatchInput.errorPoly, eval_batchErrorPoly,
    ← hc, ← hz, ← hy, ← hp]
  simp only [List.size_toArray, List.length_map]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [getElem!_map_toArray]
  have hi := List.getElem_mem i.isLt
  rw [(openings[i].commitment.scalarOf_eq (hv _ hi).1 (ha _ hi).1),
    (openings[i].proof.scalarOf_eq (hv _ hi).2 (ha _ hi).2)]

/-- The symbolic equation specializes to the concrete blob verifier's verdict.

The equality of opening batches fixes the individual challenges and evaluations.

`y.challenge` is the actual hash of those openings. -/
theorem verifyBlobKzgProofBatch_ok_iff_symbolic {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) (y : BlobBatchInput) (openings : List Opening)
    (hbatch : Opening.toBatch openings = y.toOpeningBatch)
    (hv : ∀ o ∈ openings,
      validateKzgG1 o.commitment.bytes = true ∧ validateKzgG1 o.proof.bytes = true)
    (ha : ∀ o ∈ openings, o.commitment.Valid τ ∧ o.proof.Valid τ) {b : Bool}
    (h : verifyBlobKzgProofBatch s y.blobs y.commitments y.proofs = .ok b) :
    b = true ↔ (batchErrorAt openings y.challenge).eval τ = 0 := by
  obtain ⟨_, _, _, _, _, hcs, hps, _⟩ := verifyBlobKzgProofBatch_eq_ok h
  obtain ⟨hcsz, hc⟩ := Base.array_mapM_ok hcs
  obtain ⟨hpsz, hp⟩ := Base.array_mapM_ok hps
  rw [eval_batchErrorAt_eq_errorPoly hbatch hv ha]
  apply verifyBlobKzgProofBatch_ok_iff_root hs y
  · intro i hi P hP
    have hvalid := hc i hi (hcsz.symm ▸ hi)
    rw [← getElem!_pos y.commitments i hi] at hvalid
    exact represents_scalarOf (validateKzgG1_of_validateKzgG1Point hvalid) hP
  · intro i hi P hP
    have hvalid := hp i hi (hpsz.symm ▸ hi)
    rw [← getElem!_pos y.proofs i hi] at hvalid
    exact represents_scalarOf (validateKzgG1_of_validateKzgG1Point hvalid) hP
  · exact h

end EthLib.Cryptography.Kzg.BlobBinding
