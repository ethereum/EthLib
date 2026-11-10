module

public import EthLib.Cryptography.Proofs.Kzg.BlobBindingSecurity

/-!
# Proofs: the blob-binding equation and the concrete verifier

The concrete batch fixes each individual challenge to the hash of its blob and commitment.

It also fixes each value to the decoded blob's evaluation.

The batch challenge is then the verifier's own hash of those openings.

When a successful challenge loop takes the concrete hashes as challenges, its openings are that batch.
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
  rw [batchErrorAt, batchError, eval_errorPoly, eval_finsetSum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [List.getD_eq_getElem?_getD, Opening.error, eval_blobOpeningError_at, openingError]

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

/-- A call of the blob verifier that returns a verdict validated every point of its batch.

So the openings of the same batch pass point validation. -/
theorem validated_of_verifyBlobKzgProofBatch {s : TrustedSetup} {y : BlobBatchInput}
    {openings : List Opening} (hbatch : Opening.toBatch openings = y.toOpeningBatch) {b : Bool}
    (h : verifyBlobKzgProofBatch s y.blobs y.commitments y.proofs = .ok b) :
    ∀ o ∈ openings,
      validateKzgG1 o.commitment.bytes = true ∧ validateKzgG1 o.proof.bytes = true := by
  obtain ⟨_, _, _, _, _, hcs, hps, _⟩ := verifyBlobKzgProofBatch_eq_ok h
  obtain ⟨hcsz, hc⟩ := Base.array_mapM_ok hcs
  obtain ⟨hpsz, hp⟩ := Base.array_mapM_ok hps
  have hc' := congrArg OpeningBatch.commitments hbatch
  have hp' := congrArg OpeningBatch.proofs hbatch
  simp only [Opening.toBatch, OpeningData.toBatch, List.map_map, Function.comp_def,
    Opening.data, BlobBatchInput.toOpeningBatch] at hc' hp'
  intro o ho
  constructor
  · have hmem : o.commitment.bytes ∈ y.commitments := by
      rw [← hc']; simpa using ⟨o, ho, rfl⟩
    obtain ⟨i, hi, hie⟩ := Array.mem_iff_getElem.mp hmem
    have hvalid := hc i hi (hcsz.symm ▸ hi)
    rw [hie] at hvalid
    exact validateKzgG1_of_validateKzgG1Point hvalid
  · have hmem : o.proof.bytes ∈ y.proofs := by
      rw [← hp']; simpa using ⟨o, ho, rfl⟩
    obtain ⟨i, hi, hie⟩ := Array.mem_iff_getElem.mp hmem
    have hvalid := hp i hi (hpsz.symm ▸ hi)
    rw [hie] at hvalid
    exact validateKzgG1_of_validateKzgG1Point hvalid

/-- The symbolic equation specializes to the concrete blob verifier's verdict.

The equality of opening batches fixes the individual challenges and evaluations.

The batch challenge is the actual hash of those openings. -/
theorem verifyBlobKzgProofBatch_ok_iff_symbolic {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) (y : BlobBatchInput) (openings : List Opening)
    (hbatch : Opening.toBatch openings = y.toOpeningBatch)
    (ha : ∀ o ∈ openings, o.commitment.Valid τ ∧ o.proof.Valid τ) {b : Bool}
    (h : verifyBlobKzgProofBatch s y.blobs y.commitments y.proofs = .ok b) :
    b = true ↔ (batchErrorAt openings y.challenge).eval τ = 0 := by
  obtain ⟨_, _, _, _, _, hcs, hps, _⟩ := verifyBlobKzgProofBatch_eq_ok h
  obtain ⟨hcsz, hc⟩ := Base.array_mapM_ok hcs
  obtain ⟨hpsz, hp⟩ := Base.array_mapM_ok hps
  rw [eval_batchErrorAt_eq_errorPoly hbatch (validated_of_verifyBlobKzgProofBatch hbatch h) ha]
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

/-! ## The game's challenge loop and the concrete batch -/

/-- The verifier's input for the blobs, commitments and proofs that the adversary submits. -/
def BlobOpening.toInput (out : List BlobOpening) : BlobBatchInput where
  blobs := (out.map BlobOpening.blob).toArray
  commitments := (out.map fun o => o.commitment.bytes).toArray
  proofs := (out.map fun o => o.proof.bytes).toArray

/-- Matching openings keep the submitted commitments and proofs, in order. -/
private theorem Matches.map_points {out : List BlobOpening} {openings : List Opening}
    (h : Matches out openings) :
    openings.map Opening.commitment = out.map BlobOpening.commitment ∧
      openings.map Opening.proof = out.map BlobOpening.proof := by
  induction out generalizing openings with
  | nil => cases openings <;> simp_all [Matches]
  | cons o out ih =>
    cases openings with
    | nil => cases h
    | cons opening openings =>
      have := ih h.2.2.2
      simp [h.1, h.2.1, this.1, this.2]

/-- Matching openings come from decoded blobs whose polynomials give the opened values. -/
private theorem Matches.exists_polys {out : List BlobOpening} {openings : List Opening}
    (h : Matches out openings) :
    ∃ ps : List Polynomial, (out.map BlobOpening.blob).mapM blobToPolynomial = .ok ps ∧
      ps.length = out.length ∧
      ∀ (i : Nat) (hi : i < openings.length) (hj : i < ps.length),
        openings[i].y = (interpolant ps[i]).eval openings[i].z := by
  induction out generalizing openings with
  | nil =>
    cases openings with
    | nil => exact ⟨[], rfl, rfl, by simp⟩
    | cons _ _ => cases h
  | cons o out ih =>
    cases openings with
    | nil => cases h
    | cons opening openings =>
      obtain ⟨⟨values, hb, hy⟩, hrest⟩ := h.2.2
      obtain ⟨ps, hps, hlen, hall⟩ := ih hrest
      refine ⟨values :: ps, ?_, by simp [hlen], ?_⟩
      · simp only [List.map_cons, List.mapM_cons, hb, hps]
        rfl
      · intro i hi hj
        cases i with
        | zero => simpa using hy
        | succ i => simpa using hall i (by simpa using hi) (by simpa using hj)

/-- **The game's openings are the concrete batch.**

Let the openings of the challenge loop match the submitted blobs.

Let each challenge be the concrete hash of its blob and commitment.

Then the openings form the batch that the concrete verifier builds from the submission. -/
theorem Matches.toBatch_eq_toOpeningBatch {out : List BlobOpening} {openings : List Opening}
    (hm : Matches out openings)
    (hz : openings.map Opening.z = out.map fun o => computeChallenge o.blob o.commitment.bytes) :
    Opening.toBatch openings = (BlobOpening.toInput out).toOpeningBatch := by
  have hlen := hm.length
  obtain ⟨hc, hp⟩ := hm.map_points
  obtain ⟨ps, hps, hpl, hy⟩ := hm.exists_polys
  have hdec : decodeBlobPolys (BlobOpening.toInput out).blobs = ps.toArray := by
    apply decodeBlobPolys_of_ok
    rw [Array.mapM_eq_mapM_toList]
    simp only [BlobOpening.toInput, List.toList_toArray, hps]
    rfl
  have hcb : openings.map (fun o => o.commitment.bytes) = out.map fun o => o.commitment.bytes := by
    have := congrArg (List.map AlgebraicPoint.bytes) hc
    simpa [List.map_map, Function.comp_def] using this
  have hpb : openings.map (fun o => o.proof.bytes) = out.map fun o => o.proof.bytes := by
    have := congrArg (List.map AlgebraicPoint.bytes) hp
    simpa [List.map_map, Function.comp_def] using this
  unfold Opening.toBatch OpeningData.toBatch BlobBatchInput.toOpeningBatch
  simp only [List.map_map, Function.comp_def, Opening.data]
  have hch : (BlobOpening.toInput out).challenges = (openings.map Opening.z).toArray := by
    rw [hz]
    apply Array.ext
    · simp [BlobBatchInput.challenges, BlobOpening.toInput]
    · intro i h1 h2
      have hi : i < out.length := by simpa using h2
      simp [BlobBatchInput.challenges, BlobOpening.toInput, List.getElem?_eq_getElem hi]
  have hev : (BlobOpening.toInput out).evals = (openings.map fun x => x.y).toArray := by
    apply Array.ext
    · simp [BlobBatchInput.evals, hlen, BlobOpening.toInput]
    · intro i h1 h2
      have hi : i < out.length := by simpa [BlobBatchInput.evals, BlobOpening.toInput] using h1
      have hio : i < openings.length := hlen ▸ hi
      have hip : i < ps.length := hpl ▸ hi
      simp only [BlobBatchInput.evals, Array.getElem_ofFn, hdec, hch]
      rw [getElem!_pos _ _ (by simpa using hio), getElem!_pos _ _ (by simpa using hip)]
      simpa using (hy i hio hip).symm
  rw [hcb, hpb, hch, hev]
  rfl

/-- A successful challenge loop with the concrete hashes as challenges gives the concrete batch. -/
theorem toBatch_eq_toOpeningBatch_of_mem_support_challengeOpenings {out : List BlobOpening}
    {openings : List Opening} (h : some openings ∈ MonadAttach.support (challengeOpenings out))
    (hz : openings.map Opening.z = out.map fun o => computeChallenge o.blob o.commitment.bytes) :
    Opening.toBatch openings = (BlobOpening.toInput out).toOpeningBatch :=
  (matches_of_mem_support_challengeOpenings out h).toBatch_eq_toOpeningBatch hz

/-- **The game's equation is the concrete verdict.**

Let the openings of the challenge loop match the submitted blobs.

Let their challenges be the concrete hashes, and their point annotations be correct.

Let the blob verifier return a verdict on the submission.

Then the verdict is true exactly when the game's equation holds at the concrete batch challenge. -/
theorem verifyBlobKzgProofBatch_ok_iff_game {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {out : List BlobOpening} {openings : List Opening} (hm : Matches out openings)
    (hz : openings.map Opening.z = out.map fun o => computeChallenge o.blob o.commitment.bytes)
    (ha : ∀ o ∈ openings, o.commitment.Valid τ ∧ o.proof.Valid τ) {b : Bool}
    (h : verifyBlobKzgProofBatch s (BlobOpening.toInput out).blobs
      (BlobOpening.toInput out).commitments (BlobOpening.toInput out).proofs = .ok b) :
    b = true ↔ (batchErrorAt openings (BlobOpening.toInput out).challenge).eval τ = 0 :=
  verifyBlobKzgProofBatch_ok_iff_symbolic hs _ openings (hm.toBatch_eq_toOpeningBatch hz) ha h

end EthLib.Cryptography.Kzg.BlobBinding
