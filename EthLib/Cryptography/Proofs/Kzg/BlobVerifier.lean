module

public import EthLib.Cryptography.Proofs.Bls.FinalExponentiation
public import EthLib.Cryptography.Proofs.Bls.PairingCongr
public import EthLib.Cryptography.Proofs.Kzg.BatchChallenge

/-!
# Proofs: the batch check of blob openings

The batch check of blobs takes triples of a blob, a commitment and a proof, as bytes.

For each triple in turn, it validates the commitment, decodes the blob and validates the proof.

It evaluates each decoded blob at its evaluation challenge.

It then runs the batch check of openings on these points, evaluation challenges and values.

Each root below is a root of the error polynomial of the batch.

- On well-formed inputs of one size, the batch check of blobs returns a verdict, with no error.
- The empty batch verifies, for every setup.
- Under the pairing law, the verdict is true exactly when the batch challenge is a root.
- Every entry of an accepted batch satisfies the opening equation, or the batch challenge is a root.
- With the hash a random oracle, the root case has probability at most `(q + 1) (n - 1) / r`.
  Here `q` bounds the queries, `n` the commitments, and `r` is the order of `Fr`.
- The bound is tight at `q = 0` and `n = 2`, where a batch of two blobs reaches it.
- Every batch of valid blob openings is accepted, including honestly computed proofs.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (array_mapM_ok array_mapM_exists_ok)
open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-! ## Inputs and error polynomial of a blob batch -/

/-- The inputs of the batch check of blobs, as the caller gives them. -/
structure BlobBatchInput where
  blobs : Array Blob
  commitments : Array Bytes48
  proofs : Array Bytes48

/-- The polynomials of the blobs, or no polynomials if some blob does not decode. -/
def decodeBlobPolys (blobs : Array Blob) : Array Polynomial :=
  match blobs.mapM blobToPolynomial with
  | .ok ps => ps
  | .error _ => #[]

/-- Blobs that decode have their polynomials as their decoding.

It is stated on variable blobs, so the kernel never evaluates the decoding. -/
theorem decodeBlobPolys_of_ok {blobs : Array Blob} {ps : Array Polynomial}
    (h : blobs.mapM blobToPolynomial = .ok ps) : decodeBlobPolys blobs = ps := by
  simp only [decodeBlobPolys, h]

/-- The evaluation challenges of the pairs of a blob and its commitment. -/
def BlobBatchInput.challenges (y : BlobBatchInput) : Array Fr :=
  Array.ofFn (n := y.blobs.size) fun i => computeChallenge y.blobs[i.val] y.commitments[i.val]!

/-- The values of the decoded blobs at their evaluation challenges. -/
noncomputable def BlobBatchInput.evals (y : BlobBatchInput) : Array Fr :=
  Array.ofFn (n := y.blobs.size) fun i =>
    (interpolant (decodeBlobPolys y.blobs)[i.val]!).eval y.challenges[i.val]!

/-- The batch challenge: the Fiat-Shamir challenge of the batch check of openings on blobs. -/
noncomputable def BlobBatchInput.challenge (y : BlobBatchInput) : Fr :=
  computeVerifyKzgProofBatchChallenge y.commitments y.challenges y.evals y.proofs

/-- The inputs that the batch check of openings hashes for a blob batch. -/
noncomputable def BlobBatchInput.toOpeningBatch (y : BlobBatchInput) : OpeningBatch where
  commitments := y.commitments
  zs := y.challenges
  ys := y.evals
  proofs := y.proofs

/-- The error polynomial of a blob batch, where `c` and `w` map the bytes of points to scalars. -/
noncomputable def BlobBatchInput.errorPoly (y : BlobBatchInput) (τ : Fr)
    (c w : Bytes48 → Fr) : Fr[X] :=
  batchErrorPoly τ (fun i => c y.commitments[i]!) (y.evals[·]!) (fun i => w y.proofs[i]!)
    (y.challenges[·]!) y.commitments.size

/-! ## Decomposition and totality of the batch check -/

/-- The accumulator type of the loop of the batch check of blobs. -/
private abbrev BlobBatchAcc :=
  Array KZGCommitment × Array G1 × Array Fr × Array Fr × Array KZGProof × Array G1

/-- One pure step of the accumulator of the batch check of blobs. -/
private noncomputable def blobPureStep (acc : BlobBatchAcc)
    (entry : Blob × Bytes48 × Bytes48 × G1 × G1 × Polynomial) : BlobBatchAcc :=
  let (commitments, commitmentsG1, challenges, ys, proofs, proofsG1) := acc
  let (blob, cb, pb, c, p, poly) := entry
  let z := computeChallenge blob cb
  (commitments.push cb, commitmentsG1.push c, challenges.push z,
    ys.push ((interpolant poly).eval z), proofs.push pb, proofsG1.push p)

/-- Pushing `g x` at each list element appends `(L.map g).toArray`. -/
private theorem list_foldl_push {σ α β : Type} {step : σ → α → σ} (p : σ → Array β) (g : α → β)
    (hp : ∀ acc x, p (step acc x) = (p acc).push (g x)) :
    ∀ (L : List α) (init : σ), p (L.foldl step init) = p init ++ (L.map g).toArray
  | [], init => by simp
  | x :: L, init => by
    rw [List.foldl_cons, list_foldl_push p g hp L, hp, List.map_cons, List.toArray_cons]
    ext i h₁ h₂ <;> simp [Array.getElem_append]

/-- If a fold over a list succeeds, every member satisfies any condition needed by one step. -/
private theorem list_foldlM_forall {ε σ α : Type} {f : σ → α → Except ε σ} {P : α → Prop}
    (hf : ∀ acc x r, f acc x = .ok r → P x) :
    ∀ (L : List α) init out, L.foldlM f init = .ok out → ∀ x ∈ L, P x
  | [], _, _, _, _, hx => absurd hx List.not_mem_nil
  | x :: xs, init, out, h, q, hq => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hx : f init x with
    | error e => rw [hx] at h; cases h
    | ok mid =>
      rw [hx] at h
      rcases List.mem_cons.mp hq with rfl | hmem
      · exact hf init q mid hx
      · exact list_foldlM_forall hf xs mid out h q hmem

/-- A monadic fold whose every step succeeds with a pure step returns the pure fold. -/
private theorem list_foldlM_eq_foldl {ε σ α : Type} {f : σ → α → Except ε σ} {step : σ → α → σ}
    {L : List α} (hstep : ∀ acc x, x ∈ L → f acc x = .ok (step acc x)) :
    ∀ init, L.foldlM f init = .ok (L.foldl step init) := by
  induction L with
  | nil => intro init; rfl
  | cons x xs ih =>
    intro init
    rw [List.foldlM_cons, hstep init x List.mem_cons_self, List.foldl_cons]
    simp only [bind, Except.bind]
    exact ih (fun acc q hq => hstep acc q (List.mem_cons_of_mem x hq)) _

/-- One step of the loop of the batch check of blobs, on inputs that decode. -/
private theorem blobLoopStep_of_ok (acc : BlobBatchAcc) (blob : Blob) (cb pb : Bytes48) (i : Nat)
    {c p : G1} {poly : Polynomial} (hcb : validateKzgG1Point cb = .ok c)
    (hpb : validateKzgG1Point pb = .ok p) (hbl : blobToPolynomial blob = .ok poly) :
    (let (commitments, commitmentsG1, challenges, ys, proofs, proofsG1) := acc
     do
       let commitmentG1 ← match validateKzgG1Point cb with
         | .ok c => pure c
         | .error _ => throw (KzgError.invalidCommitment (some i))
       let polynomial ← blobToPolynomial blob
       let challenge := computeChallenge blob cb
       let y ← evaluatePolynomialInEvaluationForm polynomial challenge
       let proofG1 ← match validateKzgG1Point pb with
         | .ok p => pure p
         | .error _ => throw (KzgError.invalidProof (some i))
       pure (commitments.push cb, commitmentsG1.push commitmentG1,
         challenges.push challenge, ys.push y, proofs.push pb, proofsG1.push proofG1)) =
      .ok (blobPureStep acc (blob, cb, pb, c, p, poly)) := by
  rcases acc with ⟨a1, a2, a3, a4, a5, a6⟩
  have hsz := size_blobToPolynomial blob poly hbl
  dsimp only [blobPureStep, interpolant]
  rw [hcb, hpb, hbl]
  simp only [bind, Except.bind, pure, Except.pure,
    evaluatePolynomialInEvaluationForm_eq_interpolate poly _ hsz]

/-- A successful step of the loop of the batch check of blobs means that its three inputs decode. -/
private theorem blobLoopStep_valid (acc r : BlobBatchAcc) (blob : Blob) (cb pb : Bytes48) (i : Nat)
    (hr : (let (commitments, commitmentsG1, challenges, ys, proofs, proofsG1) := acc
           do
             let commitmentG1 ← match validateKzgG1Point cb with
               | .ok c => pure c
               | .error _ => throw (KzgError.invalidCommitment (some i))
             let polynomial ← blobToPolynomial blob
             let challenge := computeChallenge blob cb
             let y ← evaluatePolynomialInEvaluationForm polynomial challenge
             let proofG1 ← match validateKzgG1Point pb with
               | .ok p => pure p
               | .error _ => throw (KzgError.invalidProof (some i))
             pure (commitments.push cb, commitmentsG1.push commitmentG1,
               challenges.push challenge, ys.push y, proofs.push pb, proofsG1.push proofG1)) =
      .ok r) :
    (∃ c, validateKzgG1Point cb = .ok c) ∧
      (∃ p, validateKzgG1Point pb = .ok p) ∧
      ∃ poly, blobToPolynomial blob = .ok poly := by
  rcases acc with ⟨a1, a2, a3, a4, a5, a6⟩
  dsimp only at hr
  cases hcb : validateKzgG1Point cb with
  | error err =>
    rw [hcb] at hr
    cases hr
  | ok c =>
    cases hbl : blobToPolynomial blob with
    | error err =>
      rw [hcb, hbl] at hr
      cases hr
    | ok poly =>
      cases hpb : validateKzgG1Point pb with
      | error err =>
        rw [hcb, hbl, hpb] at hr
        simp only [bind, Except.bind, pure, Except.pure,
          evaluatePolynomialInEvaluationForm_eq_interpolate poly _
            (size_blobToPolynomial blob poly hbl)] at hr
        cases hr
      | ok p => exact ⟨⟨c, rfl⟩, ⟨p, rfl⟩, ⟨poly, rfl⟩⟩

/-- The pure fold over raw entries produces the six arrays of their mapped components. -/
private theorem list_foldl_blobPureStep
    (L : List (Blob × Bytes48 × Bytes48 × G1 × G1 × Polynomial)) :
    L.foldl blobPureStep (#[], #[], #[], #[], #[], #[]) =
      ((L.map fun e => e.2.1).toArray, (L.map fun e => e.2.2.2.1).toArray,
        (L.map fun e => computeChallenge e.1 e.2.1).toArray,
        (L.map fun e => (interpolant e.2.2.2.2.2).eval (computeChallenge e.1 e.2.1)).toArray,
        (L.map fun e => e.2.2.1).toArray, (L.map fun e => e.2.2.2.2.1).toArray) := by
  have hp1 := list_foldl_push (step := blobPureStep) (fun s₀ => s₀.1) (fun e => e.2.1)
    (fun ⟨_, _, _, _, _, _⟩ _ => rfl) L (#[], #[], #[], #[], #[], #[])
  have hp2 := list_foldl_push (step := blobPureStep) (fun s₀ => s₀.2.1) (fun e => e.2.2.2.1)
    (fun ⟨_, _, _, _, _, _⟩ _ => rfl) L (#[], #[], #[], #[], #[], #[])
  have hp3 := list_foldl_push (step := blobPureStep) (fun s₀ => s₀.2.2.1)
    (fun e => computeChallenge e.1 e.2.1) (fun ⟨_, _, _, _, _, _⟩ _ => rfl) L
    (#[], #[], #[], #[], #[], #[])
  have hp4 := list_foldl_push (step := blobPureStep) (fun s₀ => s₀.2.2.2.1)
    (fun e => (interpolant e.2.2.2.2.2).eval (computeChallenge e.1 e.2.1))
    (fun ⟨_, _, _, _, _, _⟩ _ => rfl) L (#[], #[], #[], #[], #[], #[])
  have hp5 := list_foldl_push (step := blobPureStep) (fun s₀ => s₀.2.2.2.2.1)
    (fun e => e.2.2.1) (fun ⟨_, _, _, _, _, _⟩ _ => rfl) L (#[], #[], #[], #[], #[], #[])
  have hp6 := list_foldl_push (step := blobPureStep) (fun s₀ => s₀.2.2.2.2.2)
    (fun e => e.2.2.2.2.1) (fun ⟨_, _, _, _, _, _⟩ _ => rfl) L (#[], #[], #[], #[], #[], #[])
  rcases h : L.foldl blobPureStep (#[], #[], #[], #[], #[], #[]) with ⟨a1, a2, a3, a4, a5, a6⟩
  simp only [h, Array.empty_append] at hp1 hp2 hp3 hp4 hp5 hp6
  rw [hp1, hp2, hp3, hp4, hp5, hp6]

/-- When the three arrays decode, the loop computes the six batch arrays. -/
private theorem blobLoop_eq_ok {blobs : Array Blob} {commitmentsBytes proofsBytes : Array Bytes48}
    (hc : commitmentsBytes.size = blobs.size) (hp : proofsBytes.size = blobs.size)
    {ps : Array Polynomial} (hps : blobs.mapM blobToPolynomial = .ok ps)
    {csG1 : Array G1} (hcsG1 : commitmentsBytes.mapM validateKzgG1Point = .ok csG1)
    {psG1 : Array G1} (hpsG1 : proofsBytes.mapM validateKzgG1Point = .ok psG1) :
    let y : BlobBatchInput := ⟨blobs, commitmentsBytes, proofsBytes⟩
    (blobs.zip (commitmentsBytes.zip proofsBytes)).zipIdx.foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array G1), (#[] : Array Fr),
                (#[] : Array Fr), (#[] : Array KZGProof), (#[] : Array G1)))
      (fun (commitments, commitmentsG1, challenges, ys, proofs, proofsG1) ((blob, cb, pb), i) => do
        let commitmentG1 ← match validateKzgG1Point cb with
          | .ok c => pure c
          | .error _ => throw (KzgError.invalidCommitment (some i))
        let polynomial ← blobToPolynomial blob
        let challenge := computeChallenge blob cb
        let y ← evaluatePolynomialInEvaluationForm polynomial challenge
        let proofG1 ← match validateKzgG1Point pb with
          | .ok p => pure p
          | .error _ => throw (KzgError.invalidProof (some i))
        pure (commitments.push cb, commitmentsG1.push commitmentG1,
          challenges.push challenge, ys.push y, proofs.push pb, proofsG1.push proofG1)) =
      .ok (commitmentsBytes, csG1, y.challenges, y.evals, proofsBytes, psG1) := by
  intro y
  obtain ⟨hpssz, hpsk⟩ := array_mapM_ok hps
  obtain ⟨hcssz, hcsk⟩ := array_mapM_ok hcsG1
  obtain ⟨hpgsz, hpgk⟩ := array_mapM_ok hpsG1
  have hdec : decodeBlobPolys blobs = ps := decodeBlobPolys_of_ok hps
  rw [← Array.foldlM_toList]
  set L := (blobs.zip (commitmentsBytes.zip proofsBytes)).zipIdx.toList
  have hlenL : L.length = blobs.size := by simp [L, hc, hp]
  have hgetL : ∀ k (hk : k < L.length),
      L[k] = ((blobs[k]'(hlenL ▸ hk), commitmentsBytes[k]'(hc ▸ hlenL ▸ hk),
        proofsBytes[k]'(hp ▸ hlenL ▸ hk)), k) := by
    intro k hk
    simp [L, Array.getElem_toList]
  let pureEntry : (Blob × Bytes48 × Bytes48) × Nat →
      Blob × Bytes48 × Bytes48 × G1 × G1 × Polynomial :=
    fun e => (e.1.1, e.1.2.1, e.1.2.2, csG1[e.2]!, psG1[e.2]!, ps[e.2]!)
  rw [list_foldlM_eq_foldl (L := L)
    (step := fun acc e => blobPureStep acc (pureEntry e)) fun acc e he => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
      rw [hgetL k hk]
      have hk' : k < blobs.size := hlenL ▸ hk
      have hcb := hcsk k (hc ▸ hk') (by omega)
      rw [← getElem!_pos csG1 k (by omega)] at hcb
      have hpb := hpgk k (hp ▸ hk') (by omega)
      rw [← getElem!_pos psG1 k (by omega)] at hpb
      have hbl := hpsk k hk' (by omega)
      rw [← getElem!_pos ps k (by omega)] at hbl
      exact blobLoopStep_of_ok acc _ _ _ k hcb hpb hbl]
  rw [← List.foldl_map, list_foldl_blobPureStep]
  refine congrArg Except.ok ?_
  have h1 : ((L.map pureEntry).map fun e => e.2.1).toArray = commitmentsBytes := by
    apply Array.ext (by simp [hlenL, hc])
    intro k hk₁ hk₂
    simp [pureEntry, hgetL k (by simp [hlenL]; omega)]
  have h2 : ((L.map pureEntry).map fun e => e.2.2.2.1).toArray = csG1 := by
    apply Array.ext (by simp [hlenL, hcssz, hc])
    intro k hk₁ hk₂
    simp [pureEntry, hgetL k (by simp [hlenL]; omega), getElem!_pos csG1 k hk₂]
  have h3 : ((L.map pureEntry).map fun e => computeChallenge e.1 e.2.1).toArray = y.challenges := by
    apply Array.ext (by simp [y, BlobBatchInput.challenges, hlenL])
    intro k hk₁ hk₂
    have hk' : k < blobs.size := by simpa [y, BlobBatchInput.challenges] using hk₂
    simp [y, pureEntry, BlobBatchInput.challenges, hgetL k (hlenL.symm ▸ hk'),
      getElem!_pos commitmentsBytes k (hc ▸ hk')]
  have h4 : ((L.map pureEntry).map fun e =>
      (interpolant e.2.2.2.2.2).eval (computeChallenge e.1 e.2.1)).toArray = y.evals := by
    apply Array.ext (by simp [y, BlobBatchInput.evals, hlenL])
    intro k hk₁ hk₂
    have hk' : k < blobs.size := by simpa [y, BlobBatchInput.evals] using hk₂
    simp [y, pureEntry, BlobBatchInput.evals, BlobBatchInput.challenges, hdec,
      hgetL k (hlenL.symm ▸ hk'), getElem!_pos commitmentsBytes k (hc ▸ hk')]
  have h5 : ((L.map pureEntry).map fun e => e.2.2.1).toArray = proofsBytes := by
    apply Array.ext (by simp [hlenL, hp])
    intro k hk₁ hk₂
    simp [pureEntry, hgetL k (by simp [hlenL]; omega)]
  have h6 : ((L.map pureEntry).map fun e => e.2.2.2.2.1).toArray = psG1 := by
    apply Array.ext (by simp [hlenL, hpgsz, hp])
    intro k hk₁ hk₂
    simp [pureEntry, hgetL k (by simp [hlenL]; omega), getElem!_pos psG1 k hk₂]
  rw [h1, h2, h3, h4, h5, h6]

/-- **A blob batch check that returns a verdict decodes its inputs and checks the openings.**

Let the batch check of blobs return a verdict.

Then the commitments and the proofs are as many as the blobs.

Every blob decodes to a polynomial, and every commitment and proof passes KZG validation.

The batch check of openings returns the same verdict on the decoded inputs. -/
theorem verifyBlobKzgProofBatch_eq_ok {s : TrustedSetup} {blobs : Array Blob}
    {commitmentsBytes proofsBytes : Array Bytes48} {b : Bool}
    (h : verifyBlobKzgProofBatch s blobs commitmentsBytes proofsBytes = .ok b) :
    let y : BlobBatchInput := ⟨blobs, commitmentsBytes, proofsBytes⟩
    commitmentsBytes.size = blobs.size ∧ proofsBytes.size = blobs.size ∧
      (∃ ps, blobs.mapM blobToPolynomial = .ok ps) ∧
      ∃ commitmentsG1 proofsG1,
        commitmentsBytes.mapM validateKzgG1Point = .ok commitmentsG1 ∧
        proofsBytes.mapM validateKzgG1Point = .ok proofsG1 ∧
        verifyKzgProofBatch s commitmentsBytes commitmentsG1 y.challenges y.evals
          proofsBytes proofsG1 = .ok b := by
  intro y
  unfold verifyBlobKzgProofBatch at h
  by_cases hc : commitmentsBytes.size ≠ blobs.size
  · rw [ite_eq_left hc] at h
    cases h
  by_cases hp : proofsBytes.size ≠ blobs.size
  · rw [ite_eq_right hc, ite_eq_left hp] at h
    cases h
  rw [ite_eq_right hc, ite_eq_right hp] at h
  replace hc := Decidable.not_not.mp hc
  replace hp := Decidable.not_not.mp hp
  obtain ⟨acc, hfold, hbatch⟩ := EthLib.Base.bind_ok_iff.mp h
  have hmemL : ∀ k (hk : k < blobs.size),
      ((blobs[k], commitmentsBytes[k]'(hc ▸ hk), proofsBytes[k]'(hp ▸ hk)), k) ∈
        (blobs.zip (commitmentsBytes.zip proofsBytes)).zipIdx.toList := by
    intro k hk
    have hkz : k < (blobs.zip (commitmentsBytes.zip proofsBytes)).zipIdx.size := by
      simp [hc, hp, hk]
    have heq : (blobs.zip (commitmentsBytes.zip proofsBytes)).zipIdx[k]'hkz =
        ((blobs[k], commitmentsBytes[k]'(hc ▸ hk), proofsBytes[k]'(hp ▸ hk)), k) := by
      simp [Array.getElem_zipIdx, Array.getElem_zip]
    rw [← heq]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hkz)
  have hfoldL := hfold
  rw [← Array.foldlM_toList] at hfoldL
  have hall := list_foldlM_forall
    (fun s₀ (e : (Blob × Bytes48 × Bytes48) × Nat) r hr =>
      blobLoopStep_valid s₀ r e.1.1 e.1.2.1 e.1.2.2 e.2 hr) _ _ _ hfoldL
  obtain ⟨ps, hps⟩ := array_mapM_exists_ok (f := blobToPolynomial) (xs := blobs) fun bl hbl => by
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hbl
    exact (hall _ (hmemL k hk)).2.2
  obtain ⟨csG1, hcsG1⟩ := array_mapM_exists_ok (f := validateKzgG1Point)
      (xs := commitmentsBytes) fun cb hcb => by
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hcb
    exact (hall _ (hmemL k (hc ▸ hk))).1
  obtain ⟨psG1, hpsG1⟩ := array_mapM_exists_ok (f := validateKzgG1Point)
      (xs := proofsBytes) fun pb hpb => by
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hpb
    exact (hall _ (hmemL k (hp ▸ hk))).2.1
  have hacc := Except.ok.inj (hfold.symm.trans (blobLoop_eq_ok hc hp hps hcsG1 hpsG1))
  subst hacc
  exact ⟨hc, hp, ⟨ps, hps⟩, csG1, psG1, hcsG1, hpsG1, hbatch⟩

/-- **The blob batch check returns a verdict on well-formed inputs of one size.**

The commitments and the proofs are as many as the blobs.

Every blob decodes to a polynomial, and every commitment and proof passes KZG validation.

Then the batch check of blobs returns a verdict, with no error. -/
theorem verifyBlobKzgProofBatch_exists_ok (s : TrustedSetup) {blobs : Array Blob}
    {commitmentsBytes proofsBytes : Array Bytes48}
    (hc : commitmentsBytes.size = blobs.size) (hp : proofsBytes.size = blobs.size)
    (hblobs : ∀ blob ∈ blobs, ∃ poly, blobToPolynomial blob = .ok poly)
    (hcs : ∀ cb ∈ commitmentsBytes, validateKzgG1 cb = true)
    (hps : ∀ pb ∈ proofsBytes, validateKzgG1 pb = true) :
    ∃ b, verifyBlobKzgProofBatch s blobs commitmentsBytes proofsBytes = .ok b := by
  obtain ⟨ps, hpsM⟩ := array_mapM_exists_ok hblobs
  obtain ⟨csG1, hcsG1⟩ := array_mapM_exists_ok (f := validateKzgG1Point)
    (xs := commitmentsBytes) fun cb hcb => exists_validateKzgG1Point_of_validateKzgG1 (hcs cb hcb)
  obtain ⟨psG1, hpsG1⟩ := array_mapM_exists_ok (f := validateKzgG1Point)
    (xs := proofsBytes) fun pb hpb => exists_validateKzgG1Point_of_validateKzgG1 (hps pb hpb)
  unfold verifyBlobKzgProofBatch
  rw [ite_eq_right (not_not.mpr hc), ite_eq_right (not_not.mpr hp)]
  obtain ⟨b, hb⟩ := verifyKzgProofBatch_exists_ok s
    (zs := (⟨blobs, commitmentsBytes, proofsBytes⟩ : BlobBatchInput).challenges)
    (ys := (⟨blobs, commitmentsBytes, proofsBytes⟩ : BlobBatchInput).evals)
    (by simp [BlobBatchInput.challenges, hc]) (by simp [BlobBatchInput.evals, hc])
    (hp.trans hc.symm) (array_mapM_ok hcsG1).1 ((array_mapM_ok hpsG1).1.trans (hp.trans hc.symm))
  exact ⟨b, EthLib.Base.bind_ok_iff.mpr ⟨_, blobLoop_eq_ok hc hp hpsM hcsG1 hpsG1, hb⟩⟩

/-- **The empty batch verifies.**

With no blob, no commitment and no proof, the batch check of blobs returns true.

It holds for every setup, with no assumption on the pairing. -/
theorem verifyBlobKzgProofBatch_empty (s : TrustedSetup) :
    verifyBlobKzgProofBatch s #[] #[] #[] = .ok true := by
  have hpowers : computePowers (computeVerifyKzgProofBatchChallenge #[] #[] #[] #[]) 0 = #[] :=
    Array.eq_empty_of_size_eq_zero (size_computePowers _ 0)
  -- The loop over no entry leaves six empty arrays, and every sum over them is the identity.
  simp [verifyBlobKzgProofBatch, Array.foldlM, verifyKzgProofBatch, hpowers,
    g1LincombPoints_empty]
  -- Both pairs hold the point at infinity, so the pairing check sees an empty product.
  have hinf : ∀ pq ∈ #[((G1.zero : G1), (s.g2Monomial[1]'(by decide)).neg),
      ((G1.zero : G1).add G1.zero, (G2.generator : G2))],
      (pq.1.isInfinity || pq.2.isInfinity) = true := by
    simp [Bls.G1.add, Bls.G1.isInfinity, Bls.G1.zero, Bls.Fp.isZero]
  rw [← Array.empty_append (xs := #[_, _]), Bls.pairingCheck_append_infinity _ _ hinf,
    Bls.pairingCheck_eq_finalExp_prod]
  simp only [List.filterMap_nil, List.foldl_nil, Bls.finalExponentiation_eq_pow,
    Bls.Fp12.one_eq_one, one_pow]
  exact congrArg Except.ok (Bls.Fp12.isOne_iff.mpr rfl)

/-! ## Root characterization and soundness dichotomy -/

/-- **The verdict of the blob batch check, as a root.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Let each commitment that decodes give a point that represents the scalar `c` of its bytes.

Let each proof that decodes give a point that represents the scalar `w` of its bytes.

Let the batch check of blobs return the verdict `b`.

Then `b` is true exactly when the batch challenge is a root of the error polynomial of the batch. -/
theorem verifyBlobKzgProofBatch_ok_iff_root (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) (y : BlobBatchInput) {c w : Bytes48 → Fr}
    (hC : ∀ i < y.commitments.size, ∀ P, uncompressG1 y.commitments[i]! = .ok P →
      G1.Represents P (c y.commitments[i]!))
    (hP : ∀ i < y.proofs.size, ∀ P, uncompressG1 y.proofs[i]! = .ok P →
      G1.Represents P (w y.proofs[i]!)) {b : Bool}
    (h : verifyBlobKzgProofBatch s y.blobs y.commitments y.proofs = .ok b) :
    b = true ↔ (y.errorPoly τ c w).eval y.challenge = 0 := by
  obtain ⟨-, -, -, csG1, psG1, hcsG1, hpsG1, hbatch⟩ := verifyBlobKzgProofBatch_eq_ok h
  obtain ⟨hcssz, hcsk⟩ := array_mapM_ok hcsG1
  obtain ⟨hpgsz, hpgk⟩ := array_mapM_ok hpsG1
  have hC' : ∀ i < csG1.size, G1.Represents csG1[i]! ((fun i => c y.commitments[i]!) i) :=
    fun i hi => by
      have h1 := hcsk i (hcssz ▸ hi) hi
      rw [← getElem!_pos y.commitments i (hcssz ▸ hi), ← getElem!_pos csG1 i hi] at h1
      exact hC i (hcssz ▸ hi) _ (uncompressG1_of_validateKzgG1Point h1)
  have hP' : ∀ i < psG1.size, G1.Represents psG1[i]! ((fun i => w y.proofs[i]!) i) :=
    fun i hi => by
      have h1 := hpgk i (hpgsz ▸ hi) hi
      rw [← getElem!_pos y.proofs i (hpgsz ▸ hi), ← getElem!_pos psG1 i hi] at h1
      exact hP i (hpgsz ▸ hi) _ (uncompressG1_of_validateKzgG1Point h1)
  exact verifyKzgProofBatch_ok_iff_root laws hs hC' hP' hbatch

/-- **An accepted batch of blobs is valid, or its batch challenge is a root.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Let each commitment that decodes give a point that represents the scalar `c` of its bytes.

Let each proof that decodes give a point that represents the scalar `w` of its bytes.

Let the batch check of blobs accept.

Then every entry satisfies `c - y = w (τ - z)` at its evaluation challenge `z` and value `y`.

Each entry also passes the check of one blob.

Otherwise the error polynomial of the batch is not zero, and the batch challenge is a root of it. -/
theorem verifyBlobKzgProofBatch_valid_or_root (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) (y : BlobBatchInput) {c w : Bytes48 → Fr}
    (hC : ∀ i < y.commitments.size, ∀ P, uncompressG1 y.commitments[i]! = .ok P →
      G1.Represents P (c y.commitments[i]!))
    (hP : ∀ i < y.proofs.size, ∀ P, uncompressG1 y.proofs[i]! = .ok P →
      G1.Represents P (w y.proofs[i]!))
    (h : verifyBlobKzgProofBatch s y.blobs y.commitments y.proofs = .ok true) :
    (∀ i < y.blobs.size,
        c y.commitments[i]! - y.evals[i]! = w y.proofs[i]! * (τ - y.challenges[i]!) ∧
        verifyBlobKzgProof s y.blobs[i]! y.commitments[i]! y.proofs[i]! = .ok true) ∨
      (y.errorPoly τ c w ≠ 0 ∧ (y.errorPoly τ c w).eval y.challenge = 0) := by
  by_cases hzero : y.errorPoly τ c w = 0
  · obtain ⟨hc, hp, ⟨ps, hps⟩, csG1, psG1, hcsG1, hpsG1, -⟩ := verifyBlobKzgProofBatch_eq_ok h
    obtain ⟨hpssz, hpsk⟩ := array_mapM_ok hps
    obtain ⟨hcssz, hcsk⟩ := array_mapM_ok hcsG1
    obtain ⟨hpgsz, hpgk⟩ := array_mapM_ok hpsG1
    have hdec : decodeBlobPolys y.blobs = ps := decodeBlobPolys_of_ok hps
    refine Or.inl fun i hi => ?_
    have hi_c : i < y.commitments.size := hc ▸ hi
    have hi_p : i < y.proofs.size := hp ▸ hi
    have heq := (batchErrorPoly_eq_zero_iff τ (fun k => c y.commitments[k]!) (y.evals[·]!)
      (fun k => w y.proofs[k]!) (y.challenges[·]!) y.commitments.size).mp hzero i hi_c
    refine ⟨heq, ?_⟩
    have hbl := hpsk i hi (hpssz ▸ hi)
    have hcb := hcsk i hi_c (hcssz ▸ hi_c)
    have hpb := hpgk i hi_p (hpgsz ▸ hi_p)
    rw [← getElem!_pos y.blobs i hi, ← getElem!_pos ps i (hpssz ▸ hi)] at hbl
    rw [← getElem!_pos y.commitments i hi_c, ← getElem!_pos csG1 i (hcssz ▸ hi_c)] at hcb
    rw [← getElem!_pos y.proofs i hi_p, ← getElem!_pos psG1 i (hpgsz ▸ hi_p)] at hpb
    have hrC := hC i hi_c _ (uncompressG1_of_validateKzgG1Point hcb)
    have hrP := hP i hi_p _ (uncompressG1_of_validateKzgG1Point hpb)
    have hchal : y.challenges[i]! = computeChallenge y.blobs[i]! y.commitments[i]! := by
      rw [getElem!_pos y.challenges i (by simp [BlobBatchInput.challenges, hi])]
      simp [BlobBatchInput.challenges, getElem!_pos y.blobs i hi]
    have heval : y.evals[i]! = (interpolant ps[i]!).eval y.challenges[i]! := by
      rw [getElem!_pos y.evals i (by simp [BlobBatchInput.evals, hi])]
      simp [BlobBatchInput.evals, hdec]
    refine verifyBlobKzgProof_of_blobOpeningValid laws hs
      ⟨ps[i]!, _, _, _, _, hbl, hcb, hrC, hpb, hrP, ?_⟩
    rw [← hchal, ← heval]
    exact heq
  · exact Or.inr ⟨hzero, (verifyBlobKzgProofBatch_ok_iff_root laws hs y hC hP h).mp rfl⟩

/-! ## The batch challenge from a random oracle -/

/-- The game of the batch challenge for the batch check of blobs.

The adversary queries the oracle as it likes, then outputs the inputs of a blob batch.

The verifier hashes the batch of openings that the batch check of blobs builds. -/
noncomputable def blobInputRomExperiment
    (adversary : OracleComp (OpeningBatch →ₒ Fr) BlobBatchInput) :
    OracleComp (OpeningBatch →ₒ Fr) (BlobBatchInput × Fr) := do
  let y ← adversary
  let r ← liftM ((OpeningBatch →ₒ Fr).query y.toOpeningBatch)
  return (y, r)

/-- **The bound for batches of at most `n` blobs.**

The hash of the batch check is a random oracle on the batch of openings that the check builds.

The adversary makes at most `q` queries, then outputs a batch with at most `n` commitments.

The event is that the batch challenge is a root of a nonzero error polynomial of the batch.

Its probability is at most `(q + 1) (n - 1) / r`.

An accepted batch runs on inputs of one size, so `n` bounds the number of blobs as well.

The event does not ask that the check accepts.

Take the pairing law, a well-formed setup of `τ`, and the oracle in place of the hash.

Let each scalar be the scalar of its bytes.

Then an accepted batch with an invalid entry lies in this event. -/
theorem prEvent_blobInput_root_le (τ : Fr) (c w : Bytes48 → Fr) {n : Nat}
    (adversary : OracleComp (OpeningBatch →ₒ Fr) BlobBatchInput) {q : Nat}
    (hq : OracleComp.IsTotalQueryBound adversary q) :
    Pr{let p ← (simulateQ OracleSpec.randomOracle (blobInputRomExperiment adversary)).run' ∅}[
        p.1.commitments.size ≤ n ∧ p.1.errorPoly τ c w ≠ 0 ∧
        (p.1.errorPoly τ c w).eval p.2 = 0] ≤
      (q + 1) * ((n - 1 : Nat) / Fr.modulus) := by
  have hq' : OracleComp.IsTotalQueryBound (BlobBatchInput.toOpeningBatch <$> adversary) q := by
    rw [map_eq_bind_pure_comp, ← Nat.add_zero q]
    exact OracleComp.isTotalQueryBound_bind hq fun _ => trivial
  have hexp : batchRomExperiment (BlobBatchInput.toOpeningBatch <$> adversary) =
      Prod.map BlobBatchInput.toOpeningBatch id <$> blobInputRomExperiment adversary := by
    simp [batchRomExperiment, blobInputRomExperiment]
  have h := prEvent_batchErrorPoly_root_le τ (fun x i => c x.commitments[i]!)
    (fun x i => w x.proofs[i]!) (n := n) _ hq'
  rw [hexp, simulateQ_map, StateT.run'_map', prEvent_map] at h
  exact h

/-! ## Valid blob openings and completeness -/

/-- **The blob batch check accepts every batch of valid blob openings.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Take arrays of blobs, commitments and proofs of one size.

Let every entry be a valid blob opening at `τ`.

Then the batch check of blobs accepts. -/
theorem verifyBlobKzgProofBatch_of_blobOpeningValid (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {blobs : Array Blob} {commitments proofs : Array Bytes48}
    (hc : commitments.size = blobs.size) (hp : proofs.size = blobs.size)
    (hv : ∀ i < blobs.size, BlobOpeningValid τ blobs[i]! commitments[i]! proofs[i]!) :
    verifyBlobKzgProofBatch s blobs commitments proofs = .ok true := by
  let y : BlobBatchInput := ⟨blobs, commitments, proofs⟩
  have hblobs : ∀ blob ∈ blobs, ∃ poly, blobToPolynomial blob = .ok poly := fun blob hbl => by
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hbl
    obtain ⟨poly, -, -, -, -, hpoly, -⟩ := hv i hi
    exact ⟨poly, by rwa [getElem!_pos blobs i hi] at hpoly⟩
  have hcs : ∀ cb ∈ commitments, validateKzgG1 cb = true := fun cb hcb => by
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hcb
    obtain ⟨-, C, -, -, -, -, hCv, -⟩ := hv i (hc ▸ hi)
    rw [getElem!_pos commitments i hi] at hCv
    exact validateKzgG1_of_validateKzgG1Point hCv
  have hps : ∀ pb ∈ proofs, validateKzgG1 pb = true := fun pb hpb => by
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hpb
    obtain ⟨-, -, -, P, -, -, -, -, hPv, -⟩ := hv i (hp ▸ hi)
    rw [getElem!_pos proofs i hi] at hPv
    exact validateKzgG1_of_validateKzgG1Point hPv
  obtain ⟨b, hb⟩ := verifyBlobKzgProofBatch_exists_ok s hc hp hblobs hcs hps
  obtain ⟨ps, hpsM⟩ := array_mapM_exists_ok hblobs
  obtain ⟨hpssz, hpsk⟩ := array_mapM_ok hpsM
  have hdec : decodeBlobPolys blobs = ps := decodeBlobPolys_of_ok hpsM
  have hzero : y.errorPoly τ scalarOf scalarOf = 0 := by
    refine (batchErrorPoly_eq_zero_iff τ _ _ _ _ _).mpr fun i hi => ?_
    have hi' : i < blobs.size := hc ▸ hi
    obtain ⟨poly, C, c, P, w, hpoly, hCv, hCr, hPv, hPr, heq⟩ := hv i hi'
    have hpoly_eq : ps[i]! = poly := by
      have h1 := hpsk i hi' (by omega)
      rw [← getElem!_pos blobs i hi'] at h1
      rw [getElem!_pos ps i (by omega)]
      exact Except.ok.inj (h1.symm.trans hpoly)
    have hchal : y.challenges[i]! = computeChallenge blobs[i]! commitments[i]! := by
      rw [getElem!_pos y.challenges i (by simp [y, BlobBatchInput.challenges, hi'])]
      simp [y, BlobBatchInput.challenges, getElem!_pos blobs i hi']
    have heval : y.evals[i]! =
        (interpolant poly).eval (computeChallenge blobs[i]! commitments[i]!) := by
      rw [getElem!_pos y.evals i (by simp [y, BlobBatchInput.evals, hi'])]
      simp [y, BlobBatchInput.evals, hdec, hpoly_eq, hchal]
    rw [scalarOf_eq hCv hCr, scalarOf_eq hPv hPr, hchal, heval]
    exact heq
  have hroot := (verifyBlobKzgProofBatch_ok_iff_root laws hs y
    (fun i hi _ hu => represents_scalarOf
      (hcs y.commitments[i]! (getElem!_pos y.commitments i hi ▸ Array.getElem_mem hi)) hu)
    (fun i hi _ hu => represents_scalarOf
      (hps y.proofs[i]! (getElem!_pos y.proofs i hi ▸ Array.getElem_mem hi)) hu) hb).mpr
    (by rw [hzero, Polynomial.eval_zero])
  rw [hb, hroot]

/-- **The blob batch check accepts honestly computed commitments and proofs.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Take arrays of blobs, commitments and proofs of one size.

Let each commitment and proof come from `blobToKzgCommitment` and `computeBlobKzgProof`.

Then the batch check of blobs accepts. -/
theorem verifyBlobKzgProofBatch_computeBlobKzgProof (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {blobs : Array Blob} {commitments proofs : Array Bytes48}
    (hc : commitments.size = blobs.size) (hp : proofs.size = blobs.size)
    (hhonest : ∀ i < blobs.size, blobToKzgCommitment s blobs[i]! = .ok commitments[i]! ∧
      computeBlobKzgProof s blobs[i]! commitments[i]! = .ok proofs[i]!) :
    verifyBlobKzgProofBatch s blobs commitments proofs = .ok true :=
  verifyBlobKzgProofBatch_of_blobOpeningValid laws hs hc hp fun i hi =>
    blobOpeningValid_computeBlobKzgProof hs (hhonest i hi).1 (hhonest i hi).2

/-! ## Non-vacuity witness -/

/-- The all-zero blob, built as 4096 canonical encodings of zero. -/
private def zeroBlob : Blob :=
  (Vector.ofFn (n := FIELD_ELEMENTS_PER_BLOB) fun _ => blsFieldToBytes Fr.zero).flatten

/-- The all-zero blob decodes to 4096 zeros, without kernel evaluation of the array. -/
private theorem blobToPolynomial_zeroBlob :
    blobToPolynomial zeroBlob =
      .ok (Array.ofFn fun _ : Fin FIELD_ELEMENTS_PER_BLOB => Fr.zero) := by
  unfold blobToPolynomial zeroBlob
  refine bytesToBlsFields_eq_ok (k := FIELD_ELEMENTS_PER_BLOB) (fun _ => Fr.zero) fun i => ?_
  rw [fieldElementBytes_flatten]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, bytesToBlsField_blsFieldToBytes]

/-- **A non-empty honest batch of blobs exists and is accepted.**

Under the pairing law, every secret `τ` has a well-formed setup and a non-empty batch.

Its commitments and proofs are computed honestly, and the batch check of blobs accepts it. -/
theorem exists_honest_blob_batch (laws : Bls.PairingLaws) (τ : Fr) :
    ∃ (s : TrustedSetup) (y : BlobBatchInput),
      s.WellFormed τ ∧ y.blobs.size > 0 ∧
      (∀ i < y.blobs.size, blobToKzgCommitment s y.blobs[i]! = .ok y.commitments[i]! ∧
        computeBlobKzgProof s y.blobs[i]! y.commitments[i]! = .ok y.proofs[i]!) ∧
      verifyBlobKzgProofBatch s y.blobs y.commitments y.proofs = .ok true := by
  obtain ⟨C, P, hC, hP⟩ :=
    exists_blobToKzgCommitment_computeBlobKzgProof (wellFormed_ofPowers τ) blobToPolynomial_zeroBlob
  have hhonest : ∀ i < (#[zeroBlob]).size,
      blobToKzgCommitment (TrustedSetup.ofPowers (setupPowers τ)) (#[zeroBlob])[i]! =
        .ok (#[C])[i]! ∧
      computeBlobKzgProof (TrustedSetup.ofPowers (setupPowers τ)) (#[zeroBlob])[i]! (#[C])[i]! =
        .ok (#[P])[i]! := by
    intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    rw [getElem!_pos #[zeroBlob] 0 (Nat.zero_lt_one), getElem!_pos #[C] 0 (Nat.zero_lt_one),
      getElem!_pos #[P] 0 (Nat.zero_lt_one)]
    exact ⟨hC, hP⟩
  exact ⟨TrustedSetup.ofPowers (setupPowers τ), ⟨#[zeroBlob], #[C], #[P]⟩,
    wellFormed_ofPowers τ, Nat.zero_lt_one, hhonest,
    verifyBlobKzgProofBatch_computeBlobKzgProof laws (wellFormed_ofPowers τ) rfl rfl hhonest⟩

/-- Both entries of an array of two equal elements are that element. -/
private theorem getElem!_pair {α : Type} [Inhabited α] (a : α) {i : Nat} (hi : i < 2) :
    (#[a, a])[i]! = a := by
  interval_cases i <;> rfl

/-- For an adversary that outputs a fixed batch, the batch challenge is uniform. -/
private theorem prEvent_blobInputRomExperiment_pure (y : BlobBatchInput)
    (E : BlobBatchInput × Fr → Prop) :
    Pr{let p ← (simulateQ OracleSpec.randomOracle (blobInputRomExperiment (pure y))).run' ∅}[
        E p] = Pr{let u ← $ᵗ Fr}[E (y, u)] := by
  simp only [blobInputRomExperiment, pure_bind, simulateQ_bind, simulateQ_pure, simulateQ_query,
    StateT.run'_eq, StateT.run_bind, StateT.run_map, randomOracle.run_eq,
    OracleSpec.QueryCache.empty_apply]
  simp only [map_bind, bind_assoc, pure_bind, StateT.run_pure, map_pure]
  rfl

/-- **A zero-query adversary reaches the root case, and the bound is tight there.**

The adversary outputs two all-zero blobs.

Each has `[1]_1` as its commitment and `[0]_1` as its proof.

With each scalar the scalar of its bytes, each entry has the error `1 - 0 - 0 = 1`.

So the error polynomial of the batch is `1 + X`, which is not zero and has the root `-1`.

The batch challenge is uniform, so the event of the bound has probability exactly `1 / r`.

That is the bound at `q = 0` and `n = 2`, which is `(0 + 1) (2 - 1) / r`. -/
theorem exists_blobInput_adversary_prEvent_root_eq (τ : Fr) :
    ∃ (adversary : OracleComp (OpeningBatch →ₒ Fr) BlobBatchInput) (y : BlobBatchInput),
      adversary = pure y ∧
      OracleComp.IsTotalQueryBound adversary 0 ∧
      y.commitments.size = 2 ∧
      (∀ i < y.commitments.size, ∀ P, uncompressG1 y.commitments[i]! = .ok P →
        G1.Represents P (scalarOf y.commitments[i]!)) ∧
      (∀ i < y.proofs.size, ∀ P, uncompressG1 y.proofs[i]! = .ok P →
        G1.Represents P (scalarOf y.proofs[i]!)) ∧
      y.errorPoly τ scalarOf scalarOf ≠ 0 ∧
      Pr{let p ← (simulateQ OracleSpec.randomOracle (blobInputRomExperiment adversary)).run' ∅}[
          p.1.commitments.size ≤ 2 ∧ p.1.errorPoly τ scalarOf scalarOf ≠ 0 ∧
          (p.1.errorPoly τ scalarOf scalarOf).eval p.2 = 0] =
        1 / Fr.modulus := by
  obtain ⟨Cg, hCg, hrCg⟩ := validateKzgG1Point_compressG1 G1.represents_generator
  obtain ⟨Cz, hCz, hrCz⟩ := validateKzgG1Point_compressG1 (G1.represents_mul_generator 0)
  let y : BlobBatchInput :=
    ⟨#[zeroBlob, zeroBlob], #[compressG1 G1.generator, compressG1 G1.generator],
      #[compressG1 (G1.mul G1.generator 0), compressG1 (G1.mul G1.generator 0)]⟩
  have hC : ∀ i < y.commitments.size, ∀ P, uncompressG1 y.commitments[i]! = .ok P →
      G1.Represents P (scalarOf y.commitments[i]!) := fun i hi P hP => by
    rw [getElem!_pair _ hi] at hP ⊢
    exact represents_scalarOf (validateKzgG1_of_validateKzgG1Point hCg) hP
  have hP : ∀ i < y.proofs.size, ∀ P, uncompressG1 y.proofs[i]! = .ok P →
      G1.Represents P (scalarOf y.proofs[i]!) := fun i hi P hP => by
    rw [getElem!_pair _ hi] at hP ⊢
    exact represents_scalarOf (validateKzgG1_of_validateKzgG1Point hCz) hP
  -- Each blob decodes to zeros, so each value at its evaluation challenge is zero.
  obtain ⟨ps, hpsM⟩ := array_mapM_exists_ok (f := blobToPolynomial) (xs := y.blobs) fun bl hbl => by
    obtain rfl : bl = zeroBlob := by simpa [y] using hbl
    exact ⟨_, blobToPolynomial_zeroBlob⟩
  obtain ⟨hpssz, hpsk⟩ := array_mapM_ok hpsM
  have hdec : decodeBlobPolys y.blobs = ps := decodeBlobPolys_of_ok hpsM
  have heval : ∀ i < 2, y.evals[i]! = 0 := fun i hi => by
    have hpsi : ps[i]! = Array.ofFn fun _ : Fin FIELD_ELEMENTS_PER_BLOB => Fr.zero := by
      have hi2 : i < y.blobs.size := hi
      have hj : i < ps.size := by rw [hpssz]; exact hi2
      have h0 := hpsk i hi2 hj
      rw [← getElem!_pos y.blobs i hi2, ← getElem!_pos ps i hj] at h0
      rw [getElem!_pair _ hi] at h0
      exact Except.ok.inj (h0.symm.trans blobToPolynomial_zeroBlob)
    have hinterp : interpolant ps[i]! = 0 := by
      rw [interpolant, Lagrange.interpolate_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hpsi, getElem!_pos _ j.val (by simp [j.isLt])]
      simp
    rw [getElem!_pos y.evals i (by simpa [y, BlobBatchInput.evals] using hi)]
    simp [BlobBatchInput.evals, hdec, hinterp]
  -- Each entry has the error `1`, so the error polynomial takes the value `1 + r` at `r`.
  have herr : ∀ r : Fr, (y.errorPoly τ scalarOf scalarOf).eval r = 1 + r := fun r => by
    have hent : ∀ i < 2, openingError τ (scalarOf y.commitments[i]!) y.evals[i]!
        (scalarOf y.proofs[i]!) y.challenges[i]! = 1 := fun i hi => by
      rw [getElem!_pair _ hi, getElem!_pair _ hi, heval i hi, scalarOf_eq hCg hrCg,
        scalarOf_eq hCz hrCz, openingError, sub_zero, zero_mul, sub_zero]
    rw [BlobBatchInput.errorPoly, eval_batchErrorPoly, show y.commitments.size = 2 from rfl,
      Finset.sum_range_succ, Finset.sum_range_one, hent 0 (by decide), hent 1 (by decide)]
    ring
  have hne : y.errorPoly τ scalarOf scalarOf ≠ 0 := fun h0 => by
    simpa [h0] using herr 0
  refine ⟨pure y, y, rfl, trivial, rfl, hC, hP, hne, ?_⟩
  -- The single query of the verifier is fresh, so the batch challenge is uniform.
  have hsize : y.commitments.size = 2 := rfl
  clear_value y
  have hiff : ∀ u : Fr, (y.commitments.size ≤ 2 ∧ y.errorPoly τ scalarOf scalarOf ≠ 0 ∧
      (y.errorPoly τ scalarOf scalarOf).eval u = 0) ↔ u = -1 := fun u => by
    rw [herr, hsize, add_eq_zero_iff_neg_eq, eq_comm]
    exact ⟨fun h => h.2.2, fun h => ⟨le_refl 2, hne, h⟩⟩
  rw [prEvent_blobInputRomExperiment_pure]
  simp only [hiff]
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Bls.Fr.card_eq, one_div]

end EthLib.Cryptography.Kzg
