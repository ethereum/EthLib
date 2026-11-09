module

public import EthLib.Cryptography.Proofs.Kzg.BlobBindingGame
public import EthLib.Cryptography.Proofs.Kzg.BlobBindingReduction
import EthLib.Cryptography.Proofs.Bls.SignaturesUnique

set_option autoImplicit false

/-!
# Proofs: binding of blob batches in the algebraic random-oracle model

An accepted nonbinding algebraic batch hits a fresh challenge root or yields the setup secret.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.BlobBinding

open EthLib.Cryptography.Bls (Fr G1)
open OracleComp OracleSpec ENNReal Polynomial
open scoped EthLib.Cryptography.Bls.Fr

private theorem polynomialDifference_eq_zero_iff (a b : Fr[X]) :
    polynomialDifference a b = 0 ↔ a = b := sub_eq_zero

private theorem eval_polynomialDifference (a b : Fr[X]) (x : Fr) :
    (polynomialDifference a b).eval x = a.eval x - b.eval x := eval_sub a b x

/-- A validated commitment to the interpolant is the commitment computed from the blob. -/
theorem blobToKzgCommitment_eq_of_represents {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {blob : Blob} {values : Polynomial} {bytes : Bytes48} {point : G1}
    (hblob : blobToPolynomial blob = .ok values)
    (hpoint : validateKzgG1Point bytes = .ok point)
    (hrep : G1.Represents point ((interpolant values).eval τ)) :
    blobToKzgCommitment s blob = .ok bytes := by
  obtain ⟨hcommit, hsum⟩ := blobToKzgCommitment_represents hs hblob
  have heq := G1.compress_congr hsum.1 hrep.1 (hsum.2.trans hrep.2.symm)
  have hround := G1.compress_uncompress (validateKzgG1Point_eq_ok_iff.mp hpoint).1
  have hbytes : compressG1 (G1.msm s.g1LagrangeBrp.toArray values) = bytes := by
    apply Vector.toArray_inj.mp
    exact congrArg ByteArray.data (heq.trans hround)
  exact hbytes ▸ hcommit

/-- The output encodings pass the same point validation as the blob verifier. -/
def Validated (out : List BlobOpening) : Prop :=
  ∀ o ∈ out, validateKzgG1 o.commitment.bytes = true ∧ validateKzgG1 o.proof.bytes = true

/-- At least one submitted commitment differs from the commitment computed from its blob. -/
def Nonbinding (τ : Fr) (out : List BlobOpening) : Prop :=
  ∃ o ∈ out, blobToKzgCommitment (TrustedSetup.ofPowers (setupPowers τ)) o.blob ≠
    .ok o.commitment.bytes

/-- The scalar batch verification equation at the oracle challenges. -/
def Accepted (τ : Fr) (checked : Option (List Opening × Fr)) : Prop :=
  ∃ openings r, checked = some (openings, r) ∧ (batchErrorAt openings r).eval τ = 0

/-- An algebraic adversary wins with an accepted nonbinding batch within the size budget. -/
def Wins (n : Nat) (τ : Fr) (result : Outcome) : Prop :=
  let out := result.1.1
  out.length ≤ n ∧ Algebraic τ out result.2 ∧ Validated out ∧ Nonbinding τ out ∧
    Accepted τ result.1.2

/-- The verifier's openings retain their submitted points and the decoded blob values. -/
def Matches : List BlobOpening → List Opening → Prop
  | [], [] => True
  | out :: outputs, o :: openings =>
    o.commitment = out.commitment ∧ o.proof = out.proof ∧
      (∃ values, blobToPolynomial out.blob = .ok values ∧
        o.y = (interpolant values).eval o.z) ∧ Matches outputs openings
  | _, _ => False

/-- Successful challenge generation preserves the submitted points and blob evaluations. -/
theorem matches_of_mem_support_challengeOpenings (out : List BlobOpening)
    {openings : List Opening} (h : some openings ∈ MonadAttach.support (challengeOpenings out)) :
    Matches out openings := by
  induction out generalizing openings with
  | nil =>
    change some openings ∈ MonadAttach.support
      (pure (some []) : OracleComp Spec (Option (List Opening))) at h
    have heq := OracleComp.eq_of_mem_support_pure (some ([] : List Opening)) h
    cases Option.some.inj heq
    trivial
  | cons o out ih =>
    rw [challengeOpenings_cons] at h
    cases hb : blobToPolynomial o.blob with
    | error e =>
      rw [hb, challengeDecoded_error] at h
      have heq := OracleComp.eq_of_mem_support_pure (none : Option (List Opening)) h
      cases heq
    | ok values =>
      rw [hb, challengeDecoded_ok] at h
      obtain ⟨z, _, hrest⟩ := OracleComp.mem_support_bind_peel _ _ h
      obtain ⟨rest, hr, hpure⟩ := OracleComp.mem_support_bind_peel _ _ hrest
      have heq := OracleComp.eq_of_mem_support_pure _ hpure
      cases rest with
      | none => cases heq
      | some rest =>
        cases heq
        exact ⟨rfl, rfl, ⟨values, hb, rfl⟩, ih hr⟩

/-- Challenge generation has one opening per submitted blob. -/
theorem Matches.length {out : List BlobOpening} {openings : List Opening}
    (h : Matches out openings) : openings.length = out.length := by
  induction out generalizing openings with
  | nil => cases openings <;> simp_all [Matches]
  | cons o out ih =>
    cases openings with
    | nil => cases h
    | cons opening openings => exact congrArg Nat.succ (ih h.2.2.2)

/-- The verifier does not change the submitted group representations. -/
theorem Matches.points {out : List BlobOpening} {openings : List Opening}
    (h : Matches out openings) : Request.points (.batch openings) = BlobOpening.points out := by
  induction out generalizing openings with
  | nil => cases openings <;> simp_all [Matches, Request.points, BlobOpening.points]
  | cons o out ih =>
    cases openings with
    | nil => cases h
    | cons opening openings =>
      change [opening.commitment, opening.proof] ++ Request.points (.batch openings) =
        [o.commitment, o.proof] ++ BlobOpening.points out
      rw [h.1, h.2.1, ih h.2.2.2]

/-- Matching openings retain the submitted point-validation results. -/
theorem Matches.validated {out : List BlobOpening} {openings : List Opening}
    (h : Matches out openings) (hv : Validated out) :
    ∀ o ∈ openings, validateKzgG1 o.commitment.bytes = true ∧
      validateKzgG1 o.proof.bytes = true := by
  induction out generalizing openings with
  | nil => cases openings <;> simp_all [Matches]
  | cons a out ih =>
    cases openings with
    | nil => cases h
    | cons opening openings =>
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · simpa [h.1, h.2.1] using hv a (by simp)
      · exact ih h.2.2.2 (fun p hp => hv p (by simp [hp])) o ho

/-- Repeated batch inputs have the same symbolic polynomial unless representations conflict. -/
theorem batchError_eq_of_data_eq {out : List BlobOpening} {s : State}
    (hc : Consistent out s) {left right : List Opening}
    (hl : ∀ p ∈ Request.points (.batch left), p ∈ allPoints out s)
    (hr : ∀ p ∈ Request.points (.batch right), p ∈ allPoints out s)
    (hv : ∀ o ∈ right, validateKzgG1 o.commitment.bytes = true ∧
      validateKzgG1 o.proof.bytes = true)
    (heq : left.map Opening.data = right.map Opening.data) :
    batchError left = batchError right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons a left ih =>
    cases right with
    | nil => simp at heq
    | cons b right =>
      obtain ⟨hab, htail⟩ := List.cons.inj heq
      have hCbytes := congrArg OpeningData.commitment hab
      have hPbytes := congrArg OpeningData.proof hab
      change a.commitment.bytes = b.commitment.bytes at hCbytes
      change a.proof.bytes = b.proof.bytes at hPbytes
      have hC : a.commitment.polynomial = b.commitment.polynomial :=
        hc _ (hl _ (by simp [Request.points])) _ (hr _ (by simp [Request.points]))
          hCbytes (by simpa only [hCbytes] using (hv b (by simp)).1)
      have hP : a.proof.polynomial = b.proof.polynomial :=
        hc _ (hl _ (by simp [Request.points])) _ (hr _ (by simp [Request.points]))
          hPbytes (by simpa only [hPbytes] using (hv b (by simp)).2)
      have hz := congrArg OpeningData.z hab
      have hy := congrArg OpeningData.y hab
      have herr : a.error = b.error := by
        simp only [Opening.error, hC, hP, show a.z = b.z from hz, show a.y = b.y from hy]
      rw [batchError, batchError, herr,
        ih (fun p hp => hl p (List.mem_append_right _ hp))
        (fun p hp => hr p (List.mem_append_right _ hp))
        (fun o ho => hv o (by simp [ho])) htail]

/-- A commitment different from the blob's computed commitment has a nonzero difference. -/
theorem blobError_ne_zero_of_nonbinding {τ : Fr} {o : BlobOpening} {values : Polynomial}
    (hb : blobToPolynomial o.blob = .ok values)
    (hv : validateKzgG1 o.commitment.bytes = true) (ha : o.commitment.Valid τ)
    (hne : blobToKzgCommitment (TrustedSetup.ofPowers (setupPowers τ)) o.blob ≠
      .ok o.commitment.bytes) : blobError o.blob o.commitment ≠ 0 := by
  intro hzero
  have heq : o.commitment.polynomial = interpolant values := by
    rw [blobError_of_ok o.commitment hb] at hzero
    exact (polynomialDifference_eq_zero_iff _ _).mp hzero
  obtain ⟨P, hP⟩ := exists_validateKzgG1Point_of_validateKzgG1 hv
  apply hne
  apply blobToKzgCommitment_eq_of_represents (wellFormed_ofPowers τ) hb hP
  simpa only [← heq] using ha P hP

/-- A zero opening error makes its individual challenge a root of the blob difference. -/
theorem eval_blobError_eq_zero {o : BlobOpening} {opening : Opening} {values : Polynomial}
    (hb : blobToPolynomial o.blob = .ok values) (hc : opening.commitment = o.commitment)
    (hy : opening.y = (interpolant values).eval opening.z) (he : opening.error = 0) :
    (blobError o.blob o.commitment).eval opening.z = 0 := by
  rw [blobError_of_ok o.commitment hb, eval_polynomialDifference]
  have hz := congrArg (fun p : Fr[X] => p.eval opening.z) he
  simpa only [Opening.error, eval_blobOpeningError, eval_zero, hc, hy] using hz

/-- A submitted blob and its matching opening have the same logged individual challenge. -/
theorem Matches.exists_queried_opening {out : List BlobOpening} {openings : List Opening}
    {s : State} (hm : Matches out openings) (hq : QueriedBlobs s out openings)
    {o : BlobOpening} (ho : o ∈ out) :
    ∃ opening ∈ openings, opening.commitment = o.commitment ∧
      (∃ values, blobToPolynomial o.blob = .ok values ∧
        opening.y = (interpolant values).eval opening.z) ∧
      ∃ fresh, ⟨.blob o.blob o.commitment, opening.z, fresh⟩ ∈ s.history := by
  induction out generalizing openings with
  | nil => cases ho
  | cons a out ih =>
    cases openings with
    | nil => cases hm
    | cons opening openings =>
      rcases List.mem_cons.mp ho with rfl | ho
      · exact ⟨opening, by simp, hm.1, hm.2.2.1, hq.1⟩
      · obtain ⟨opening', hmem, hrest⟩ := ih hm.2.2.2 hq.2 ho
        exact ⟨opening', List.mem_cons_of_mem _ hmem, hrest⟩

/-- A replayed individual root is already present at the first response to that input. -/
theorem badBlob_of_queried_root {out : List BlobOpening} {s : State}
    (hs : s.Coherent) (hc : Consistent out s) {o : BlobOpening} (ho : o ∈ out)
    (hv : validateKzgG1 o.commitment.bytes = true) {z : Fr} {fresh : Bool}
    (hq : ⟨.blob o.blob o.commitment, z, fresh⟩ ∈ s.history)
    (hne : blobError o.blob o.commitment ≠ 0)
    (hroot : (blobError o.blob o.commitment).eval z = 0) : s.BadBlob := by
  obtain ⟨first, hf, hfresh, hkey, hans⟩ := State.fresh_reply hs hq
  cases hr : first.request with
  | batch openings => simp [hr, Request.key] at hkey
  | blob b commitment =>
    obtain ⟨hb, hbytes⟩ := HashKey.blob.inj (by simpa [hr, Request.key] using hkey)
    have hp : commitment ∈ allPoints out s := by
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      exact ⟨first, hf, by simp [hr, Request.points]⟩
    have hop : o.commitment ∈ allPoints out s := by
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨o, ho, by simp⟩
    have hpoly := hc _ hp _ hop hbytes (by simpa only [hbytes] using hv)
    have herr : blobError b commitment = blobError o.blob o.commitment := by
      subst b
      cases hdecoded : blobToPolynomial o.blob with
      | error error => rw [blobError_of_error _ hdecoded, blobError_of_error _ hdecoded]
      | ok values => rw [blobError_of_ok _ hdecoded, blobError_of_ok _ hdecoded, hpoly]
    exact ⟨first, hf, hfresh, by simpa [hr, herr, hans] using And.intro hne hroot⟩

/-- A replayed symbolic batch root is already present at the first response to that input. -/
theorem badBatch_of_queried_root {n : Nat} {out : List BlobOpening} {s : State}
    (hs : s.Coherent) (hc : Consistent out s) {openings : List Opening} {r : Fr}
    (hm : Matches out openings) (hv : Validated out) (hlen : openings.length ≤ n)
    {fresh : Bool} (hq : ⟨.batch openings, r, fresh⟩ ∈ s.history)
    (hne : batchError openings ≠ 0) (hroot : batchErrorAt openings r = 0) :
    s.BadBatch n := by
  obtain ⟨first, hf, hfresh, hkey, hans⟩ := State.fresh_reply hs hq
  cases hr : first.request with
  | blob b commitment => simp [hr, Request.key] at hkey
  | batch previous =>
    have hdata : previous.map Opening.data = openings.map Opening.data :=
      HashKey.batch.inj (by simpa [hr, Request.key] using hkey)
    have herr : batchError previous = batchError openings := by
      apply batchError_eq_of_data_eq hc
      · intro p hp
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨first, hf, by simpa [hr] using hp⟩)
      · intro p hp
        exact List.mem_append_right _ (hm.points ▸ hp)
      · exact hm.validated hv
      · exact hdata
    have hlength : previous.length = openings.length := by
      simpa using congrArg List.length hdata
    refine ⟨first, hf, hfresh, ?_⟩
    simpa only [hr, Reply.BadBatch, hans, hlength, herr, batchErrorAt] using
      And.intro hlen (And.intro hne hroot)

/-- A successful verifier output contains the submitted blobs' matching openings. -/
theorem matches_of_mem_support_verifierQueries (out : List BlobOpening)
    {s final : State} {openings : List Opening} {r : Fr}
    (h : (some (openings, r), final) ∈
      MonadAttach.support ((simulateQ impl (verifierQueries out)).run s)) :
    Matches out openings := by
  have hs : some (openings, r) ∈ MonadAttach.support (verifierQueries out) := by
    apply support_simulateQ_run'_subset impl (verifierQueries out) s
    rw [StateT.run'_eq, MonadAttach.support_map]
    exact Set.mem_image_of_mem _ h
  unfold verifierQueries at hs
  obtain ⟨checked, hc, hrest⟩ := OracleComp.mem_support_bind_peel _ _ hs
  cases checked with
  | none => cases OracleComp.eq_of_mem_support_pure _ hrest
  | some os =>
    obtain ⟨answer, _, hpure⟩ := OracleComp.mem_support_bind_peel _ _ hrest
    have heq := OracleComp.eq_of_mem_support_pure _ hpure
    cases heq
    exact matches_of_mem_support_challengeOpenings out hc

/-- A successful capped experiment includes a supported run of the verifier on its output. -/
theorem verifier_support_of_mem_support_boundedExperiment {n : Nat}
    {adversary : OracleComp Spec (List BlobOpening)} {out : List BlobOpening}
    {openings : List Opening} {r : Fr} {final : State}
    (h : ((out, some (openings, r)), final) ∈
      MonadAttach.support (run (boundedExperiment n adversary))) :
    ∃ s, (some (openings, r), final) ∈
      MonadAttach.support ((simulateQ impl (verifierQueries out)).run s) := by
  simp only [run, boundedExperiment, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at h
  obtain ⟨⟨out', before⟩, _, h⟩ := h
  dsimp only at h
  by_cases hsize : out'.length ≤ n
  · rw [ite_eq_left hsize] at h
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨⟨checked, final'⟩, hc, heq⟩ := h
    cases heq
    exact ⟨before, hc⟩
  · rw [ite_eq_right hsize] at h
    simp [simulateQ_pure, StateT.run_pure] at h

/-- An accepted nonbinding algebraic output hits oracle roots or yields the setup secret. -/
theorem wins_imp_root_or_setupSecret {n : Nat} {τ : Fr}
    {adversary : OracleComp Spec (List BlobOpening)} {result : Outcome}
    (hsupport : result ∈ MonadAttach.support (run (boundedExperiment n adversary)))
    (hw : Wins n τ result) :
    result.2.BadBlob ∨ result.2.BadBatch n ∨
      setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ := by
  classical
  rcases result with ⟨⟨out, checked⟩, final⟩
  obtain ⟨hn, ha, hv, hwrong, openings, r, hchecked, hroot⟩ := hw
  change checked = some (openings, r) at hchecked
  subst checked
  by_cases hconsistent : Consistent out final
  · by_cases herror : batchErrorAt openings r = 0
    · obtain ⟨before, hverifier⟩ := verifier_support_of_mem_support_boundedExperiment
        hsupport
      have hm := matches_of_mem_support_verifierQueries out hverifier
      obtain ⟨hq, fresh, hbatch⟩ := queried_of_mem_support_verifierQueries out hverifier
      by_cases hbatchzero : batchError openings = 0
      · obtain ⟨o, ho, hne⟩ := hwrong
        obtain ⟨opening, hopening, hc, ⟨values, hb, hy⟩, fresh, hquery⟩ :=
          hm.exists_queried_opening hq ho
        have hvalid := (hv o ho).1
        have halgebraic : o.commitment.Valid τ :=
          ha.2 _ (List.mem_flatMap.mpr ⟨o, ho, by simp⟩)
        have hnonzero := blobError_ne_zero_of_nonbinding hb hvalid halgebraic hne
        have hzero := (batchError_eq_zero_iff openings).mp hbatchzero opening hopening
        exact Or.inl (badBlob_of_queried_root (run_coherent hsupport) hconsistent ho
          hvalid hquery hnonzero (eval_blobError_eq_zero hb hc hy hzero))
      · exact Or.inr (Or.inl (badBatch_of_queried_root (run_coherent hsupport) hconsistent
          hm hv (hm.length.trans_le hn) hbatch hbatchzero herror))
    · exact Or.inr (Or.inr (setupSecretRootSearch_eq_some_of_mem_candidatePolynomials
        (batchErrorAt_mem_candidatePolynomials rfl) herror hroot))
  · exact Or.inr (Or.inr (setupSecretRootSearch_eq_some_of_not_consistent ha hconsistent))

end EthLib.Cryptography.Kzg.BlobBinding
