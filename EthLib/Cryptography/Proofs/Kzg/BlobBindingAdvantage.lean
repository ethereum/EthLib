module

public import EthLib.Cryptography.Proofs.Kzg.BlobBindingSecurity
public import EthLib.Cryptography.Proofs.Kzg.BlobBindingRom
public import EthLib.Cryptography.Proofs.Kzg.BlobBindingVerifier

set_option autoImplicit false

/-!
# Proofs: the algebraic blob-batch binding bound

The adversary receives public setup powers and supplies polynomial representations.

It shares one cached oracle with the verifier.

The oracle has two typed input domains and uniform answers in `Fr`.

The experiment rejects final batches above `n` blobs before verification.

The adversary makes at most `qBlob` individual queries.

It makes at most `qBatch` batch queries.

The root bound is `(qBlob + n) 4095 / r + (qBatch + 1) (n - 1) / r`, where `r` is the order of `Fr`.

Add the success probability of a named reduction that recovers the setup secret.

Recovery is measured from the full public setup powers.

The reduction searches roots of explicit polynomials; its running time is not formalized.

A separate equivalence connects the equation to the concrete verifier.

That equivalence uses concrete challenges; the probability bound uses the idealized oracle.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.BlobBinding

open EthLib.Cryptography.Bls (Fr)
open OracleComp OracleSpec ENNReal MeasureTheory
open scoped EthLib.Cryptography.Bls.Fr

/-- Acceptance of a valid batch containing a commitment different from its blob's commitment. -/
def BindingWins (n : Nat) (τ : Fr) (result : Outcome) : Prop :=
  result.1.1.length ≤ n ∧ Validated result.1.1 ∧ Nonbinding τ result.1.1 ∧
    Accepted τ result.1.2

/-- All group representations supplied by the adversary are correct at the hidden setup secret. -/
def AlgebraicAdversary (n : Nat)
    (adversary : SetupPowers → OracleComp Spec (List BlobOpening)) : Prop :=
  ∀ τ result, result ∈ MonadAttach.support (run (boundedExperiment n (adversary (setupPowers τ)))) →
    Algebraic τ result.1.1 result.2

/-- The binding advantage, with a uniform setup secret and one shared random oracle. -/
noncomputable def blobBindingAdvantage (n : Nat)
    (adversary : SetupPowers → OracleComp Spec (List BlobOpening)) : ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let result ← run (boundedExperiment n (adversary (setupPowers τ)))}[
    BindingWins n τ result]

/-- Blob-batch binding reduces to fresh challenge roots or recovery of the setup secret.

The adversary is algebraic: each point that decodes carries a representation correct at the secret.

This hypothesis stands for the algebraic group model, an assumption.

Nothing restricts how the adversary computes its representations.

The individual and batch budgets count the adversary's queries, including repeated inputs.

The verifier adds at most `n` individual queries and one batch query. -/
theorem blobBindingAdvantage_le (n qBlob qBatch : Nat)
    (adversary : SetupPowers → OracleComp Spec (List BlobOpening))
    (halgebraic : AlgebraicAdversary n adversary)
    (hblob : ∀ pw, IsQueryBoundP (adversary pw) (fun q => isBlobQuery q = true) qBlob)
    (hbatch : ∀ pw, IsQueryBoundP (adversary pw) (fun q => isBatchQuery q = true) qBatch) :
    blobBindingAdvantage n adversary ≤
      (qBlob + n : Nat) * blobRootWeight + (qBatch + 1 : Nat) * batchRootWeight n +
        setupSecretAdvantage (setupSecretReduction n adversary) := by
  let _ : MeasurableSpace Fr := ⊤
  have _ : DiscreteMeasurableSpace Fr := ⟨fun _ => trivial⟩
  let bound : ℝ≥0∞ :=
    (qBlob + n : Nat) * blobRootWeight + (qBatch + 1 : Nat) * batchRootWeight n
  have hpoint (τ : Fr) :
      Pr{let result ← run (boundedExperiment n (adversary (setupPowers τ)))}[
        BindingWins n τ result] ≤ bound +
      Pr{let result ← run (boundedExperiment n (adversary (setupPowers τ)))}[
        setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ] := by
    refine (prEvent_mono_of_support _ _
      (fun result => (result.2.BadBlob ∨ result.2.BadBatch n) ∨
        setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ)
      ?_).trans ((prEvent_or_le _ _ _).trans ?_)
    · intro result hs hw
      have hwin : Wins n τ result :=
        ⟨hw.1, halgebraic τ result hs, hw.2.1, hw.2.2.1, hw.2.2.2⟩
      exact or_assoc.mpr (wins_imp_root_or_setupSecret hs hwin)
    · exact _root_.add_le_add (prEvent_run_roots_le n _
        (boundedExperiment_blobQueries n (hblob (setupPowers τ)))
        (boundedExperiment_batchQueries n (hbatch (setupPowers τ)))) le_rfl
  rw [blobBindingAdvantage, setupSecretAdvantage_setupSecretReduction,
    prEvent_bind_bind_eq_lintegral_of_discrete, prEvent_bind_bind_eq_lintegral_of_discrete]
  calc
    _ ≤ ∫⁻ τ, bound + Pr{let result ← run (boundedExperiment n (adversary (setupPowers τ)))}[
        setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ]
        ∂𝒟[($ᵗ Fr)] := lintegral_mono hpoint
    _ = bound * 𝒟[($ᵗ Fr)] Set.univ +
        ∫⁻ τ, Pr{let result ← run (boundedExperiment n (adversary (setupPowers τ)))}[
          setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ]
          ∂𝒟[($ᵗ Fr)] := by rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ _ := _root_.add_le_add
      (mul_le_of_le_one_right' (evalDist_apply_univ_le_one ($ᵗ Fr))) le_rfl

end EthLib.Cryptography.Kzg.BlobBinding
