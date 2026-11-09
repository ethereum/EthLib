module

public import EthLib.Cryptography.Proofs.Kzg.BlobBindingGame
public import EthLib.Cryptography.Proofs.Kzg.BlobSecret

set_option autoImplicit false

/-!
# Proofs: reduce blob binding to recovery of the setup secret

The reduction runs the adversary and verifier with one shared random-oracle cache.

It searches roots of representation differences and of the final batch error.

Its input contains the public setup powers, never the secret.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.BlobBinding

open EthLib.Cryptography.Bls (Fr)
open OracleComp OracleSpec ENNReal Polynomial
open scoped EthLib.Cryptography.Bls.Fr

/-- Run the adversary, then reject a final batch above the size budget before verification. -/
noncomputable def boundedExperiment (n : Nat)
    (adversary : OracleComp Spec (List BlobOpening)) :
    OracleComp Spec (List BlobOpening × Option (List Opening × Fr)) := do
  let out ← adversary
  let checked ← if out.length ≤ n then verifierQueries out else pure none
  return (out, checked)

/-- The result and public transcript of one size-budgeted experiment. -/
abbrev Outcome := (List BlobOpening × Option (List Opening × Fr)) × State

/-- Representation differences and the final batch error, when challenge generation succeeds. -/
noncomputable def candidatePolynomials (result : Outcome) : List Fr[X] :=
  representationDifferences (allPoints result.1.1 result.2) ++ match result.1.2 with
    | none => []
    | some (openings, r) => [batchErrorAt openings r]

/-- Every representation difference is a candidate for extraction. -/
theorem mem_candidatePolynomials_of_mem_representationDifferences {result : Outcome} {p : Fr[X]}
    (hp : p ∈ representationDifferences (allPoints result.1.1 result.2)) :
    p ∈ candidatePolynomials result :=
  List.mem_append_left _ hp

/-- A generated batch error is a candidate for extraction. -/
theorem batchErrorAt_mem_candidatePolynomials {result : Outcome} {openings : List Opening} {r : Fr}
    (h : result.1.2 = some (openings, r)) :
    batchErrorAt openings r ∈ candidatePolynomials result := by
  simp [candidatePolynomials, h]

/-- A nonzero candidate rooted at the secret makes the search recover it. -/
theorem setupSecretRootSearch_eq_some_of_mem_candidatePolynomials {τ : Fr} {result : Outcome}
    {p : Fr[X]} (hp : p ∈ candidatePolynomials result) (hp0 : p ≠ 0) (hroot : p.eval τ = 0) :
    setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ :=
  setupSecretRootSearch_eq_some hp hp0 hroot

/-- Conflicting valid representations of one encoding make the search recover the secret. -/
theorem setupSecretRootSearch_eq_some_of_not_consistent {τ : Fr} {result : Outcome}
    (ha : Algebraic τ result.1.1 result.2) (hc : ¬Consistent result.1.1 result.2) :
    setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ := by
  obtain ⟨p, hp, hp0, hroot⟩ := root_of_not_consistent ha hc
  exact setupSecretRootSearch_eq_some_of_mem_candidatePolynomials
    (mem_candidatePolynomials_of_mem_representationDifferences hp) hp0 hroot

/-- Run the size-budgeted experiment once and search its polynomial roots using the public setup. -/
noncomputable def setupSecretReduction (n : Nat)
    (adversary : SetupPowers → OracleComp Spec (List BlobOpening)) :
    SetupPowers → ProbComp (Option Fr) :=
  fun pw => (fun result => setupSecretRootSearch pw (candidatePolynomials result)) <$>
    run (boundedExperiment n (adversary pw))

/-- The reduction's success probability observes the same experiment and transcript. -/
theorem setupSecretAdvantage_setupSecretReduction (n : Nat)
    (adversary : SetupPowers → OracleComp Spec (List BlobOpening)) :
    setupSecretAdvantage (setupSecretReduction n adversary) =
      Pr{let τ ← $ᵗ Fr; let result ← run (boundedExperiment n (adversary (setupPowers τ)))}[
        setupSecretRootSearch (setupPowers τ) (candidatePolynomials result) = some τ] := by
  simp only [setupSecretAdvantage, setupSecretReduction, Functor.map_map]

end EthLib.Cryptography.Kzg.BlobBinding
