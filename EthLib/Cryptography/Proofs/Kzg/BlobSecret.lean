module

public import EthLib.Cryptography.Proofs.Kzg.Commitment
public import EthLib.Cryptography.Proofs.Kzg.BatchChallenge

/-!
# Proofs: recover the setup secret from polynomial roots

A nonzero polynomial that vanishes at the setup secret contains it among its roots.

The public first monomial point identifies which root is the secret.

The search receives only the setup powers and a finite list of polynomials, never the secret.

The candidate count is at most the sum of the polynomial degrees.

Root finding uses Mathlib's mathematical root operation.

The running time of factoring and of the search is not formalized.

The advantage below concerns recovery from the whole setup, including its higher powers.

No equivalence to discrete logarithm from a single group element is asserted.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr G1)
open Polynomial OracleComp ENNReal
open scoped EthLib.Cryptography.Bls.Fr

/-- The roots of the candidate polynomials, with multiplicity. -/
noncomputable def setupSecretCandidates (polys : List Fr[X]) : List Fr :=
  polys.flatMap fun p => p.roots.toList

open Classical in
/-- Find a candidate whose generator multiple is the public first monomial point. -/
noncomputable def setupSecretRootSearch (pw : SetupPowers) (polys : List Fr[X]) : Option Fr :=
  (setupSecretCandidates polys).find? fun candidate => decide (G1.Represents pw.1[1] candidate)

private theorem represents_first_setupPower (τ : Fr) :
    G1.Represents (setupPowers τ).1[1] τ := by
  rw [show (setupPowers τ).1[1] = G1.mul G1.generator τ by
    simpa using setupPowers_g1 τ ⟨1, by decide⟩]
  exact G1.represents_mul_generator τ

/-- A result of the search is the secret, because its public multiple matches. -/
theorem setupSecretRootSearch_sound {τ candidate : Fr} {polys : List Fr[X]}
    (h : setupSecretRootSearch (setupPowers τ) polys = some candidate) : candidate = τ := by
  classical
  have hrep : G1.Represents (setupPowers τ).1[1] candidate := by
    simpa only [decide_eq_true_eq] using List.find?_some h
  exact hrep.unique (represents_first_setupPower τ)

/-- A nonzero candidate polynomial with the secret as a root makes the search recover it. -/
theorem setupSecretRootSearch_eq_some {τ : Fr} {polys : List Fr[X]} {p : Fr[X]}
    (hp : p ∈ polys) (hp0 : p ≠ 0) (hroot : p.eval τ = 0) :
    setupSecretRootSearch (setupPowers τ) polys = some τ := by
  classical
  have hmem : τ ∈ setupSecretCandidates polys := by
    exact List.mem_flatMap.mpr ⟨p, hp, by simpa using (Polynomial.mem_roots hp0).mpr hroot⟩
  cases h : setupSecretRootSearch (setupPowers τ) polys with
  | none =>
    have hnone := List.find?_eq_none.mp h τ hmem
    have hrep := represents_first_setupPower τ
    simp only [decide_eq_true_eq] at hnone
    exact False.elim (hnone hrep)
  | some candidate =>
    exact congrArg some (setupSecretRootSearch_sound h)

/-- With no candidates, the search fails. -/
theorem setupSecretRootSearch_nil (pw : SetupPowers) : setupSecretRootSearch pw [] = none := by
  simp [setupSecretRootSearch, setupSecretCandidates]

/-- The zero polynomial supplies no roots to the search. -/
theorem setupSecretRootSearch_zero (pw : SetupPowers) :
    setupSecretRootSearch pw [0] = none := by
  simp [setupSecretRootSearch, setupSecretCandidates]

/-- The search tests at most the sum of the candidate degrees. -/
theorem length_setupSecretCandidates_le (polys : List Fr[X]) :
    (setupSecretCandidates polys).length ≤ (polys.map Polynomial.natDegree).sum := by
  induction polys with
  | nil => simp [setupSecretCandidates]
  | cons p polys ih =>
    simp only [setupSecretCandidates, List.flatMap_cons, List.length_append,
      Multiset.length_toList, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (Polynomial.card_roots' p) ih

/-- The probability of recovering a uniform secret from its public setup powers.

`none` is a failure even when the secret is zero. -/
noncomputable def setupSecretAdvantage
    (adversary : SetupPowers → ProbComp (Option Fr)) : ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let candidate ← adversary (setupPowers τ)}[candidate = some τ]

end EthLib.Cryptography.Kzg
