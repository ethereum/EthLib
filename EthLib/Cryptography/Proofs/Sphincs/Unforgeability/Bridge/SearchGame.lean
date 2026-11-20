module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.SearchGameRun

/-!
# Proofs: the game hop that charges the signer's long counter searches apart

Fix a bound `T` on the counter searches.

A wrapped adversary runs the adversary and forwards its queries.

It stops forwarding once a signing answer is nothing or has a counter of at least `T`.

From then on it still forwards coins.

It answers a hash call with 0 and a signing request with nothing, without querying.

It returns the adversary's forgery.

Up to that answer, the two runs are the same.

So the adversary forges at most as often as the wrapped one, plus one more chance.

That is the chance that some answer of its own run has a long search.

Such an answer leaves a failed search of `T` trials in the cache, which is unlikely.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic
open scoped OracleComp.Lower
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld)

/-- A forging probability over a counted run is an expectation over the plain random oracle. -/
theorem prEvent_eq_wp_of_eq_withAddCost (oa : OracleComp OracleWorld Bool)
    (X : ProbComp (Bool × Nat))
    (hX : X = (simulateQ (HashSpec.romImpl.withAddCost hashCost) oa).run.run' ∅) :
    Pr{let result ← X}[result.1 = true] =
      wp ((simulateQ HashSpec.romImpl oa).run ∅) (fun x => propInd (x.1 = true)) := by
  subst hX
  refine (HashSig.prEvent_run_withAddCost oa hashCost).trans ?_
  rw [prEvent_eq_wp_propInd, StateT.run'_eq, wp_map]
  rfl

/-- A counted run within `n` hash calls leaves a failed search with chance `<= n (1 - p)^T`.

A failed search is one whose first `T` trials all failed, with `1 <= T <= 2^32`.

`p` is the chance that one counter gives a codeword, `CODE_SIZE / 2^128`. -/
theorem wp_failedSearch_le_of_eq {α : Type} (T : Nat) (hT₁ : 1 ≤ T)
    (hT : T ≤ MAX_COUNTER_TRIALS) (oa : OracleComp OracleWorld α) (X : ProbComp (α × Nat))
    (hX : X = (simulateQ (HashSpec.romImpl.withAddCost hashCost) oa).run.run' ∅) (n : Nat)
    (hn : ∀ z ∈ support X, z.2 ≤ n) :
    wp ((simulateQ HashSpec.romImpl oa).run ∅)
      (fun x => propInd (HashSig.FailedSearch searchPoint SearchMiss T x.2)) ≤
      (n : ℝ≥0∞) * (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ T := by
  subst hX
  rw [← prEvent_eq_wp_propInd, ← prEvent_searchMiss]
  exact HashSig.prEvent_failedSearch_le searchPoint SearchMiss T hT₁
    (fun p p' j j' hj hj' he => searchPoint_inj p p' j j' (by omega) (by omega) he)
    hashCost (fun _ => le_rfl) oa n hn

/-- **The adversary forges at most as often as the wrapped one, plus a long-search term.**

The adversary makes at most `q` hash calls of its own and `r` signing requests.

The bound on the searches is `1 <= T <= 2^32`.

The extra term is `(q + C) * (1 - p)^T`, where `C` bounds the scheme's calls.

`p` is the chance that one counter gives a codeword, `CODE_SIZE / 2^128`. -/
theorem forgeAdvantage_le_capSearches (T : Nat) (hT₁ : 1 ≤ T) (hT : T ≤ MAX_COUNTER_TRIALS)
    (adversary : Adversary) (q r : Nat) (h : HasAdversaryQueryBound adversary q r) :
    forgeAdvantage adversary ≤ forgeAdvantage (capSearches T adversary) +
      ((q + schemeCalls r : Nat) : ℝ≥0∞) *
        (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ T := by
  -- Both advantages are expectations over the plain random oracle, from the empty cache.
  have hE : ∀ B, forgeAdvantage B = wp ((simulateQ HashSpec.romImpl (gameCore B)).run ∅)
      (fun x => propInd (x.1 = true)) := fun B =>
    prEvent_eq_wp_of_eq_withAddCost (gameCore B) (experiment B) (experiment_eq B)
  -- A long search somewhere in the honest game leaves a failed search in its final cache.
  have hFS : wp ((simulateQ HashSpec.romImpl (gameCore adversary)).run ∅)
      (fun x => propInd (HashSig.FailedSearch searchPoint SearchMiss T x.2)) ≤
      ((q + schemeCalls r : Nat) : ℝ≥0∞) *
        (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ T :=
    wp_failedSearch_le_of_eq T hT₁ hT (gameCore adversary) (experiment adversary)
      (experiment_eq adversary) _ (hasHashQueryBound_of_adversary adversary q r h)
  rw [hE, hE]
  refine le_trans ?_ (add_le_add le_rfl hFS)
  rw [wp_run_gameCore, wp_run_gameCore, wp_run_gameCore, ← ExpectationWP.Lower.wp_add_of_oracle]
  -- After key generation, compare the two runs with the same check.
  exact wp_mono _ fun w => wp_run_le_wp_capSearches T hT adversary w.1.1 w.1.2 w.2
    fun run => liftM (verifierOf w.1.2 run.1) >>= fun verified =>
      pure (verdictOf run.1 run.2 verified)

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
