module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.QueryBound
public import EthLib.Cryptography.Proofs.IndependentAnswers

/-!
# Proofs: the key-only game of ECDSA, and its bijection swapped for independent answers

A key-only forger gets the public key, coins, and `Π` in both directions, but no signatures.

It wins when it returns a valid signature on some message.

This is the chosen-message game with no signing query, as a lemma below proves.

The game draws `Π` up front.

Read the game as a program of the permutation oracle.

Then its final check asks for `Π` at most once more than the forger.

With `Π` sampled one answer at a time, it has the same law.

Then answer each new query of `Π` with an independent uniform value instead.

A flag rises when that value is already in the cache, in the direction of the query.

Take a forger that asks for `Π` or its inverse at most `q` times.

Compare its chance to win the game with its chance to win with independent answers and no flag.

The first exceeds the second by at most `q (q + 1) / 2` over `|A|`.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The key-only game is the variant of their Figure 1 named in their Definition 4.

Their key generation avoids the scalar `0`, and the key here may be `0`, which never verifies.

So the advantage here is theirs times `(n - 1) / n`, where `n` is the number of scalars.

No theorem states it.

The swap is the step from Game G0 to Game G1 of their §4.2, in the proof of their Theorem 2.

Their Game G1 is in their Figure 7, and stops with `0` where the flag rises here.

Their `Q` bounds the forger's queries, and their forger asks the check's query first.

Here the check may ask once more, hence `q + 1`.

Their bound `Q² / 2^L` is still at least the one here.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- A key-only forger: from the public key, it returns a message and a claimed signature `(t, s)`.

It has coins and `Π` in both directions, and no signing oracle. -/
structure KeyOnlyAdversary (F G A M : Type) where
  /-- The forger's run, with access to the oracles. -/
  main : G → PermComp A (M × F × F)

/-- A key-only forger in the chosen-message game: it never asks for a signature. -/
def KeyOnlyAdversary.toAdversary (adversary : KeyOnlyAdversary F G A M) : Adversary F G A M where
  main X := simulateQ keyOnlyLift (adversary.main X)

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A key-only forger on the key `X`, then the check of its forgery, which may ask for `Π`. -/
def keyOnlyRunQ (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) (X : G) :
    PermComp A ((M × F × F) × Bool) := do
  let z ← adversary.main X
  let b ← verifyQ scheme X z.1 z.2.1 z.2.2
  pure (z, b)

/-- The run asks for `Π` or its inverse at most once more than the forger. -/
theorem isQueryBoundP_keyOnlyRunQ (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {q : ℕ}
    (hq : IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    IsQueryBoundP (keyOnlyRunQ scheme adversary X) (·.isRight = true) (q + 1) := by
  have h := isQueryBoundP_bind hq fun z _ =>
    isQueryBoundP_bind (isQueryBoundP_verifyQ scheme X z.1 z.2.1 z.2.2) fun b _ =>
      isQueryBoundP_pure (fun t : (unifSpec + PermSpec A).Domain => t.isRight = true)
        ((z, b) : (M × F × F) × Bool) 0
  simpa [keyOnlyRunQ] using h

variable [SampleableType F]

/-- The key-only game as a program of the permutation oracle.

It draws the key, runs the forger, and checks the forgery.

The check asks for `Π` itself, once or never. -/
def keyOnlyExperimentQ (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) :
    PermComp A Bool := do
  let x ← ($ᵗ F : ProbComp F)
  Prod.snd <$> keyOnlyRunQ scheme adversary (x • scheme.g)

/-- The key-only game asks for `Π` or its inverse at most `q + 1` times.

The forger asks for them at most `q` times, on every key. -/
theorem isQueryBoundP_keyOnlyExperimentQ (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) {q : ℕ}
    (hq : ∀ X, IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    IsQueryBoundP (keyOnlyExperimentQ scheme adversary) (·.isRight = true) (q + 1) := by
  have h := isQueryBoundP_bind (isQueryBoundP_liftM_permComp ($ᵗ F)) fun x _ =>
    (isQueryBoundP_map_iff _ Prod.snd _).2
      (isQueryBoundP_keyOnlyRunQ scheme adversary (x • scheme.g) (hq (x • scheme.g)))
  simpa [keyOnlyExperimentQ] using h

omit [DecidableEq G] in
/-- The oracles of the chosen-message game answer a lifted run as `π` does, with the cache kept. -/
theorem simulateQ_impl_keyOnlyLift_run [DecidableEq M] (scheme : Scheme F G A M) (fuel : ℕ)
    (π : Equiv.Perm A) (x : F) {α : Type} (oa : PermComp A α) (cache : Cache F M) :
    (simulateQ (impl scheme fuel π x) (simulateQ keyOnlyLift oa)).run cache =
      (·, cache) <$> simulateQ (permImpl π) oa := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | a | b
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change ((·, cache) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) >>= _ = _
      simp [ih]
    all_goals
      simp only [StateT.run, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, keyOnlyLift_inr_inl, keyOnlyLift_inr_inr,
        HasQuery.instOfMonadLift_query, id_map, impl, map_pure, pure_bind, add_apply_inr]
      exact ih _ cache

variable [FinEnum A]

/-- The key-only game: draw `Π` and the key, run the forger with its oracles, check the forgery.

The key is uniform over all scalars, as in the chosen-message game.

The source's key generation avoids `0`; the key `0` gives the point `0`, which never verifies. -/
def keyOnlyExperiment (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) :
    ProbComp Bool := do
  let π ← $ᵗ (Equiv.Perm A)
  let x ← $ᵗ F
  let X := x • scheme.g
  let (m, t, s) ← simulateQ (permImpl π) (adversary.main X)
  return verify scheme π X m t s

/-- The probability that the key-only forger forges. -/
noncomputable def keyOnlyAdvantage (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) : ℝ≥0∞ :=
  Pr{let b ← keyOnlyExperiment scheme adversary}[b = true]

/-- A key-only forger wins the chosen-message game as often as the key-only game.

The signing oracle is never asked, so every message is fresh. -/
theorem forgeAdvantage_toAdversary [DecidableEq M] (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : KeyOnlyAdversary F G A M) :
    forgeAdvantage scheme fuel adversary.toAdversary = keyOnlyAdvantage scheme adversary := by
  unfold forgeAdvantage keyOnlyAdvantage
  congr 1
  simp only [experiment, keyOnlyExperiment, KeyOnlyAdversary.toAdversary,
    simulateQ_impl_keyOnlyLift_run, bind_map_left]
  simp [signed]

/-- With `Π` drawn up front and given to the oracle, the program is the key-only game. -/
theorem keyOnlyExperiment_eq_permImpl (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) :
    keyOnlyExperiment scheme adversary =
      (do
        let π ← $ᵗ (Equiv.Perm A)
        simulateQ (permImpl π) (keyOnlyExperimentQ scheme adversary)) := by
  simp only [keyOnlyExperiment, keyOnlyExperimentQ, keyOnlyRunQ, simulateQ_bind,
    simulateQ_permImpl_liftM, map_bind, simulateQ_pure, map_pure]
  refine bind_congr fun π => bind_congr fun x => bind_congr fun z => ?_
  rw [simulateQ_permImpl_verifyQ]
  simp

/-- The advantage of every key-only forger is its chance to win the lazy key-only game. -/
theorem keyOnlyAdvantage_eq_lazy (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) :
    keyOnlyAdvantage scheme adversary =
      Pr{let b ←
        (simulateQ lazyPermImpl (keyOnlyExperimentQ scheme adversary)).run' []}[b = true] := by
  rw [keyOnlyAdvantage, keyOnlyExperiment_eq_permImpl]
  exact (uniformSample_bind_simulateQ_permImpl_evalDistEq _).prEvent_eq _

/-- The key-only game with independent answers, as their Game G1.

It runs the program from the empty cache, and wins when the check passes and no flag rose. -/
def keyOnlyIndepExperiment (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) :
    ProbComp Bool :=
  (fun z => z.1 && !z.2.2) <$>
    (simulateQ indepPermImpl (keyOnlyExperimentQ scheme adversary)).run ([], false)

/-- The probability that the key-only forger wins with independent answers. -/
noncomputable def keyOnlyIndepAdvantage (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) : ℝ≥0∞ :=
  Pr{let b ← keyOnlyIndepExperiment scheme adversary}[b = true]

/-- **The key-only game with `Π` swapped for independent answers.**

The forger asks for `Π` or its inverse at most `q` times, on every key.

Its chance to win the key-only game exceeds its chance to win with independent answers.

The excess is at most `q (q + 1) / 2` over `|A|`. -/
theorem keyOnlyAdvantage_le_indep (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) {q : ℕ}
    (hq : ∀ X, IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    keyOnlyAdvantage scheme adversary ≤
      keyOnlyIndepAdvantage scheme adversary + ((q + 1).choose 2 : ℝ≥0∞) / FinEnum.card A := by
  rw [keyOnlyAdvantage_eq_lazy, keyOnlyIndepAdvantage, keyOnlyIndepExperiment, prEvent_map]
  refine (prEvent_lazyPermImpl_le_indepPermImpl _
    (isQueryBoundP_keyOnlyExperimentQ scheme adversary hq) (· = true)).trans (le_of_eq ?_)
  congr 1
  refine prEvent_congr _ _ _ fun z => ?_
  cases z.1 <;> cases z.2.2 <;> simp

end EthLib.Cryptography.Secp256k1.Security
