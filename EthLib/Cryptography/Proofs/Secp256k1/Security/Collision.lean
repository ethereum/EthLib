module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.LazyGame

/-!
# Proofs: a forgery on an old hash, charged to a collision of the hash

A forgery on a new message with the hash of a signed message exhibits a collision of `H`.

Source: [Fersch, Kiltz, Poettering, CCS 2016][fkp], Theorem 1, Figure 4, Games G0 to G1.

[fkp]: https://doi.org/10.1145/2976749.2978413
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- The chance that a finder returns two different messages with the same hash.

A finder returns a pair of messages, or nothing. -/
noncomputable def collisionAdvantage (scheme : Scheme F G A M)
    (finder : ProbComp (Option (M × M))) : ℝ≥0∞ :=
  Pr{let r ← finder}[∃ m m', r = some (m, m') ∧ m ≠ m' ∧ scheme.hash m = scheme.hash m']

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [DecidableEq M] [FinEnum A]

/-- The finder of a collision from a forger.

It runs the game with `Π` sampled lazily, and keeps the forged message and the signing cache.

It returns a signed message other than the forged one with the same hash, if the cache has one.

It returns it with the forged message. -/
def collisionFinder (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp (Option (M × M)) :=
  -- The collision that the final signing cache exhibits, paired with the forged message.
  (fun z : (M × F × F) × Bool × Cache F M =>
      (collisionOf scheme z.2.2 z.1.1).map fun m' => (m', z.1.1)) <$>
    -- The game, with `Π` sampled lazily, as a reduction can.
    --
    -- No theorem states the running time of the finder.
    --
    -- It tries up to `fuel` nonces for each request, where their `τ_cr = τ + O(Q_s)` counts one.
    (simulateQ lazyPermImpl (experimentViewQ scheme fuel adversary)).run' []

/-- The chance to win the game when no signed message other than the forged one has its hash.

It is their Game G1: this game with lines 18 and 19 of their Figure 4. -/
noncomputable def noCollisionAdvantage (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) : ℝ≥0∞ :=
  Pr{let z ← experimentView scheme fuel adversary}[
    z.2.1 = true ∧ collisionOf scheme z.2.2.1 z.1.1 = none]

/-- **A forgery on an old hash is charged to the finder of a collision.**

The forger's advantage is at most the sum of two terms.

The first is its chance to win with no collision in the cache.

The second is the advantage of the finder built from it. -/
theorem forgeAdvantage_le_noCollisionAdvantage_add_collisionAdvantage (scheme : Scheme F G A M)
    (fuel : ℕ) (adversary : Adversary F G A M) :
    forgeAdvantage scheme fuel adversary ≤
      noCollisionAdvantage scheme fuel adversary +
        collisionAdvantage scheme (collisionFinder scheme fuel adversary) := by
  have h1 : forgeAdvantage scheme fuel adversary =
      Pr{let z ← experimentView scheme fuel adversary}[z.2.1 = true] := by
    rw [forgeAdvantage, ← result_map_experimentView, prEvent_map]
  -- The game counts a forgery on a new message whose hash is the hash of a signed message.
  --
  -- Such a forgery exhibits a collision of `H`, so split the wins on one.
  have h2 : Pr{let z ← experimentView scheme fuel adversary}[z.2.1 = true] ≤
      Pr{let z ← experimentView scheme fuel adversary}[
        (z.2.1 = true ∧ collisionOf scheme z.2.2.1 z.1.1 = none) ∨
          collisionOf scheme z.2.2.1 z.1.1 ≠ none] := by
    refine prEvent_mono _ _ _ fun z hz => ?_
    by_cases h : collisionOf scheme z.2.2.1 z.1.1 = none
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr h
  -- A collision in the cache is a win of the finder.
  --
  -- Here `H` is fixed, while their §2.3 draws a key for it.
  --
  -- So an adversary that knows a collision of `H` always wins the game of collisions.
  --
  -- The bound therefore charges the named finder, and no adversary against collisions in general.
  have h3 : Pr{let z ← experimentView scheme fuel adversary}[
      collisionOf scheme z.2.2.1 z.1.1 ≠ none] ≤
      collisionAdvantage scheme (collisionFinder scheme fuel adversary) := by
    have hd := experimentView_evalDistEq_lazy scheme fuel adversary
    have h4 := EvalDistEq.prEvent_eq hd
      (fun w : (M × F × F) × Bool × Cache F M => collisionOf scheme w.2.2 w.1.1 ≠ none)
    rw [prEvent_map] at h4
    refine h4.trans_le ?_
    rw [collisionAdvantage, collisionFinder, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hw
    refine ⟨m', w.1.1, by simp [hm'], ?_⟩
    exact collisionOf_valid hm'
  calc _ = _ := h1
    _ ≤ _ := h2
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
      unfold noCollisionAdvantage
      gcongr

/-- The chance to win with no collision is the same in the game with `Π` sampled lazily.

The next steps of the proof start from that lazy game. -/
theorem noCollisionAdvantage_eq_lazy (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    noCollisionAdvantage scheme fuel adversary =
      Pr{let z ← (simulateQ lazyPermImpl (experimentViewQ scheme fuel adversary)).run' []}[
        z.2.1 = true ∧ collisionOf scheme z.2.2 z.1.1 = none] := by
  rw [← (experimentView_evalDistEq_lazy scheme fuel adversary).prEvent_eq, prEvent_map]
  rfl

end EthLib.Cryptography.Secp256k1.Security
