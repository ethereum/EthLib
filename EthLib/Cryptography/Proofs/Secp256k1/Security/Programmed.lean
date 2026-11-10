module

public import EthLib.Cryptography.Proofs.ProgrammedPermutation
public import EthLib.Cryptography.Proofs.Secp256k1.Security.Collision
public import EthLib.Cryptography.Proofs.Secp256k1.Security.JointGame

/-!
# Proofs: the ECDSA game with `Π` programmed by the signer

The lazy game keeps one cache of `Π`, and the signer asks `Π` like the adversary does.

Here the signer programs `Π` instead.

For each nonzero nonce, it draws the answer uniformly from all of `A`, and records the pair.

The adversary's queries go to an overlay.

The overlay answers from its own cache.

Otherwise it asks the lazy permutation, and records the answer.

So the lazy permutation sees only the relayed queries.

Each pair of the overlay's cache carries a flag: set by the signer, or relayed.

The overlay and the programming oracle come from a shared module on lazy permutations.

The game also always checks the forgery, through the overlay, even on a signed message.

A conflict is two pairs of the cache that share a query or an answer.

Until a conflict, the lazy game puts at least as much mass on each outcome as this game.

So the chance to win the lazy game with no collision is at most a sum of two chances.

The first is the chance to win here with no collision and no conflict.

The second is the chance of a conflict here.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

This is the step from Game G1 of their Figure 4 to Game G2 of their Figure 5.

Their `Π_S` holds the pairs set by the signer, and their `Π_O` the relayed pairs.

Their aborts in lines 05, 11, 13 and 25 are conflicts here.

The relayed query of the check adds one more source of conflict.

They stop the game, where here the game goes on and the event excludes them.

Their signer tries one nonce, and the one here tries up to `fuel`.

Each nonzero nonce asks `Π` once, so it records a pair, also when its signature then fails.

Their line 14 records it before the checks of lines 16 and 19 too.

So the cache holds up to `fuel` pairs set by the signer per signing query.

So their counts of `Q_s` pairs set by the signer become `fuel` times `Q_s`.

The check of the forgery may relay one more query, which their Definition 4 rules out.

So a bound on the chance of a conflict counts that query too.

No theorem bounds that chance yet.

Such a bound needs a nonzero base point and a semi-injective `φ`.

With the base point `0`, every nonce programs the same query, and the second one conflicts.

The keyless signer of their Game G3 must record the pairs of failed nonces as well.

Otherwise the cache, and the answers of later queries, differ from the ones here.

Their Figure 5 records only at line 40, after the checks of lines 31, 34 and 36.

So this departs from the source.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type} [FinEnum A]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]

/-! ## The game with `Π` programmed -/

variable [SampleableType F]

/-- The game with `Π` programmed by the signer, after their Game G2.

It differs from it in these ways.

Its conflicts do not stop it, its signer tries up to `fuel` nonces, and it always checks.

That check may relay a new query of `Π`.

Its key is drawn from all scalars.

The win, with no collision and a new message, is a separate event.

It draws the key, and runs the adversary with the overlay of `Π` and the programming signer.

Then it checks the forgery through the overlay, also when its message was signed.

It returns the forgery, the result of the check, and the final states. -/
def programmedExperiment (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    ProbComp (((M × F × F) × Bool) × JointState F M (ProgrammedCache A × PermCache A)) := do
  let x ← $ᵗ F
  (simulateQ (jointImpl overlayLazyOracle
      (liftFresh programPermOracle fun m => signFreshQ scheme x m fuel))
    (runWithCheck scheme adversary (x • scheme.g))).run ([], ([], []))

/-- Whether a run of the game with `Π` programmed wins with no collision.

The forged message is new, the check passes, and no other signed message has its hash. -/
def ProgrammedWin (scheme : Scheme F G A M)
    (z : ((M × F × F) × Bool) × JointState F M (ProgrammedCache A × PermCache A)) : Prop :=
  signed z.2.1 z.1.1.1 = false ∧ z.1.2 = true ∧ collisionOf scheme z.2.1 z.1.1.1 = none

/-- **A win with no collision, against the game with `Π` programmed.**

The chance to win the chosen-message game with no collision is at most a sum of two chances.

Both are chances in the programmed game.

The first is the chance to win there with no collision and no conflict in the cache of `Π`.

The second is the chance of a conflict there. -/
theorem noCollisionAdvantage_le_programmed (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    noCollisionAdvantage scheme fuel adversary ≤
      Pr{let z ← programmedExperiment scheme fuel adversary}[
        ProgrammedWin scheme z ∧ ¬z.2.2.1.Conflict] +
      Pr{let z ← programmedExperiment scheme fuel adversary}[z.2.2.1.Conflict] := by
  rw [noCollisionAdvantage_eq_lazy, StateT.run'_eq, prEvent_map,
    simulateQ_lazyPermImpl_experimentViewQ_run, jointExperiment, programmedExperiment,
    prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← mul_add]
  gcongr
  rw [prEvent_jointRun_eq_runWithCheck scheme adversary _ lazyPermOracle [] _
    fun f c => collisionOf scheme c f.1 = none]
  have hfresh := fun m (s : ProgrammedCache A × PermCache A) (hs : s.2 = s.1.relayed)
      (_ : ¬s.1.Conflict) (Q : Option (F × F) × PermCache A → Prop) =>
    dominatedUntilBad_programPermImpl.prEvent_simulateQ_run_map_and_not_bad_le
      preservesInv_programPermImpl_relayed preservesInv_programPermImpl_conflict
      (signFreshQ scheme x m fuel) s hs Q
  have hdom := dominatedUntilBad_jointImpl dominatedUntilBad_overlayLazyOracle hfresh
  have hinv := preservesInv_jointImpl (F := F) preservesInv_overlayLazyOracle_relayed
    fun m => simulateQ_run_preservesInv _ _ preservesInv_programPermImpl_relayed
      (signFreshQ scheme x m fuel)
  have hbad := preservesInv_jointImpl (F := F) preservesInv_overlayLazyOracle_conflict
    fun m => simulateQ_run_preservesInv _ _ preservesInv_programPermImpl_conflict
      (signFreshQ scheme x m fuel)
  refine (hdom.prEvent_simulateQ_run_le_map_or_bad hinv hbad
    (runWithCheck scheme adversary (x • scheme.g)) ([], ([], [])) rfl
    fun z => signed z.2.1 z.1.1.1 = false ∧ z.1.2 = true ∧
      collisionOf scheme z.2.1 z.1.1.1 = none).trans ?_
  refine (prEvent_mono _ _
    (fun z => (ProgrammedWin scheme z ∧ ¬z.2.2.1.Conflict) ∨ z.2.2.1.Conflict)
    fun z hz => ?_).trans (prEvent_or_le _ _ _)
  by_cases hc : z.2.2.1.Conflict
  · exact Or.inr hc
  · exact Or.inl ⟨hz.resolve_right hc, hc⟩

end EthLib.Cryptography.Secp256k1.Security
