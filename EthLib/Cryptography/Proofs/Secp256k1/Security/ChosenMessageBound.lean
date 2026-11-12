module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.Conflict
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeylessForger
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnlyBound

/-!
# Proofs: the bound on a chosen-message forger of ECDSA

Take a forger with at most `q_Π` queries to `Π` or its inverse, and `q_S` signing queries.

Its advantage is at most a sum of four terms.

The first is the advantage of a key-only forger built from it.

The second is the advantage of a solver of the discrete logarithm.

It covers a forgery whose point holds a pair that the signer programmed.

The third is the advantage of a finder of collisions of `H`.

The last is the bound on the chance of a conflict in the cache of `Π`.

The bound on a key-only forger then gives a bound with no key-only forger.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The first bound is their Theorem 1.

Its proof follows their games of Figures 4 and 5, and their forger of Figure 6.

Their bound is `ε_0 + ε_cr + 3 Q Q_s / ((q - 1) / 2 - Q)`.

There `Q = Q_s + Q_Π`, and `q` is the group order.

The first bound departs from theirs in these ways.

- The signing oracle answers a repeated message from its cache, as RFC 6979 does.
  Their signing oracle draws a fresh nonce on each request.
- Their key generation draws the key from the nonzero scalars.
  Here it draws it from all of them.
- The hash `H` is fixed, while their §2.3 draws a key for it.
  So the bound charges the named finder of collisions.
  It charges no adversary against collisions in general.
- The signer tries up to `fuel` nonces per request, where theirs tries one.
  So their `Q_s` becomes `fuel · q_S` in the bound on a conflict.
- The check of the forgery may relay one more query of `Π`, which their Definition 4 rules out.
  So their `Q_Π` becomes `q_Π + 1` there.
- Their Game G3 records a pair of `Π` only when a nonce signs.
  Their Game G2 records it before its checks.
  So their claim that the forger wins as often in both games does not follow as written.
  The signer with no key here records the pairs of failed nonces too.
- Their forger signs again at line 30 of Figure 6, which may fail.
  The case of a programmed point is charged to a named solver of the discrete logarithm instead.
  That adds the second term.
  Their forger also asks `Π` again when it signs there.
- The bound on a conflict keeps the three terms of their proof, before they sum them.
  Its terms are in `|A|` and `|F|`, with `N = q_Π + 1 + fuel · q_S` for their `Q`.
  No theorem compares the two.
- No theorem states the running times of the forger, the solver or the finder.

The second bound adds the departures of the bound on a key-only forger, from their Theorem 2.

Their `Q` is `q_Π + 1` there, and the bound there has another form.

It is at most theirs term by term, which no theorem states.

Its solvers of the discrete logarithm draw the key from all scalars, a gap of at most `1 / q`.

Its inverse solver is efficient only when the test of the image is.

Its proof marks each new forward query with a query of the coins at the code of its point.

That bound covers the encodings where opposite points share their encoding, as ECDSA's does.

So it covers the case of ECDSA of their Definition 2 (b), and not the injective case.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal

variable {F G A M : Type}

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]
  [FinEnum F] [SampleableType F] [FinEnum A]

/-- **The bound on a chosen-message forger, by a key-only forger.**

The forger asks for `Π` or its inverse at most `q_Π` times, and for signatures at most `q_S` times.

Both query bounds hold on every key.

Its advantage is at most the sum of four terms.

They are the key-only forger's advantage, the solver's, the finder's, and the bound on a conflict.

The base point must be nonzero, and the encoding semi-injective.

The normal form must keep or negate `s`.

The bound departs from their Theorem 1 in the ways the module header lists. -/
theorem forgeAdvantage_le_keyOnly {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (hnorm : scheme.NormalizeSign) (fuel : ℕ)
    (adversary : Adversary F G A M) {qPerm qSign : ℕ}
    (hPerm : ∀ X, IsQueryBoundP (adversary.main X) (isPermQuery · = true) qPerm)
    (hSign : ∀ X, IsQueryBoundP (adversary.main X) (isSignQuery · = true) qSign) :
    forgeAdvantage scheme fuel adversary ≤
      keyOnlyAdvantage scheme (keylessForger scheme fuel adversary) +
        Pr{let b ← DiffieHellman.dlogExperiment scheme.g (keylessSolver scheme fuel adversary)}[
          b = true] +
        collisionAdvantage scheme (collisionFinder scheme fuel adversary) +
        conflictBound F A fuel qPerm qSign := by
  have hwin : Pr{let z ← programmedExperiment scheme fuel adversary}[
      ProgrammedWin scheme z ∧ ¬z.2.2.1.Conflict] ≤
      Pr{let z ← keylessExperiment scheme fuel adversary}[ProgrammedWin scheme z] := by
    rw [EvalDistEq.prEvent_eq (keylessExperiment_evalDistEq_programmedExperiment hg fuel adversary)]
    exact prEvent_mono _ _ _ fun z hz => hz.1
  calc forgeAdvantage scheme fuel adversary
      ≤ noCollisionAdvantage scheme fuel adversary +
          collisionAdvantage scheme (collisionFinder scheme fuel adversary) :=
        forgeAdvantage_le_noCollisionAdvantage_add_collisionAdvantage scheme fuel adversary
    _ ≤ (keyOnlyAdvantage scheme (keylessForger scheme fuel adversary) +
          Pr{let b ← DiffieHellman.dlogExperiment scheme.g (keylessSolver scheme fuel adversary)}[
            b = true] + conflictBound F A fuel qPerm qSign) +
          collisionAdvantage scheme (collisionFinder scheme fuel adversary) := by
        gcongr
        exact (noCollisionAdvantage_le_programmed scheme fuel adversary).trans
          (add_le_add (hwin.trans (prEvent_keylessExperiment_win_le hg hsemi hnorm fuel adversary))
            (prEvent_programmedExperiment_conflict_le hg hsemi fuel adversary hPerm hSign))
    _ = _ := add_right_comm _ _ _

variable [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

/-- **The bound on a chosen-message forger.**

The forger asks for `Π` or its inverse at most `q_Π` times, and for signatures at most `q_S` times.

Both query bounds hold on every key.

Its advantage is at most the bound by a key-only forger.

There the key-only forger's advantage is bounded in turn.

That adds `C(q_Π + 1, 2) / |A|` and `(q_Π + 1) / |A|`.

That bound charges two more solvers of the discrete logarithm.

It also charges a reduction to division resistance.

All four adversaries and the finder are built from the forger.

The base point must be nonzero, and `2` must be nonzero in the scalars.

The encoding must be semi-injective, and opposite points must share their encoding.

The normal form must keep or negate `s`.

The test of the inverse solver must agree with a search.

That search is over the nonzero multiples of the base point.

The bound has the departures of both bounds, which the module header lists. -/
theorem forgeAdvantage_le {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α) (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0)
    (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg) (hnorm : scheme.NormalizeSign)
    (fuel : ℕ) (adversary : Adversary F G A M) {qPerm qSign : ℕ}
    (hPerm : ∀ X, IsQueryBoundP (adversary.main X) (isPermQuery · = true) qPerm)
    (hSign : ∀ X, IsQueryBoundP (adversary.main X) (isSignQuery · = true) qSign) :
    let forger := keylessForger scheme fuel adversary
    forgeAdvantage scheme fuel adversary ≤
      ((qPerm + 1).choose 2 : ℝ≥0∞) / FinEnum.card A +
        Pr{let b ← DiffieHellman.dlogExperiment scheme.g (inverseSolver scheme inImage forger)}[
          b = true] +
        (qPerm + 1 : ℝ≥0∞) / FinEnum.card A +
        ((qPerm + 1 : ℝ≥0∞) *
          (Pr{let b ← DiffieHellman.dlogExperiment scheme.g (forwardSolver scheme forger qPerm)}[
              b = true] +
            (qPerm + 1) * divisionAdvantage scheme (divisionReduction scheme forger qPerm))) ^
          (2⁻¹ : ℝ) +
        Pr{let b ← DiffieHellman.dlogExperiment scheme.g (keylessSolver scheme fuel adversary)}[
          b = true] +
        collisionAdvantage scheme (collisionFinder scheme fuel adversary) +
        conflictBound F A fuel qPerm qSign := by
  intro forger
  have hkey := keyOnlyAdvantage_le hImage hg h2 hsemi hneg forger
    (isQueryBoundP_keylessForger scheme fuel adversary hPerm)
  refine (forgeAdvantage_le_keyOnly hg hsemi hnorm fuel adversary hPerm hSign).trans ?_
  gcongr ?_ + _ + _ + _

end EthLib.Cryptography.Secp256k1.Security
