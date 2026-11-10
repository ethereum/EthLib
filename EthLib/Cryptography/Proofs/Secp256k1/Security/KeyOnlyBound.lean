module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.DivisionResistance
public import EthLib.Cryptography.Proofs.Secp256k1.Security.ForwardSolver

/-!
# Proofs: the bound on a key-only forger

Take a key-only forger with at most `q` queries to `Π` or its inverse, on every key.

Its advantage is at most a sum of four terms.

The first is `C(q + 1, 2) / |A|`, the cost of answering `Π` with independent values.

The second is the advantage of a solver of the discrete logarithm, for a forgery on an inverse pair.

The third is `(q + 1) / |A|`.

The last is the square root of `(q + 1) (ε' + (q + 1) ε_dr)`.

There `ε'` is the advantage of a second solver of the discrete logarithm, from a fork.

And `ε_dr` is the advantage of a reduction in the game of division resistance of `H`.

Each of the three adversaries is built from the forger, and each advantage is a term of the bound.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The bound is their Theorem 2, from their games of Figure 7 and the reductions of Figures 9 and 10.

Their `Q` is `q + 1` here, and their `|B|` is `|A|`.

Their bound is `√(2 Q² ε_dr + 2 Q ε') + ε'' + Q² / 2^L`, where `ε''` is the inverse solver's.

Here the terms in `|A|` sum to `Q (Q + 1) / (2 |A|)`, at most `Q² / |A|`.

The root here is `√(Q ε' + Q² ε_dr)`, so the bound here is at most theirs.

The theorems bound chances only; no theorem states the running times of the three adversaries.

The inverse solver is efficient only when the test of the image is, as Definition 2 (a) asks.

Their key generation draws the key from the nonzero scalars; here it draws it from all of them.

So the advantage here is the source's times `(n - 1) / n`, where `n` is the number of scalars.

The hash `H` is fixed here, while their §2.3 draws a key for it.

So the bound charges the named reduction, and no adversary of division resistance in general.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [FinEnum F] [FinEnum A] [SampleableType F] [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

/-- **The bound on a key-only forger, by its chance of a fork index.**

Take a forger that asks for `Π` or its inverse at most `q` times, on every key.

Its advantage is at most `C(q + 1, 2) / |A|`, plus the inverse solver's advantage, plus a chance.

That chance is the one that its run has a fork index, with the key drawn uniformly.

The base point must be nonzero, and `2` must be nonzero in the scalars.

The encoding must be semi-injective, and opposite points must share their encoding.

The test of the inverse solver must agree with the search over all scalars. -/
theorem keyOnlyAdvantage_le_add_forkIndex {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α) (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0)
    (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg)
    (adversary : KeyOnlyAdversary F G A M) {q : ℕ}
    (hq : ∀ X, IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    keyOnlyAdvantage scheme adversary ≤
      ((q + 1).choose 2 : ℝ≥0∞) / FinEnum.card A +
        Pr{let b ← (DiffieHellman.dlogExperiment scheme.g
          (inverseSolver scheme inImage adversary))}[b = true] +
        Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
           let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
          (forkIndex scheme (x • scheme.g) q tr).isSome] := by
  have h1 := keyOnlyAdvantage_le_indep scheme adversary hq
  have h3 := keyOnlyIndepAdvantage_le_forkIndex_add_notMem scheme adversary hq
  have h4 := prEvent_inverse_le_dlog (inImage := inImage) hImage hg h2 hsemi hneg adversary
  refine h1.trans ((add_le_add (h3.trans (add_le_add le_rfl h4)) le_rfl).trans_eq ?_)
  ring

omit [FinEnum F] in
/-- **The chance of a fork index is bounded by the forward solver and division resistance.**

Let `acc` be the chance that the run of the forger has a fork index, with the key drawn uniformly.

Then `acc (acc / (q + 1) - 1 / |A|)` is at most the advantage of the forward solver plus a term.

That term is `q + 1` times the advantage of the reduction to division resistance.

The base point must be nonzero, and the encoding semi-injective. -/
theorem forkIndex_mul_le_dlog_add_division {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (adversary : KeyOnlyAdversary F G A M) (q : ℕ) :
    let acc := Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
                  let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
      (forkIndex scheme (x • scheme.g) q tr).isSome]
    acc * (acc / (q + 1 : ℝ≥0∞) - (FinEnum.card A : ℝ≥0∞)⁻¹) ≤
      Pr{let b ← DiffieHellman.dlogExperiment scheme.g (forwardSolver scheme adversary q)}[
        b = true] +
        (q + 1) * divisionAdvantage scheme (divisionReduction scheme adversary q) := by
  intro acc
  refine (le_prEvent_isSome_contextFork_keyOnlyOutsideRun_uniform scheme adversary q).trans ?_
  have key : ∀ P : Option (KeyOnlyTrace F A M × KeyOnlyTrace F A M) → Prop,
      Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A); let r ← (contextFork
          (keyOnlyOutsideRun scheme adversary (x • scheme.g)) (forkBound q) (.inr ())
          (forkIndex scheme (x • scheme.g) q))}[P r] =
        Pr{let r ← (liftComp ($ᵗ F : ProbComp F) (OutsideSpec A) >>= fun x ↦ contextFork
          (keyOnlyOutsideRun scheme adversary (x • scheme.g)) (forkBound q) (.inr ())
          (forkIndex scheme (x • scheme.g) q))}[P r] := fun P ↦ by
    rw [map_bind]
  refine le_trans ?_ (add_le_add (prEvent_contextFork_div_ne_le_dlog hg hsemi adversary q)
    (prEvent_contextFork_div_eq_le_divisionAdvantage scheme adversary q))
  rw [key, key, key]
  refine (prEvent_mono _ _ _ fun r hr ↦ ?_).trans (prEvent_or_le _ _ _)
  obtain ⟨⟨tr₁, tr₂⟩, rfl⟩ := Option.isSome_iff_exists.mp hr
  by_cases hd : scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 =
      scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1
  · exact .inr ⟨tr₁, tr₂, rfl, hd⟩
  · exact .inl ⟨tr₁, tr₂, rfl, hd⟩

/-- Take `a`, a finite nonzero `Q`, and `c`, `B` with `a (a / Q - c)` at most `B`.

Then `a` is at most `Q c` plus the square root of `Q B`. -/
private theorem le_mul_add_rpow_of_mul_div_sub_le {a Q c B : ℝ≥0∞} (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤)
    (h : a * (a / Q - c) ≤ B) : a ≤ Q * c + (Q * B) ^ (2⁻¹ : ℝ) := by
  rcases le_or_gt a (Q * c) with hac | hac
  · exact le_add_right hac
  have hsub : Q * (a / Q - c) = a - Q * c := by
    rw [ENNReal.mul_sub (fun _ _ ↦ hQ), ENNReal.mul_div_cancel hQ0 hQ]
  have hsq : (a - Q * c) ^ (2 : ℝ) ≤ Q * B := by
    rw [ENNReal.rpow_two, sq]
    calc (a - Q * c) * (a - Q * c) ≤ a * (a - Q * c) := by gcongr; exact tsub_le_self
      _ = Q * (a * (a / Q - c)) := by rw [← hsub]; ring
      _ ≤ Q * B := by gcongr
  have hd : a - Q * c ≤ (Q * B) ^ (2⁻¹ : ℝ) := by
    rw [ENNReal.le_rpow_inv_iff (by norm_num)]
    exact hsq
  calc a = Q * c + (a - Q * c) := (add_tsub_cancel_of_le hac.le).symm
    _ ≤ Q * c + (Q * B) ^ (2⁻¹ : ℝ) := by gcongr

/-- **The bound on a key-only forger.**

Take a forger that asks for `Π` or its inverse at most `q` times, on every key.

Let `ε''` be the advantage of the inverse solver and `ε'` the one of the forward solver.

Let `ε_dr` be the advantage of the reduction to division resistance.

Then the forger's advantage is at most the sum of `C(q + 1, 2) / |A|`, `ε''` and `(q + 1) / |A|`.

To that sum it adds the square root of `(q + 1) (ε' + (q + 1) ε_dr)`.

The hypotheses are the ones of the bound by the chance of a fork index. -/
theorem keyOnlyAdvantage_le {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α) (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0)
    (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg)
    (adversary : KeyOnlyAdversary F G A M) {q : ℕ}
    (hq : ∀ X, IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    keyOnlyAdvantage scheme adversary ≤
      ((q + 1).choose 2 : ℝ≥0∞) / FinEnum.card A +
        Pr{let b ← DiffieHellman.dlogExperiment scheme.g (inverseSolver scheme inImage adversary)}[
          b = true] +
        (q + 1 : ℝ≥0∞) / FinEnum.card A +
        ((q + 1 : ℝ≥0∞) *
          (Pr{let b ← DiffieHellman.dlogExperiment scheme.g (forwardSolver scheme adversary q)}[
              b = true] +
            (q + 1) * divisionAdvantage scheme (divisionReduction scheme adversary q))) ^
          (2⁻¹ : ℝ) := by
  have h1 := keyOnlyAdvantage_le_add_forkIndex hImage hg h2 hsemi hneg adversary hq
  have h3 := le_mul_add_rpow_of_mul_div_sub_le (by positivity) (by simp)
    (forkIndex_mul_le_dlog_add_division hg hsemi adversary q)
  refine h1.trans ?_
  calc _ ≤ ((q + 1).choose 2 : ℝ≥0∞) / FinEnum.card A +
          Pr{let b ← (DiffieHellman.dlogExperiment scheme.g
            (inverseSolver scheme inImage adversary))}[b = true] +
          ((q + 1 : ℝ≥0∞) * (FinEnum.card A : ℝ≥0∞)⁻¹ +
            ((q + 1 : ℝ≥0∞) *
              (Pr{let b ← DiffieHellman.dlogExperiment scheme.g (forwardSolver scheme adversary q)}[
                  b = true] +
                (q + 1) * divisionAdvantage scheme (divisionReduction scheme adversary q))) ^
              (2⁻¹ : ℝ)) := by gcongr
    _ = _ := by rw [div_eq_mul_inv ((q + 1 : ℝ≥0∞))]; ring

end EthLib.Cryptography.Secp256k1.Security
