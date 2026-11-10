module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Proofs: a computational co-Diffie-Hellman problem over two groups

Given `a • g1`, `a • g2` and `c • g2` for uniform scalars `a` and `c`, compute `(a * c) • g2`.

Keys lie in `G1` and signatures in `G2`, as in Ethereum.

[Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf) put them the other way round.

Their co-CDH problem (§2) gives only `a • g1` and `c • g2`, in these names.

The problem here also gives `a • g2`, so it is a stronger assumption.

The end of their §3.1 needs it when no computable map from `G1` to `G2` is known.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open OracleComp ENNReal MeasureTheory

/-- An adversary against co-CDH: from `(a • g1, a • g2, c • g2)` it returns a guess. -/
abbrev CoCdhAdversary (G₁ G₂ : Type) := G₁ → G₂ → G₂ → ProbComp G₂

variable (F : Type) [CommRing F] [SampleableType F] {G₁ G₂ : Type}
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]

/-- Sample `a` and `c`, run the adversary, and check its guess against `(a * c) • g2`. -/
def coCdhExperiment (g₁ : G₁) (g₂ : G₂) (adversary : CoCdhAdversary G₁ G₂) : ProbComp Bool := do
  let a ← $ᵗ F
  let c ← $ᵗ F
  let guess ← adversary (a • g₁) (a • g₂) (c • g₂)
  return decide (guess = (a * c) • g₂)

/-- The probability that the adversary solves co-CDH. -/
noncomputable def coCdhAdvantage (g₁ : G₁) (g₂ : G₂) (adversary : CoCdhAdversary G₁ G₂) :
    ℝ≥0∞ :=
  Pr{let b ← coCdhExperiment F g₁ g₂ adversary}[b = true]

/-- The advantage at co-CDH averages the solver's success over the scalars `a` and `c`. -/
theorem coCdhAdvantage_eq_lintegral (g₁ : G₁) (g₂ : G₂)
    (adversary : CoCdhAdversary G₁ G₂) :
    letI : MeasurableSpace F := ⊤
    coCdhAdvantage F g₁ g₂ adversary = ∫⁻ a, ∫⁻ c,
      Pr{let g ← adversary (a • g₁) (a • g₂) (c • g₂)}[g = (a * c) • g₂] ∂𝒟[$ᵗ F] ∂𝒟[$ᵗ F] := by
  let : MeasurableSpace F := ⊤
  rw [coCdhAdvantage, coCdhExperiment, prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun a => ?_
  rw [prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun c => ?_
  rw [bind_pure_comp, prEvent_map]
  simp

end EthLib.Cryptography.Bls.Security
