module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ClassifiedForgery

/-!
# The query budget of the classified leanXMSS experiment

The first two hash calls pay for the two guesses of a private seed in the reduction.

The remaining calls pay for the graph and the signed digest collisions.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig TwoLayerGraph Honest OracleComp OracleSpec SecretEncoding.Residual
open scoped ENNReal

private theorem seed_debit (left : Nat) (within : left + 2 ≤ 2 ^ 127) :
    (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ ≤ 1 / 2 ^ 127 := by
  have capped : left + 2 - 1 ≤ 2 ^ 127 := by omega
  calc
    _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by gcongr
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- Transfer the remaining query budget to the original game, including early refusal. -/
theorem forge_le_of_classified_budget (A : Adversary) (q : Nat) (bounded : HasHashQueryBound A q)
    (price : ∀ left, q = left + 2 → q < 2 ^ 127 → ∀ w : HashOutput,
      let pp := parameterOfWord w
      let r := localState _ _ (toKeyedState pp (afterWord w))
      Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left
        ((mixedGame pp A).run r))}[classified pp (z.1.1.map Prod.fst) z.2.1] ≤
          (left : ℝ≥0∞) / 2 ^ 127) :
    forgeAdvantage A ≤ (q : ℝ≥0∞) / 2 ^ 127 := by
  by_cases small : q ≤ 1
  · rw [forge_zero_of_le_one A q small bounded]
    exact zero_le
  by_cases large : 2 ^ 127 ≤ q
  · have prob : forgeAdvantage A ≤ 1 := prEvent_le_one _
    apply prob.trans
    calc
      1 = (2 ^ 127 : ℝ≥0∞) / 2 ^ 127 := (ENNReal.div_self (by norm_num) (by finiteness)).symm
      _ ≤ _ := by gcongr; exact_mod_cast large
  obtain ⟨left,rfl⟩ : ∃ left, q = left + 2 := ⟨q - 2, by omega⟩
  have debit := seed_debit left (by omega)
  have charged := forge_le_classified A left _ bounded (price left rfl (by omega))
  refine charged.trans ((add_le_add (add_le_add le_rfl debit) debit).trans_eq ?_)
  rw [Nat.cast_add, Nat.cast_ofNat, ENNReal.add_div]
  simp only [div_eq_mul_inv, one_mul]
  ring

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
