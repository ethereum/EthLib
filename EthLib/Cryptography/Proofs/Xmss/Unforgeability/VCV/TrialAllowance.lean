module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialPrice

/-!
# Sharing the message-query budget

The leanXMSS draft in "Security" gives the adversary a single public-hash budget.

Trial counts before and after registration refer to distinct queries in the same run.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials

open OracleComp OracleSpec
open scoped ENNReal

/-- Each trial before registration pays for the scaled second moment.

Each trial after registration pays for a later digest match.

The right-hand side retains the actual message cost for composition with the graph charges.
-/
theorem joint_price (A : Adversary) (q : Nat) (hq : q ≤ 2 ^ 127) :
    let m := game A q
    Pr{let z ← m}[z.2.1.1.hit = true] +
        (∑' z, Pr{let u ← m}[u = z] * ENNReal.ofReal
          ((z.2.2.2 / TrialMoment.rate) * z.2.2.1 +
            (1 - TrialMoment.rate) * (z.2.2.2 / TrialMoment.rate) ^ 2)) / 2 ^ 256 ≤
      (∑' z, Pr{let u ← m}[u = z] * (z.2.2.1 + z.2.1.1.paid : Nat)) / 2 ^ 128 := by
  intro m
  let pre := ∑' z, Pr{let u ← m}[u = z] * (z.2.2.1 : ℝ≥0∞)
  let post := ∑' z, Pr{let u ← m}[u = z] * (z.2.1.1.paid : ℝ≥0∞)
  have combined : (∑' z, Pr{let u ← m}[u = z] * ((z.2.2.1 + z.2.1.1.paid : Nat) : ℝ≥0∞)) =
      pre + post := by simp only [pre, post, Nat.cast_add, mul_add, tsum_add]
  rw [combined, ENNReal.add_div, add_comm (pre / _) (post / _)]
  apply add_le_add (post_price A q)
  have cost := (expected_game_product A q hq).trans
    (mul_le_mul_of_nonneg_right (TrialMoment.weight_le_digest q hq) zero_le)
  have scaled := mul_le_mul_of_nonneg_right cost (zero_le : 0 ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹)
  change _ ≤ (2 ^ 128 * pre) * _ at scaled
  rw [div_eq_mul_inv]
  apply scaled.trans_eq
  rw [mul_comm (2 ^ 128) pre, mul_assoc, div_eq_mul_inv]
  have nz : (2 : ℝ≥0∞) ^ 128 ≠ 0 := pow_ne_zero _ (by norm_num)
  have fin : (2 : ℝ≥0∞) ^ 128 ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [show 256 = 128 + 128 from rfl, pow_add, ENNReal.mul_inv (.inl nz) (.inl fin),
    ← mul_assoc ((2 : ℝ≥0∞) ^ 128), ENNReal.mul_inv_cancel nz fin, one_mul]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials
