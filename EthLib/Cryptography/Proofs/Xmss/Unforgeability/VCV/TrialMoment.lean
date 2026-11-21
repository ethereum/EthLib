module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CachedCodeword
public import VCVio.OracleComp.QueryTracking.CountingOracle.FreshTrials

/-!
# The second moment of the number of valid message trials

The leanXMSS draft in "WOTS+C", paragraph "Codewords", defines which digests the signer accepts.

The "Security" section charges hash calls throughout the signing game.

A fresh message trial counts once and accepts with the fraction of digests that are codewords.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TrialMoment

open Constants OracleSpec OracleComp CachedCodeword HashSig
open scoped ENNReal

/-- Fraction of the 16-byte digests that pass the codeword test. -/
@[expose] noncomputable def rate : ℝ := (CODE_SIZE : ℝ) / 2 ^ 128

/-- The probability in the actual fresh full-word draw has this real-valued rate. -/
theorem fresh_rate :
    Pr{let w ← $ᵗ HashOutput}[w ∈ accepted] = ENNReal.ofReal rate := by
  rw [prEvent_accepted, rate, ENNReal.ofReal_div_of_pos (by positivity)]
  norm_num

/-- The real-valued rate is strictly between zero and one. -/
theorem rate_range : 0 < rate ∧ rate ≤ 1 := by norm_num [rate, CODE_SIZE]

/-- With n physical trials so far, the linear part of the reserve uses the global budget q. -/
@[expose] noncomputable def linearWeight (q : ℕ) : ℝ :=
  (2 - rate + 3 * (1 / 2 ^ 53) / 2) * q

/-- This coefficient pays for variation of the actual success count about its mean. -/
@[expose] noncomputable def squareWeight : ℝ := 1 - rate + 3 * (2 ^ 53) / 2

/-- The reserve covers the product of valid trials and occupied rows after any bounded path. -/
theorem covers (q v c n : ℕ) (occupied : c ≤ n) (budget : n ≤ q) :
    (v / rate) * c + (1 - rate) * (v / rate) ^ 2 ≤
      BernoulliMoment.reserve rate (linearWeight q) squareWeight v n :=
  BernoulliMoment.covers rate_range.1 rate_range.2 v.cast_nonneg n.cast_nonneg
    (by exact_mod_cast occupied) (by exact_mod_cast budget) (by norm_num) (by norm_num)
    (by norm_num)

/-- A counted fresh trial adds at most this amount in expectation for every nontrivial budget. -/
theorem price_le (q : ℕ) (hq : q ≤ 2 ^ 127) :
    BernoulliMoment.price rate (linearWeight q) squareWeight ≤ (2 - rate) * q + 2 ^ 76 := by
  have bound : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  have extra : 3 * ((1 : ℝ) / 2 ^ 53) / 2 * q + squareWeight * ((1 - rate) / rate) ≤
      2 ^ 76 := by
    calc
      _ ≤ 3 * ((1 : ℝ) / 2 ^ 53) / 2 * 2 ^ 127 + squareWeight * ((1 - rate) / rate) := by gcongr
      _ ≤ _ := by norm_num [squareWeight, rate, CODE_SIZE]
  unfold BernoulliMoment.price linearWeight
  linarith

/-- Below the 127-bit security threshold the moment coefficient fits in one digest space. -/
theorem weight_le_digest (q : ℕ) (hq : q ≤ 2 ^ 127) :
    ENNReal.ofReal ((2 - rate) * q + 2 ^ 76) ≤ (2 : ℝ≥0∞) ^ 128 := by
  have budget : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  have top : (2 - rate) * q + 2 ^ 76 ≤ (2 : ℝ) ^ 128 := by
    calc
      _ ≤ (2 - rate) * 2 ^ 127 + 2 ^ 76 :=
        add_le_add (mul_le_mul_of_nonneg_left budget (by linarith [rate_range.2] : 0 ≤ 2 - rate))
          le_rfl
      _ ≤ _ := by norm_num [rate, CODE_SIZE]
  simpa using ENNReal.ofReal_le_ofReal top

/-- The monitored run keeps every original hash reply and every cache entry.

It counts the first q eligible cache misses and the codewords among those replies.
-/
noncomputable abbrev observe (q : ℕ) (eligible : HashInput → HashSpec.QueryCache → Bool) :=
  randomOracle.FreshTrials.observe q accepted eligible

/-- The reserve charges the expected product to the number of trials actually counted. -/
theorem expected_product_of_counts {ι σ γ : Type} {spec : OracleSpec ι}
    (so : QueryImpl spec (StateT σ ProbComp)) (n v : σ → ℕ) (q : ℕ) (hq : q ≤ 2 ^ 127)
    (law : BernoulliMoment.CountsTrials so n v rate q) (oa : OracleComp spec γ) (st : σ)
    (hn : n st = 0) (hv : v st = 0) :
    let m := (simulateQ so oa).run st
    (∑' z, Pr{let u ← m}[u = z] * ENNReal.ofReal
      ((v z.2 / rate) * n z.2 + (1 - rate) * (v z.2 / rate) ^ 2)) ≤
      ENNReal.ofReal ((2 - rate) * q + 2 ^ 76) *
        ∑' z, Pr{let u ← m}[u = z] * (n z.2 : ℝ≥0∞) := by
  intro m
  have cap := law.trials_le oa st (by simp [hn])
  have ha : 0 ≤ linearWeight q := by
    unfold linearWeight
    exact mul_nonneg (by linarith [rate_range.2]) q.cast_nonneg
  have hb : 0 ≤ squareWeight := by
    unfold squareWeight
    linarith [rate_range.2]
  calc
    _ ≤ ∑' z, Pr{let u ← m}[u = z] *
        ENNReal.ofReal (BernoulliMoment.reserve rate (linearWeight q) squareWeight
          (v z.2) (n z.2)) := by
      refine tsum_le_tsum fun z => ?_
      by_cases hz : z ∈ support m
      · exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
          (covers q (v z.2) (n z.2) (n z.2) le_rfl (cap z hz))) zero_le
      · simp only [prEvent_eq_zero_of_not_mem_support m hz, zero_mul, le_refl]
    _ = ENNReal.ofReal (BernoulliMoment.price rate (linearWeight q) squareWeight) *
        ∑' z, Pr{let u ← m}[u = z] * ((n z.2) : ℝ≥0∞) :=
      BernoulliMoment.run_reserve _ _ _ rate _ _ q rate_range.1 rate_range.2 ha hb law
        oa st hn hv
    _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (price_le q hq)) zero_le

/-- The product at the end of an adaptive run is charged to the expected trials it took.

The caller can choose the next physical hash input after inspecting the full previous word.

Eligibility is decided from the cache before the draw.
-/
theorem expected_product_le {γ : Type} (oa : OracleComp HashSpec γ)
    (cache : HashSpec.QueryCache) (eligible : HashInput → HashSpec.QueryCache → Bool)
    (q : ℕ) (hq : q ≤ 2 ^ 127) :
    let m := (simulateQ (observe q eligible) oa).run (cache, 0, 0)
    (∑' z, Pr{let u ← m}[u = z] * ENNReal.ofReal
      ((z.2.2.2 / rate) * z.2.2.1 + (1 - rate) * (z.2.2.2 / rate) ^ 2)) ≤
      ENNReal.ofReal ((2 - rate) * q + 2 ^ 76) *
        ∑' z, Pr{let u ← m}[u = z] * (z.2.2.1 : ℝ≥0∞) :=
  expected_product_of_counts _ _ _ q hq
    (randomOracle.FreshTrials.countsTrials q accepted eligible rate fresh_rate)
    oa (cache, 0, 0) rfl rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TrialMoment
