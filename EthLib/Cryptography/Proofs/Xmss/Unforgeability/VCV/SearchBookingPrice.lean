module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedgerAllowance
public import VCVio.OracleComp.QueryTracking.CountingOracle.FirstMoment

/-!
# The physical price at a first attempted signing search

A first search can return an old partnered row or create its partner with the final fresh reply.

The pre-registration trials pay for both terms on the same stopped graph execution.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger

open Constants HashSig OracleComp OracleSpec CachedCodeword
open RealClient.GraphPrefix RealClient.GraphPrefix.TrialGraphWatch
open scoped ENNReal Classical

private noncomputable abbrev probability := ENNReal.ofReal TrialMoment.rate

private theorem units : (CODE_SIZE / 2 ^ 128 : ℝ≥0∞) = probability :=
  prEvent_accepted ▸ TrialMoment.fresh_rate

private theorem product_units (n v : Nat) :
    (v : ℝ≥0∞) * (probability * n + (1 - probability) * v) = probability ^ 2 *
      ENNReal.ofReal ((v / TrialMoment.rate) * n + (1 - TrialMoment.rate) *
        (v / TrialMoment.rate) ^ 2) := by
  let r := TrialMoment.rate
  have pos : 0 < r := TrialMoment.rate_range.1
  have off : 0 ≤ 1 - r := sub_nonneg.mpr TrialMoment.rate_range.2
  have product : (v : ℝ) * (r * n + (1-r) * v) =
      r ^ 2 * ((v / r) * n + (1-r) * (v / r) ^ 2) := by field_simp
  have equal := congrArg ENNReal.ofReal product
  simpa only [ENNReal.ofReal_mul v.cast_nonneg, ENNReal.ofReal_add (mul_nonneg pos.le n.cast_nonneg)
    (mul_nonneg off v.cast_nonneg), ENNReal.ofReal_mul pos.le, ENNReal.ofReal_mul off,
    ENNReal.ofReal_mul (sq_nonneg r), ENNReal.ofReal_sub _ pos.le, ENNReal.ofReal_one,
    ENNReal.ofReal_pow pos.le, ENNReal.ofReal_natCast] using equal

/--
The two stopped-search terms cost at most two valid-rate credits per trial in expectation.

Only pre-registration trials count.

Scale by the inverse digest-space size divided by the valid rate to bound first-search hits.
-/
theorem booking_price {Note R α : Type} (pp : PublicParam) (keys : Finset Key) (cut : Note →
    Option Key)
    (notice : Note → R → R) (registered : R → HashInput → Bool)
    (tracks : TracksRegistration pp cut notice registered)
    (r : R) (empty : ∀ b, registered r b = false) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (q : Nat) (small : q ≤ 2 ^ 127) (p : OracleComp (Spec Note) α) (left : Nat) (room : left ≤ q) :
    let initial : Observed R × History := ((((((∅, ∅), []), r), 0), 0, 0), ((∅, ∅), fun _ => none))
    let run := (simulateQ (watched pp cut notice registered q)
      (WeightedCap.capCompOpt fee left p)).run initial
    (∑' z, Pr{let u ← run}[u = z] * (total keys (searchMass pp c fuel) z.2.2 + z.2.1.2.2)) ≤
      (2 * (CODE_SIZE / 2 ^ 128 : ℝ≥0∞)) * ∑' z, Pr{let u ← run}[u = z] * (z.2.1.2.1 : ℝ≥0∞) := by
  intro initial run
  let capped := WeightedCap.capCompOpt fee left p
  let so := observe pp notice registered q fun w => (digits w).isSome
  let m := (simulateQ so capped).run initial.1
  let n := ∑' z, Pr{let u ← run}[u = z] * (z.2.1.2.1 : ℝ≥0∞)
  let v := ∑' z, Pr{let u ← run}[u = z] * (z.2.1.2.2 : ℝ≥0∞)
  let raw (a b : Nat) := ENNReal.ofReal
    ((b / TrialMoment.rate) * a + (1 - TrialMoment.rate) * (b / TrialMoment.rate) ^ 2)
  have erase : Prod.map id Prod.fst <$> run = m :=
    extendState_run_proj_eq so (fun t _ w _ h => update pp cut t w h) capped initial.1 initial.2
  have law := counts (Note := Note) pp notice registered q (fun w =>
      (digits w).isSome) TrialMoment.rate (by
    simpa only [← mem_accepted] using TrialMoment.fresh_rate)
  have first := BernoulliMoment.expected_successes law capped initial.1 rfl rfl
  change (∑' z, Pr{let u ← m}[u = z] * (z.2.2.2 : ℝ≥0∞)) =
    probability * ∑' z, Pr{let u ← m}[u = z] * (z.2.2.1 : ℝ≥0∞) at first
  rw [← erase, tsum_prEvent_map_mul, tsum_prEvent_map_mul] at first
  change v = probability * n at first
  have second := TrialMoment.expected_product_of_counts so _ _ q small law capped initial.1 rfl rfl
  change (∑' z, Pr{let u ← m}[u = z] * raw z.2.2.1 z.2.2.2) ≤ _ *
    ∑' z, Pr{let u ← m}[u = z] * (z.2.2.1 : ℝ≥0∞) at second
  rw [← erase, tsum_prEvent_map_mul, tsum_prEvent_map_mul] at second
  have scaled := second.trans (mul_le_mul_of_nonneg_right
      (TrialMoment.weight_le_digest q small) zero_le)
  change (∑' z, Pr{let u ← run}[u = z] * raw z.2.1.2.1 z.2.1.2.2) ≤ (2 : ℝ≥0∞)^128 * n at scaled
  have paid := watched_product pp keys cut notice registered tracks r empty c fuel within q p left
      room
  dsimp only at paid
  rw [units] at paid
  let old := ∑' z, Pr{let u ← run}[u = z] * total keys (searchMass pp c fuel) z.2.2
  change probability * old ≤ (1 / 2^128 : ℝ≥0∞) *
    ∑' z, Pr{let u ← run}[u = z] * ((z.2.1.2.2 : ℝ≥0∞) *
      (probability * z.2.1.2.1 + (1-probability) * z.2.1.2.2)) at paid
  simp_rw [product_units] at paid
  have swap (a b : ℝ≥0∞) : a * (probability ^ 2 * b) = probability ^ 2 * (a * b) := by ac_rfl
  simp only [swap, ENNReal.tsum_mul_left] at paid
  rw [← swap (1 / 2 ^ 128) _] at paid
  have paid' := paid.trans (mul_le_mul_right (mul_le_mul_right scaled (probability ^ 2))
      (1 / 2^128))
  have pos : probability ≠ 0 := (ENNReal.ofReal_pos.mpr TrialMoment.rate_range.1).ne'
  have finite : probability ≠ ⊤ := ENNReal.ofReal_ne_top
  have unit : (1 / 2 ^ 128 : ℝ≥0∞) * 2 ^ 128 = 1 := by
    rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (ENNReal.pow_ne_top (by norm_num))]
  have old_le : old ≤ probability * n := by
    have scaled' : probability * old ≤ probability * (probability * n) := by
      refine paid'.trans_eq ?_
      calc
        (1 / 2 ^ 128 : ℝ≥0∞) * (probability ^ 2 * (2 ^ 128 * n)) =
            ((1 / 2 ^ 128 : ℝ≥0∞) * 2 ^ 128) * (probability * (probability * n)) := by
              rw [pow_two]; ac_rfl
        _ = _ := by rw [unit, one_mul]
    have canceled := mul_le_mul_right scaled' probability⁻¹
    simpa only [← mul_assoc probability⁻¹, ENNReal.inv_mul_cancel pos finite,
      one_mul] using canceled
  rw [units]
  simp only [mul_add, tsum_add]
  change old + v ≤ (2 * probability) * n
  rw [first, two_mul, add_mul]
  exact add_le_add old_le le_rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger
