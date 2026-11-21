module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialBudget
public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedPotential

/-!
# Expected cost of a registered digest match

The leanXMSS draft in "Security" counts the calls to the public hash.

A fresh message input at a registered key pays one chance in 2^128 of matching its digest.

The number of such inputs can depend on the replies already seen.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials

open Constants HashSig OracleComp OracleSpec PostSigning
open scoped ENNReal

private theorem post_run {α : Type} (pp : PublicParam) (q : Nat) (body : OracleComp WatchQueries α)
    (st : WatchState) (paid : Nat) (clean : st.hit = false) :
    let m := (simulateQ (handler pp q) body).run ((st, paid), 0, 0)
    Pr{let z ← m}[z.2.1.1.hit = true] ≤
      (∑' z, Pr{let u ← m}[u = z] * z.2.1.1.paid) / 2 ^ 128 := by
  let (t : unifSpec.Domain) : Finite (unifSpec.Range t) := UniformAnswerMeasure.finite_range t
  intro m
  let read := randomOracle.Targets.impl (record pp) (messageKey pp) low
  have law := randomOracle.Targets.charged (record pp) (messageKey pp) low
    ((1 : ℝ≥0∞) / 2 ^ 128) (fun b _ _ d => by
      unfold low
      rw [prEvent_halfOf_ofOutput (fun h => h = d)]
      simp)
  have price := law.prEvent_le_expected body st (by simp [clean])
  -- Drop only the trial counters and physical meter, retaining the registered digest watch.
  have view : (fun z : α × (WatchState × Nat) × Nat × Nat => (z.1, z.2.1.1)) <$> m =
      (simulateQ read body).run st := by
    have trials := extendState_run_proj_eq (randomOracle.Targets.counted (record pp) (messageKey pp) low)
      (BernoulliMoment.update q (eligible pp) validReply) body (st, paid) ((0, 0) : Nat × Nat)
    have physical := extendState_run_proj_eq (randomOracle.Targets.impl (record pp) (messageKey pp)
      low) (fun t _ _ _ n => n + randomOracle.Targets.publicCost t) body st paid
    rw [← physical]
    change _ = Prod.map id Prod.fst <$>
      (simulateQ (randomOracle.Targets.counted (record pp) (messageKey pp) low) body).run (st, paid)
    rw [← trials, Functor.map_map]
    rfl
  change Pr{let z ← (simulateQ read body).run st}[z.2.hit = true] ≤
    ∑' z, Pr{let u ← (simulateQ read body).run st}[u = z] *
      ((z.2.paid : ℝ≥0∞) * (1 / 2 ^ 128)) at price
  rw [← view, tsum_prEvent_map_mul] at price
  simpa only [prEvent_norm, div_eq_mul_inv, one_mul, ← ENNReal.tsum_mul_right, mul_assoc]
    using price

/-- The post-signing event costs one inverse digest space per actual registered fresh query. -/
theorem post_price (A : Adversary) (q : Nat) :
    let m := game A q
    Pr{let z ← m}[z.2.1.1.hit = true] ≤
      (∑' z, Pr{let u ← m}[u = z] * z.2.1.1.paid) / 2 ^ 128 := by
  let (t : unifSpec.Domain) : Finite (unifSpec.Range t) := UniformAnswerMeasure.finite_range t
  dsimp only [game]
  rw [prEvent_bind_eq_tsum, tsum_prEvent_bind_mul, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  refine tsum_le_tsum fun z => ?_
  rcases z with ⟨raw, pk, cache, paid⟩
  dsimp only
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (post_run pk.publicParam q _
    ⟨cache, fun _ => none, 0, false⟩ paid rfl) zero_le

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials
