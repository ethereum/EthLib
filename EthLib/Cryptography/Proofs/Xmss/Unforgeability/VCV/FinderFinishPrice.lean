module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishGame
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishAccumulation
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChroniclePrices

/-!
# The first-search term for the actual adaptive signing client

A stopped search books exactly one pre-search table per key.

The valid-word count and saved selection probabilities pay for all partnered returns.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig Constants OracleComp OracleSpec EarlierDigest EarlierDigest.Ledger TrialGraphWatch
open scoped ENNReal Classical

attribute [local irreducible] game caller chronicleGame

private theorem in_projection {α β : Type} {source : ProbComp α} {target : ProbComp β}
    (f : α → β) (same : f <$> source = target) {z : α} (reached : z ∈ support source) :
    f z ∈ support target := by
  rw [← same, support_map]
  exact ⟨z,reached,rfl⟩

private theorem price_covered (pp : PublicParam) (A : Adversary) (q : Nat) (r : ResidualCache pp)
    {z : Option (Outcome × ResidualCache pp) × ChronicleState}
      (ran : z ∈ support (chronicleGame pp A q r)) :
    savedPrice pp (ledger z.2).2.2 ≤ total allKeys (searchMass pp 0 MAX_RANDOMIZER_TRIALS)
      z.2.1.1.2 +
      ((counters z.2).2.2 : ℝ≥0∞) := by
  let f (u : Option (Outcome × ResidualCache pp) × ChronicleState) := (u.1,u.2.1.1)
  have w : f z ∈ support (booked pp A q r) :=
    in_projection (source := chronicleGame pp A q r) (target := booked pp A q r)
      f (chronicle_booked pp A q r) ran
  let reg := fun s b => (target pp s b).isSome
  have cold : Counted pp allKeys reg initial.1.1 :=
    counted_empty pp allKeys reg (fun _ => none) (fun b => by simp [reg])
  have room : initial.1.1.1.2.1 + q ≤ q := by change 0 + q ≤ q; omega
  have good := counted_cap pp allKeys cut register reg (tracks pp) q
    ((game pp A).run r) q initial.1.1
    cold room (z := (z.1,z.2.1.1)) w
  exact (savedPrice_le pp z.2.1.1.2).trans (add_le_add_right (Nat.cast_le.mpr good.valid) _)

private theorem event_gain {α : Type} {pp : PublicParam} (p : ProbComp α) (state : α → State pp) :
    av p (fun z => gain (state z)) = validRate * Pr{let z ← p}[Hit (state z).2] := by
  rw [prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  by_cases h : Hit (state z).2
  · simp only [gain,h,ite_true]
    exact mul_comm _ _
  · simp only [gain,h,ite_false,mul_zero]

private theorem scale_view {α β : Type} (p : ProbComp α) (h : ProbComp β) (f : α → β)
    (eq : f <$> p = h) (val : β → ℝ≥0∞) :
    av p (fun z => epsilon * val (f z)) = epsilon * mean h val := by
  rw [← eq]
  simp only [av, mean, tsum_prEvent_map_mul, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun z => mul_left_comm _ _ _

private theorem cancel_price {hit old paid trials : ℝ≥0∞}
    (localBound : validRate * hit ≤ epsilon * old) (includeOld : old ≤ paid)
    (charged : paid ≤ (2 * validRate) * trials) : hit ≤ (2 * epsilon) * trials := by
  have bound := localBound.trans (mul_le_mul_right (includeOld.trans charged) epsilon)
  have pos : (0 : ℝ≥0∞) < validRate := ENNReal.div_pos (by norm_num [CODE_SIZE]) (by norm_num)
  have finite : validRate ≠ ⊤ := ENNReal.div_ne_top (by simp) (by norm_num)
  have scaled : validRate * hit ≤ validRate * ((2 * epsilon) * trials) := bound.trans_eq (by ac_rfl)
  have canceled := mul_le_mul_right scaled validRate⁻¹
  simpa only [← mul_assoc validRate⁻¹, ENNReal.inv_mul_cancel pos.ne' finite, one_mul]
    using canceled

/-- Each fresh message trial before registration pays for both layers together.

The rate for partnered first returns is two inverse-digest chances per such physical trial. -/
theorem actual_price (pp : PublicParam) (A : Adversary) (q : Nat) (r : ResidualCache pp)
    (small : q ≤ 2 ^ 127) :
    Pr{let z ← observedGame pp A q r}[Hit z.2.2] ≤ (2 * epsilon) *
      mean (chronicleGame pp A q r) (fun z => ((counters z.2).2.1 : ℝ≥0∞)) := by
  let m := observedGame pp A q r
  let c := chronicleGame pp A q r
  have accumulated :=  all_searches q ((caller pp A).run r) q (initial,[]) (sound_empty pp)
  have emptyValue : gain (pp := pp) (initial,[]) = 0 := by simp [gain,Hit]
  have emptyCost : reserve (pp := pp) (initial,[]) = 0 := by simp [reserve,initial,ledger]
  change av m (fun z => gain z.2) + reserve (pp := pp) (initial,[]) ≤
    gain (pp := pp) (initial,[]) + av m (fun z => reserve z.2) at accumulated
  rw [emptyValue, emptyCost, zero_add, add_zero] at accumulated
  have L : av m (fun z => gain z.2) = validRate * Pr{let z ← m}[Hit z.2.2] := event_gain m Prod.snd
  let weight := fun z : (Option (Outcome × ResidualCache pp)) × ChronicleState =>
    savedPrice pp (ledger z.2).2.2
  have R : av m (fun z => reserve z.2) = epsilon * mean c weight := by
    exact scale_view m c (fun z => (z.1.1,z.2.1)) (erase_observedGame pp A q r) weight
  have upper := chronological_first_price pp A q r small
  dsimp only at upper
  have included : mean c weight ≤ mean c (fun z => total allKeys
      (searchMass pp 0 MAX_RANDOMIZER_TRIALS) z.2.1.1.2 + ((counters z.2).2.2 : ℝ≥0∞)) := by
    apply tsum_le_tsum
    intro z
    by_cases reachable : z ∈ support c
    · exact mul_le_mul_right (price_covered pp A q r reachable) _
    · simp [prEvent_eq_zero_of_not_mem_support c reachable]
  rw [L,R] at accumulated
  exact cancel_price accumulated included upper

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
