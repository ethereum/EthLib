module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChronicleGame

/-!
# Physical prices on one chronological forgery run

The graph, registered-hit and first-search charges use the same final state.

The total physical allowance includes stopped executions.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open Constants HashSig OracleSpec OracleComp CachedCodeword EarlierDigest
    EarlierDigest.Ledger TrialGraphWatch TwoLayerGraph
open scoped ENNReal Classical

private theorem mean_map {α β : Type} (p : ProbComp α) (f : α → β) (v : β → ℝ≥0∞) :
    mean (f <$> p) v = mean p (fun a => v (f a)) := by
  simp only [mean, tsum_prEvent_map_mul]

/-- The complete state projects to the stopped ledger that prices the first searches. -/
theorem chronicle_booked (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp) :
    (fun z => (z.1, z.2.1.1)) <$> chronicleGame pp A left r = booked pp A left r := by
  unfold chronicleGame booked
  let p := WeightedCap.capCompOpt fee left ((game pp A).run r)
  have h := congrArg (fun run => Prod.map id Prod.fst <$> run)
    (chronicle_joint pp left p initial.1 initial.2)
  rw [joint_ledger] at h
  simpa only [p, initial, Functor.map_map, Function.comp_def, Prod.map, id_eq] using h

/-- The search allowance uses the actual caller's pre-registration trial count. -/
theorem chronological_first_price (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp)
    (small : left ≤ 2 ^ 127) :
    let run := chronicleGame pp A left r
    mean run (fun z => total allKeys (searchMass pp 0 MAX_RANDOMIZER_TRIALS) z.2.1.1.2 +
      (counters z.2).2.2) ≤
      (2 * (CODE_SIZE / 2 ^ 128 : ℝ≥0∞)) * mean run (fun z => (counters z.2).2.1) := by
  have paid := first_price pp A left r small
  change mean (booked pp A left r) _ ≤ _ * mean (booked pp A left r) _ at paid
  rw [← chronicle_booked, mean_map, mean_map] at paid
  exact paid

/-- The same run supplies the registered hit and its expected count of later physical calls. -/
theorem chronological_post_price (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp) :
    let run := chronicleGame pp A left r
    Pr{let z ← run}[z.2.1.2 = true] ≤ mean run (fun z => (counters z.2).1.2) / 2 ^ 128 := by
  let p := WeightedCap.capCompOpt fee left ((game pp A).run r)
  let so := trackPost pp register (target pp) left (fun w => (digits w).isSome)
  have view : (fun z => (z.1, counters z.2, z.2.1.2)) <$> chronicleGame pp A left r =
      (simulateQ so p).run (counters initial, false) := by
    have h := congrArg (fun run => Prod.map id (fun s : JointState => (s.1.1, s.2)) <$> run)
      (chronicle_joint pp left p initial.1 initial.2)
    rw [joint_post] at h
    simpa only [so, p, chronicleGame, counters, initial, Functor.map_map,
      Function.comp_def, Prod.map, id_eq] using h
  have price := post_price pp register (target pp) left (fun w => (digits w).isSome) p
    (counters initial)
  change Pr{let z ← (simulateQ so p).run (counters initial, false)}[_] ≤ _ at price
  rw [← view, prEvent_map, ← project_counts pp left p initial, mean_map] at price
  exact price

/-- These expected physical expenditures share the original post-prefix quota. -/
theorem chronological_budget (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp) :
    let run := chronicleGame pp A left r
    mean run (fun z => (addressedInputs pp (counters z.2).1.1.1.1.1).encard) +
      (mean run (fun z => (counters z.2).1.2) + mean run (fun z => (counters z.2).2.1)) +
      mean run (fun z => (seedInputs (counters z.2).1.1.1.1.1).encard) ≤ left := by
  have paid := expected_budget pp register (fun s b => (target pp s b).isSome) left
    (fun w => (digits w).isSome)
    ((game pp A).run r) left (fun _ => none)
  dsimp only at paid
  have view := project_counts pp left (WeightedCap.capCompOpt fee left ((game pp A).run r)) initial
  dsimp only [counters, initial] at view
  rw [← view, mean_map, mean_map, mean_map, mean_map] at paid
  exact paid

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
