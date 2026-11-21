module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeOrigin
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeForgery
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticePrice

/-!
# The forgery experiment with first-read and finder chronology

The capped game keeps successful registrations, first searches and the hit flag in one state.

A refused prefix retains the same chronological record and deferred graph.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp EarlierDigest.Ledger CachedCodeword TrialGraphWatch TwoLayerGraph
open scoped ENNReal Classical

abbrev ChronicleState := JointState × List Arrival

@[expose] def initial : ChronicleState :=
  ((((((((∅, ∅), []), fun _ => none), 0), 0, 0), ((∅, ∅), fun _ => none)), false), [])

/-- Project the state seen by the physical message and graph counters. -/
@[expose] def counters (s : ChronicleState) : Observed Registry := s.1.1.1

theorem project_counts {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α)
    (s : ChronicleState) :
    Prod.map id counters <$> (simulateQ (chronicle pp q) p).run s =
      (simulateQ (TrialGraphWatch.observe pp register (fun r b => (target pp r b).isSome)
        q fun w => (digits w).isSome) p).run (counters s) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro t st
  simp [chronicle, joint, watched, counters, QueryImpl.extendState_apply,
    Functor.map_map, bind_pure_comp]

/-- The capped caller retains the first reply at each message address for this parameter. -/
@[expose] noncomputable def chronicleGame (pp : PublicParam) (A : Adversary)
    (left : Nat) (r : ResidualCache pp) :=
  (simulateQ (chronicle pp left) (WeightedCap.capCompOpt fee left ((game pp A).run r))).run initial

/-- Complete the pending labels without discarding a stopped prefix. -/
@[expose] noncomputable def chronicleFill (pp : PublicParam) (A : Adversary)
    (left : Nat) (r : ResidualCache pp) := do
  let z ← chronicleGame pp A left r
  let st ← RelabelState.endFill (counters z.2).1.1.1
  return (z, st)

/-- Erasing notices, snapshots and the flag gives the filled physical game. -/
theorem project_chronicleFill (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp) :
    (fun z => ((z.1.1, counters z.1.2), z.2)) <$> chronicleFill pp A left r =
      filled pp A left r register (fun s b => (target pp s b).isSome) left
        (fun w => (digits w).isSome) (fun _ => none) := by
  have eq := project_counts pp left (WeightedCap.capCompOpt fee left ((game pp A).run r)) initial
  unfold filled chronicleFill chronicleGame
  change _ = (do
    let z ← (simulateQ (TrialGraphWatch.observe pp register _ left _)
      (WeightedCap.capCompOpt fee left ((game pp A).run r))).run (counters initial)
    let y ← RelabelState.endFill z.2.1.1.1
    return (z, y))
  rw [← eq]
  simp [map_bind, bind_map_left]
  apply congrArg
  funext z
  rcases z with ⟨_, _⟩
  rfl

/-- The marked first searches, hits and graph events bound the original forgery advantage. -/
theorem forge_le_chronicle (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2))
    (each : ∀ w : HashOutput, let pp := parameterOfWord w
      let r := SecretEncoding.Residual.localState _ _ (toKeyedState pp (afterWord w))
      Pr{let z ← chronicleFill pp A left r}[accepted (z.1.1.map Prod.fst) ∨
        (graph pp).Conflict z.2] ≤ bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply forge_le_deferred_mixed A left bound bounded
  intro w
  dsimp only
  rw [← project_filled (parameterOfWord w) A left _ register
    (fun s b => (target (parameterOfWord w) s b).isSome) left (fun word =>
      (digits word).isSome) (fun _ => none),
    prEvent_map, ← project_chronicleFill, prEvent_map]
  exact each w

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
