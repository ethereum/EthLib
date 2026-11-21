module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeGame
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphPost

/-!
# The capped forgery experiment with observed finder calls

The verifier and the pending-cell fill run on the graph state produced by this same caller.

A refusal still returns that graph state to the observer.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleComp OracleSpec TwoLayerGraph TrialGraphWatch
open scoped ENNReal

/-- Run all signing notices, then finish the original pending graph work. -/
@[expose] noncomputable def filled {R : Type} (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp) (notice : FinderNotice → R → R) (registered : R → HashInput → Bool)
    (quota : Nat) (test : HashOutput → Bool) (reg : R) := do
  let z ← (simulateQ (TrialGraphWatch.observe pp notice registered quota test)
    (WeightedCap.capCompOpt fee left ((game pp A).run r))).run (((((∅, ∅), []), reg), 0), 0, 0)
  let last ← RelabelState.endFill z.2.1.1.1
  return (z, last)

/-- The transcript preserves the source output, deferred tables and final filled graph. -/
theorem project_filled {R : Type} (pp : PublicParam) (A : Adversary) (left : Nat)
    (r : ResidualCache pp) (notice : FinderNotice → R → R) (registered : R → HashInput → Bool)
    (quota : Nat) (test : HashOutput → Bool) (reg : R) :
    (fun z => ((z.1.1, z.1.2.1.1.1), z.2, ())) <$>
      filled pp A left r notice registered quota test reg =
      (graph pp).deferredFillDraw (pure ()) (guardedGraph left ((mixedGame pp A).run r)) := by
  have proj := erase_run pp notice registered quota test
    (WeightedCap.capCompOpt fee left ((game pp A).run r))
    (((((∅, ∅), []), reg), 0), 0, 0)
  rw [erase_capped_game] at proj
  unfold CanonicalGraph.deferredFillDraw guardedGraph
  rw [← proj]
  simp [filled, map_bind, bind_map_left]
  apply congrArg
  funext z
  rcases z with ⟨out, state⟩
  rfl

/-- The reduction runs the original adversary with both finder notices at the physical caller. -/
theorem forge_le_filled {R : Type} (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2)) (notice : FinderNotice → R → R)
    (registered : R → HashInput → Bool) (quota : Nat) (test : HashOutput → Bool) (reg : R)
    (each : ∀ w : HashOutput, let pp := parameterOfWord w
      let r := SecretEncoding.Residual.localState _ _ (toKeyedState pp (afterWord w))
      Pr{let z ← filled pp A left r notice registered quota test reg}[
        accepted (z.1.1.map Prod.fst) ∨ (graph pp).Conflict z.2] ≤ bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply forge_le_deferred_mixed A left bound bounded
  intro w
  dsimp only
  rw [← project_filled (parameterOfWord w) A left _ notice registered quota test reg, prEvent_map]
  exact each w

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
