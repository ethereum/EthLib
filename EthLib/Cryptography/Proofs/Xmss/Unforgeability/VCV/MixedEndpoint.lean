module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedClient
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedGame

/-!
# The graph game's observation after the last marked query

A matching normalized mixed computation produces the same ordinary and label tables on every path.

A completed run also retains the residual tables, public key, candidate, raw log and verifier reply.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig TwoLayerGraph Honest OracleComp OracleSpec SecretEncoding.Residual
open CanonicalGraph.PairedQueries

attribute [local irreducible] markedContinuation inGraph selectedImpl

/-- Eliminate only the remaining quota from the full operational comparison. -/
theorem markedRun_mixed (A : Adversary) (q : Nat) (w : HashOutput)
    (m : MixedLocal (parameterOfWord w) Outcome)
    (same : let pp := parameterOfWord w
      MixedAt pp q (localState _ _ (toKeyedState pp (afterWord w)))
        (simulateQ (selectedImpl pp) (markedContinuation A pp)) m) :
    let pp := parameterOfWord w
    let extra := localState _ _ (toKeyedState pp (afterWord w))
    returnedTables <$> markedRun A q w =
      (simulateQ (graph pp).eagerImpl (guardedGraph q (m.run extra))).run (∅, ∅) := by
  let pp := parameterOfWord w
  let r := localState _ _ (toKeyedState pp (afterWord w))
  let orig := simulateQ (selectedImpl pp) (markedContinuation A pp)
  have operational : simulateQ (graph pp).eagerImpl (visible <$> ((orig.run.run q).run r)) =
      simulateQ (graph pp).eagerImpl (((simulateQ mixedImpl (m.run r)).run).run q) := same
  have noQuota := congrArg (fun (body : StateT SharedState ProbComp _) =>
    (fun p => (p.1.1, p.2)) <$> body.run (∅, ∅)) operational
  have capped := WeightedCap.run_guard (mixedCost (H := ChainGraph.Word)
      (F := HashOutput) (fun _ => 0))
    (expand PairedHashWord.halves) (m.run r) q
  change Prod.fst <$> (((simulateQ mixedImpl (m.run r)).run).run q) =
    guardedGraph q (m.run r) at capped
  dsimp only
  rw [markedRun_guard, ← capped]
  simp only [StateT.run_map, simulateQ_map, Functor.map_map] at noQuota ⊢
  exact noQuota

open scoped ENNReal in
/-- The original security game uses the deferred bound once after matching the warm caller. -/
theorem forge_le_mixed_at (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2))
    (m : ∀ w : HashOutput, MixedLocal (parameterOfWord w) Outcome)
    (same : ∀ w : HashOutput, let pp := parameterOfWord w
      MixedAt pp left (localState _ _ (toKeyedState pp (afterWord w)))
        (simulateQ (selectedImpl pp) (markedContinuation A pp)) (m w))
    (each : ∀ w : HashOutput, let pp := parameterOfWord w
      let r := localState _ _ (toKeyedState pp (afterWord w))
      Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left ((m w).run r))}[
        accepted (z.1.1.map Prod.fst) ∨ (graph pp).Conflict z.2.1] ≤ bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  exact forge_le_normalized A left bound bounded
    (fun w => (m w).run (localState _ _ (toKeyedState _ (afterWord w))))
    (fun w => by rw [markedRun_mixed A left w (m w) (same w)]) each

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
