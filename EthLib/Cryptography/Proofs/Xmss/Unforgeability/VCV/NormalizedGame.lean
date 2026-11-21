module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedCap
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedTariff

/-!
# The normalized game at the conditioned parameter

The selected eager and deferred games use the same guard on every public word.

A refusal retains the shared graph state that may already contain a conflict.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleSpec OracleComp HashSig TwoLayerGraph CanonicalGraph.PairedQueries
open scoped ENNReal

/-- Keep the returned candidate and residual tables, and preserve the graph on refusal. -/
@[expose] def returnedTables {R : Type} (z : (Option Outcome × R) × GraphState) :
    Option (Outcome × R) × GraphState := (z.1.1.map (fun a => (a, z.1.2)), z.2)

attribute [local irreducible] markedRun guardedGraph CanonicalGraph.eagerImpl
attribute [local irreducible] CanonicalGraph.deferredFillDraw

/-- Exact eager normalization gives a single bound on the deferred event.

On a refusal the shared graph is visible to both conflict tests. -/
theorem forge_le_normalized (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2))
    (body : ∀ w : HashOutput,
      OracleComp (Mixed HashInput HashOutput Start Row ChainGraph.Word)
        (Outcome × ResidualCache (parameterOfWord w)))
    (same : ∀ w : HashOutput, let pp := parameterOfWord w
      returnedTables <$> markedRun A left w =ᵈ
        (simulateQ (graph pp).eagerImpl (guardedGraph left (body w))).run (∅, ∅))
    (each : ∀ w : HashOutput, let pp := parameterOfWord w
      Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left (body w))}[
        accepted (z.1.1.map Prod.fst) ∨ (graph pp).Conflict z.2.1] ≤ bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply forge_le_marked A left bound bounded
  intro w
  let pp := parameterOfWord w
  let win := fun o : Option (Outcome × ResidualCache pp) => accepted (o.map Prod.fst)
  have deferred := defer_selected pp left (body w) win
  have observed := (same w).prEvent_eq (fun z => win z.1 ∨ (graph pp).Conflict z.2)
  have project (z : (Option Outcome × ResidualCache pp) × GraphState) :
      win (returnedTables z).1 = accepted z.1.1 := by
    rcases z with ⟨⟨_ | a, r⟩, st⟩ <;> rfl
  refine le_trans ?_ (observed.le.trans (deferred.trans (each w)))
  simp only [prEvent_norm]
  apply le_of_eq
  apply prEvent_congr
  intro z
  change (accepted z.1.1 ∨ (graph pp).Conflict z.2) ↔
    (win (returnedTables z).1 ∨ (graph pp).Conflict z.2)
  rw [project]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
