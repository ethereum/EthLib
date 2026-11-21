module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ForgeryCollision
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedForgery

/-!
# Forgery advantage from graph hazards and signed message collisions

The leanXMSS draft, section "Security", counts all adversarial queries to the physical hash.

The capped experiment retains graph conflicts even when the cap stops before a signature returns.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig TwoLayerGraph Honest OracleComp OracleSpec SecretEncoding.Residual
open scoped ENNReal

/-- Every contributing result has a graph hazard or a collision with a signed message query. -/
def classified (pp : PublicParam) (obs : Option Outcome) (last : SharedState) : Prop :=
  (graph pp).Conflict last ∨ (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project last) ∨
    ∃ o, obs = some o ∧ wins o = true ∧ SignedCollision pp last o

attribute [local irreducible] graph mixedGame guardedGraph simulateQ

/-- Transfer a bound on the three classified events to the original adversary. -/
theorem forge_le_classified (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2))
    (each : ∀ w : HashOutput, let pp := parameterOfWord w
      let r := localState _ _ (toKeyedState pp (afterWord w))
      Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left
        ((mixedGame pp A).run r))}[classified pp (z.1.1.map Prod.fst) z.2.1] ≤ bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply forge_le_deferred_mixed A left bound bounded
  intro w
  apply le_trans _ (each w)
  apply prEvent_mono_of_support
  rintro ⟨⟨outcome, t⟩, last, u⟩ member h
  rcases h with won | clash
  · by_cases clash : (graph (parameterOfWord w)).Conflict last
    · exact Or.inl clash
    by_cases hit : (TwoLayerGraph.keys (parameterOfWord w)).TCHazard
        ((subgraph (parameterOfWord w)).project last)
    · exact Or.inr (Or.inl hit)
    obtain ⟨actual, filled, _⟩ := ((graph (parameterOfWord w)).mem_support_deferredFillDraw_iff
      (ms := pure ()) (oa := guardedGraph left ((mixedGame (parameterOfWord w) A).run
        (localState _ _ (toKeyedState (parameterOfWord w) (afterWord w)))))).mp member
    cases outcome with
    | none => cases won
    | some result =>
      obtain ⟨o, privateTable⟩ := result
      exact Or.inr (Or.inr ⟨o,rfl,won,forgery_collision _ A left _ o privateTable t last actual won
        (RelabelState.le_of_mem_support_endFill filled) clash hit⟩)
  · exact Or.inl clash

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
