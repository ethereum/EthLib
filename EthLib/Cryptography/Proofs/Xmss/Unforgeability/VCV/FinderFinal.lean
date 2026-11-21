module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ClassifiedBudget
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderUnion
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedForgery
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ClassifiedForgery

/-!
# Transferring the leanXMSS finder bound to EthLib's keyed signer

A genuine winning execution contributes only the probability of the charged events.

The two key-generation calls pay for the seed terms.

Source: the leanXMSS specification draft, section "Security".
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open Constants HashSig OracleComp OracleSpec TwoLayerGraph SecretEncoding.Residual
open scoped ENNReal Classical

attribute [local irreducible] observedFill chronicleFill graph subgraph guardedGraph mixedGame

/-- Transport a pathwise classification on the physically charged game to the original advantage. -/
private theorem forge_le_of_finder_cases (A : Adversary) (q : Nat) (bounded : HasHashQueryBound A q)
    (each : ∀ (left : Nat) (w : HashOutput),
      let pp := parameterOfWord w
      let r := localState _ _ (toKeyedState pp (afterWord w))
      ∀ z ∈ support (observedFill pp A left r), accepted (z.1.1.1.map Prod.fst) →
        ¬ (graph pp).Conflict z.2 →
        ¬ (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2) →
        z.1.2.1.1.2 = true ∨ Hit z.1.2.2) :
    forgeAdvantage A ≤ (q : ℝ≥0∞) / 2 ^ 127 := by
  apply forge_le_of_classified_budget A q bounded
  intro left hq small w
  dsimp only
  let pp := parameterOfWord w
  let r := localState _ _ (toKeyedState pp (afterWord w))
  rw [← project_graphFill pp A left r, prEvent_map, ← erase_observedFill, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ ?_).trans (risk_union pp A left r (by omega))
  intro z hz h
  change classified pp (z.1.1.1.map Prod.fst) z.2 at h
  unfold classified at h
  rcases h with clash | off | ⟨o, present, won, _⟩
  · exact Or.inl (Or.inl clash)
  · exact Or.inl (Or.inr off)
  by_cases clash : (graph pp).Conflict z.2
  · exact Or.inl (Or.inl clash)
  by_cases off : (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2)
  · exact Or.inl (Or.inr off)
  refine Or.inr (each left w z hz ?_ clash off)
  change z.1.1.1.map Prod.fst = some o at present
  rw [present]
  exact won

/-- The original keyed leanXMSS signer has 127 bits of classical strong unforgeability.

The budget counts every hash call in the stateless experiment, including signing and verification.
-/
theorem _root_.EthLib.Cryptography.Xmss.Unforgeability.keyed_security_127 :
    HasClassicalSecurityBits 127 := by
  intro q _ A bounded
  rw [Nat.cast_pow, Nat.cast_ofNat]
  apply forge_le_of_finder_cases A q bounded
  intro left w
  dsimp only
  intro z hz won clean safe
  exact (filled_cover w A left z hz (Or.inl won)).resolve_left (not_or_intro clean safe)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
