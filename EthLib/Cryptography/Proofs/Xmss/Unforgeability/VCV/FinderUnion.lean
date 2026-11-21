module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChronicleGraph
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChroniclePrices
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishFill
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishPrice

/-!
# The graph and message-digest events share the leanXMSS hash budget

The fee counts each physical hash call in the stateless security game.

Filling the graph after the last charged call preserves both the hit flag and the finder log.

Source: the leanXMSS specification draft, section "Security".
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open Constants HashSig OracleComp OracleSpec EarlierDigest TrialGraphWatch TwoLayerGraph
open scoped ENNReal Classical

private theorem post_event (pp : PublicParam) (A : Adversary) (q : Nat) (r : ResidualCache pp) :
    Pr{let z ← chronicleFill pp A q r}[z.1.2.1.2 = true] =
      Pr{let z ← chronicleGame pp A q r}[z.2.1.2 = true] := by
  unfold chronicleFill
  rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite]
  apply tsum_congr
  intro z
  simp only [bind_pure_comp, prEvent_norm]
  by_cases h : z.2.1.2 = true <;> simp [h]

private theorem double_epsilon : 2 * epsilon = (2 ^ 127 : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold epsilon; finiteness) (by finiteness)).mp
  norm_num [epsilon, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]

private theorem spent_union {α : Type} (run : ProbComp α) (G P F : α → Prop)
    (addressed post pre seed budget : ℝ≥0∞)
    (hg : Pr{let z ← run}[G z] ≤ addressed / 2 ^ 127)
    (hp : Pr{let z ← run}[P z] ≤ post / 2 ^ 128)
    (hf : Pr{let z ← run}[F z] ≤ (2 * epsilon) * pre)
    (paid : addressed + (post + pre) + seed ≤ budget) :
    Pr{let z ← run}[G z ∨ (P z ∨ F z)] ≤ budget / 2 ^ 127 := by
  have early : (2 * epsilon) * pre = pre / 2 ^ 127 := by
    rw [double_epsilon, div_eq_mul_inv, mul_comm]
  have late : post / 2 ^ 128 ≤ post / 2 ^ 127 := by
    gcongr <;> norm_num
  refine (prEvent_or_le _ _ _).trans ((add_le_add le_rfl (prEvent_or_le run P F)).trans ?_)
  refine (add_le_add hg (add_le_add (hp.trans late) (hf.trans_eq early))).trans ?_
  rw [← ENNReal.add_div, ← ENNReal.add_div]
  have available : addressed + (post + pre) ≤ budget := (le_add_right le_rfl).trans paid
  gcongr

attribute [local irreducible] observedGame observedFill chronicleGame chronicleFill graph subgraph

/-- The union of a graph hazard, a registered hit and a partnered first search fits the cap. -/
theorem risk_union (pp : PublicParam) (A : Adversary) (q : Nat) (r : ResidualCache pp)
    (small : q ≤ 2 ^ 127) :
    Pr{let z ← observedFill pp A q r}[
      ((graph pp).Conflict z.2 ∨ (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2)) ∨
      (z.1.2.1.1.2 = true ∨ Hit z.1.2.2)] ≤ (q : ℝ≥0∞) / 2 ^ 127 := by
  have graphPrice := chronological_graph_price pp A q r
  rw [← erase_observedFill, prEvent_map] at graphPrice
  have post := chronological_post_price pp A q r
  dsimp only at post
  rw [← post_event, ← erase_observedFill, prEvent_map] at post
  have early := (finish_event pp A q r Hit).trans_le (actual_price pp A q r small)
  have paid := chronological_budget pp A q r
  exact spent_union (observedFill pp A q r) _ _ _ _ _ _ _ _ graphPrice post early paid

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
