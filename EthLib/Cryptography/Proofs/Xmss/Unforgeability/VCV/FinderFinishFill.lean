module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishGame

/-!
# Fill the original pending graph after recording finder returns

The fill samples its pending cells from the same terminal ledger.

The extra finder observations remain available for the classification of a successful forgery.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig OracleComp TwoLayerGraph
open scoped ENNReal Classical

noncomputable def observedFill (pp : PublicParam) (A : Adversary) (q : Nat)
    (r : ResidualCache pp) := do
  let z ← observedGame pp A q r
  let st ← RelabelState.endFill (counters z.2.1).1.1.1
  return (z,st)

/-- Keeping the filled graph and dropping finder ends recovers the original forgery classifier. -/
theorem erase_observedFill (pp : PublicParam) (A : Adversary) (q : Nat) (r : ResidualCache pp) :
    (fun z => ((z.1.1.1,z.1.2.1),z.2)) <$> observedFill pp A q r = chronicleFill pp A q r := by
  unfold observedFill chronicleFill
  rw [← erase_observedGame pp A q r]
  simp [map_bind, bind_map_left]

/-- Filling preserves the probability of every event on recorded finder results. -/
theorem finish_event (pp : PublicParam) (A : Adversary) (q : Nat) (r : ResidualCache pp)
    (E : List (Finish pp) → Prop) :
    Pr{let z ← observedFill pp A q r}[E z.1.2.2] = Pr{let z ← observedGame pp A q r}[E z.2.2] := by
  unfold observedFill
  rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite]
  apply tsum_congr
  intro z
  simp only [bind_pure_comp, prEvent_norm]
  by_cases h : E z.2.2 <;> simp [h]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
