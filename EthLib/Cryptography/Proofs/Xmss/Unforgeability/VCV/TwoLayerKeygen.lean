module

public import EthLib.Cryptography.Proofs.Xmss.Reference
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSchedule

/-!
# The parameter and root of a generated public key

The leanXMSS draft, section "The scheme", publishes the derived parameter and the top root.

The parameter returned by its private call determines which graph describes that root.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants OracleComp LayerGraph.Hidden

/-- Use the hidden top-tree schedule when the actual parameter draw selects this graph. -/
@[expose] noncomputable def keySchedule (pp : PublicParam)
    (other : SeedPrf (OracleComp LayerGraph.Spec)) : OracleComp SharedSpec PublicKey := do
  let cb := prf pp .top other
  let drawn ← publicParamOf cb
  let root ← if drawn = pp then
      simulateQ (selection pp .top).liftQuery (beforeNode pp .top LAYER_HEIGHT 0 >>=
        fun _ => LayerGraph.readOutput (LayerGraph.treeRole LAYER_HEIGHT 0))
    else Xmss.node hash drawn cb .top LAYER_HEIGHT 0
  return {root, publicParam := drawn}

/-- The two programs return the same public key and the same complete graph state.

The split keeps the parameter draw and the root computation in a single actual execution. -/
theorem publicKeyOf_schedule (pp : PublicParam) (other : SeedPrf (OracleComp LayerGraph.Spec)) :
    simulateQ (graph pp).eagerImpl (Xmss.publicKeyOf hash (prf pp .top other)) =
      simulateQ (graph pp).eagerImpl (keySchedule pp other) := by
  simp only [Xmss.publicKeyOf, keySchedule, simulateQ_bind]
  apply bind_congr
  intro drawn
  split_ifs with found
  · cases found
    rw [node_schedule pp .top other LAYER_HEIGHT 0 le_rfl]
    simp only [simulateQ_bind]
  · simp only [simulateQ_bind]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
