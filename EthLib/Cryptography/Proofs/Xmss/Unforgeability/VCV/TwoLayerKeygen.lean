module

public import EthLib.Cryptography.Proofs.Xmss.Reference
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerValues

/-!
# The parameter and root of a generated public key

The leanXMSS draft, section "The scheme", publishes the derived parameter and the top root.

The parameter returned by its private call determines which graph describes that root.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants OracleComp LayerGraph.Hidden

/-- Use the hidden top-tree schedule when the actual parameter draw selects this graph. -/
@[expose] noncomputable def keyScheduleOf (pp : PublicParam)
    (cb : SeedPrf (OracleComp SharedSpec)) : OracleComp SharedSpec PublicKey := do
  let drawn ← publicParamOf cb
  let root ← if drawn = pp then
      simulateQ (selection pp .top).liftQuery (beforeNode pp .top LAYER_HEIGHT 0 >>=
        fun _ => LayerGraph.readOutput (LayerGraph.treeRole LAYER_HEIGHT 0))
    else Xmss.node hash drawn cb .top LAYER_HEIGHT 0
  return {root, publicParam := drawn}

/-- The two programs return the same public key and the same complete graph state.

The split keeps the parameter draw and the root computation in a single actual execution. -/
theorem publicKeyOf_schedule_of_pairs (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp .top cb) :
    simulateQ (graph pp).eagerImpl (Xmss.publicKeyOf hash cb) =
      simulateQ (graph pp).eagerImpl (keyScheduleOf pp cb) := by
  simp only [Xmss.publicKeyOf, keyScheduleOf, simulateQ_bind]
  apply bind_congr
  intro drawn
  split_ifs with found
  · cases found
    rw [node_pairs pp .top cb paired LAYER_HEIGHT 0 le_rfl]
    simp only [simulateQ_bind]
  · simp only [simulateQ_bind]

/-- The projected local seed oracle satisfies the pair law at every epoch. -/
noncomputable abbrev keySchedule (pp : PublicParam)
    (other : SeedPrf (OracleComp LayerGraph.Spec)) :=
  keyScheduleOf pp (prf pp .top other)

theorem publicKeyOf_schedule (pp : PublicParam) (other : SeedPrf (OracleComp LayerGraph.Spec)) :
    simulateQ (graph pp).eagerImpl (Xmss.publicKeyOf hash (prf pp .top other)) =
      simulateQ (graph pp).eagerImpl (keySchedule pp other) :=
  publicKeyOf_schedule_of_pairs pp _ (prf_pair pp .top other)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
