module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerBuildPath

/-!
# Read an authentication path after the bottom root has been computed

The leanXMSS draft, section "The scheme", discloses the path with the successful signature.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig Merkle OracleComp LayerGraph.Hidden

/-- The normalized root read computes a full native tree whose path remains in the graph. -/
theorem root_stores_path (pp : PublicParam) (l : Layer) (h j e : Nat)
    (bound : h ≤ LAYER_HEIGHT) (inside : e / 2 ^ h = j) (s : SharedState) (z : Digest × SharedState)
    (ran : z ∈ support ((simulateQ (graph pp).eagerImpl (simulateQ (selection pp l).liftQuery
      (beforeNode pp l h j >>= fun _ => LayerGraph.readOutput (LayerGraph.treeRole h j)))).run s)) :
    ∃ path : Vector Digest h, ∀ t : SharedState, z.2 ≤ t →
      (simulateQ (graph pp).eagerImpl
        (simulateQ (selection pp l).liftQuery (revealPath h e))).run t = pure (path, t) := by
  let aux : SeedPrf (OracleComp LayerGraph.Spec) := fun _ _ _ => pure (Vector.replicate 32 0)
  let v := selection pp l
  have actualRoot : Xmss.node hash pp (prf pp l aux) l h j =
      Built.value <$> Xmss.build hash pp (prf pp l aux) l h j := (value_build _ _ _).symm
  rw [← node_schedule pp l aux h j bound, actualRoot, simulateQ_map, StateT.run_map,
    support_map] at ran
  obtain ⟨⟨tree, state⟩, actual, rfl⟩ := ran
  have record := (build_recorded pp l aux h j bound s (tree, state) actual).1
  have reads : v.Exact (revealPath h e) :=
    exact_collect pp l h _ fun _ => v.exact_map _ (v.exact_readCell _)
  refine ⟨tree.path h e, fun t later => ?_⟩
  have cached : (simulateQ (LayerGraph.graph pp l).eagerImpl (revealPath h e)).run (v.project t) =
      pure (tree.path h e, v.project t) :=
    read_cached pp l _ _ _ ((record.mono (v.project_mono later)).2 e inside)
  rw [reads t, cached]
  simp [v.extend_project]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
