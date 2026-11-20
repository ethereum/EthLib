module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphBuildSchedule
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerValues

/-!
# One root and one path from the actual shared bottom tree

The leanXMSS draft, section "The scheme", uses the bottom root as the message signed by the top key.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig Merkle OracleComp LayerGraph.Hidden

/-- Evaluate the source's root, then read the path already present in the same tree. -/
noncomputable def builtPathSchedule (pp : PublicParam) (l : Layer) (h j e : Nat) :
    OracleComp SharedSpec (Digest × Vector Digest h) :=
  simulateQ (selection pp l).liftQuery (do
    beforeNode pp l h j
    let root ← LayerGraph.readOutput (LayerGraph.treeRole h j)
    let path ← revealPath h e
    return (root, path))

/-- The current signer's single build gives the same root, path and shared graph state. -/
theorem build_path_pairs (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp l cb) (h j e : Nat) (bound : h ≤ LAYER_HEIGHT) (inside : e / 2 ^ h = j) :
    simulateQ (graph pp).eagerImpl ((fun tree : Built Digest => (tree.value, tree.path h e)) <$>
      Xmss.build hash pp cb l h j) =
      simulateQ (graph pp).eagerImpl (builtPathSchedule pp l h j e) := by
  let v := selection pp l
  let aux : SeedPrf (OracleComp LayerGraph.Spec) := fun _ _ _ => pure (Vector.replicate 32 0)
  let localPrf := LayerGraph.startPrf pp l aux
  have native : Xmss.build hash pp cb l h j = Xmss.build hash pp (prf pp l aux) l h j := by
    unfold Xmss.build
    rw [leaves_pairs pp l cb paired aux]
  have image := Xmss.build_map_monad (fun {_} p => simulateQ v.liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _) LayerGraph.hash localPrf pp l h j
  simp only [v, hash_image] at image
  rw [native, show Xmss.build hash pp (prf pp l aux) l h j = _ from image.symm,
    ← simulateQ_map]
  ext st : 1
  apply v.run_eq_of_exact (v.exact_map _ (build_selected pp l aux h j bound).2)
  · apply v.exact_bind (beforeNode_pred (fun p => v.Exact p) (v.exact_pure ())
      (fun _ _ a b => v.exact_bind a fun _ => b) v.exact_touchCell pp l h j)
    intro _
    apply v.exact_bind (v.exact_bind (v.exact_readCell _) fun _ =>
      v.exact_bind (v.exact_touchCell _) fun _ => v.exact_pure _)
    intro root
    apply v.exact_bind (exact_collect pp l h _ (fun _ => v.exact_map _ (v.exact_readCell _)))
    intro _
    exact v.exact_pure _
  · intro s
    have same := LayerGraph.Hidden.build_path pp l aux h j e bound inside
    simp only [simulateQ_bind, simulateQ_pure] at same
    rw [LayerGraph.Hidden.node pp l aux h j bound] at same
    simpa only [simulateQ_bind, simulateQ_pure, bind_assoc] using
      congrArg (fun p => StateT.run p s) same

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
