module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphBuild
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphSchedule

/-!
# The two values used from a built bottom tree

The leanXMSS draft, section "The scheme", signs a bottom root and discloses one authentication path.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph.Hidden

open Constants HashSig OracleComp Merkle
open ChainGraph (digestEquiv)

/-- Read only the ordered low sibling rows of the requested leaf. -/
noncomputable def revealPath (height e : Nat) : OracleComp Spec (Vector Digest height) :=
  ofFnInOrder height fun k => digestEquiv.symm <$>
    readCell (some (.inr (.inl (treeRole k.val ((e / 2 ^ k.val) ^^^ 1)))))

/-- The bottom-tree build supplies the root and path, evaluating each leaf once. -/
theorem build_path (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp Spec))
    (h j e : Nat) (bound : h ≤ LAYER_HEIGHT) (inside : e / 2 ^ h = j) :
    simulateQ (graph pp l).eagerImpl ((fun tree : Built Digest => (tree.value, tree.path h e)) <$>
      Xmss.build hash pp (startPrf pp l other) l h j) =
    simulateQ (graph pp l).eagerImpl (do
      let root ← Xmss.node hash pp (startPrf pp l other) l h j
      let path ← revealPath h e
      return (root, path)) := by
  have root : Xmss.node hash pp (startPrf pp l other) l h j =
      Built.value <$> Xmss.build hash pp (startPrf pp l other) l h j :=
    (value_build _ _ _).symm
  rw [root]
  ext s : 1
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, ← bind_pure_comp]
  simp only [bind_assoc, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro tree ran
  have record := build_recorded pp l other h j bound s tree ran
  have path : (simulateQ (graph pp l).eagerImpl (revealPath h e)).run tree.2 =
      pure (tree.1.path h e, tree.2) :=
    read_cached pp l _ _ tree.2 (record.2 e inside)
  rw [path, pure_bind]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph.Hidden
