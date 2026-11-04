module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.TreeQueryBound
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.StatementLemmas
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

@[expose] public section

namespace XmssSecurity

def MerkleAddressInSubtree (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) : Prop :=
  targetLevel.val < levels ∧
    TreeCovers (levels - (targetLevel.val + 1)) node targetNode

instance (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) :
    Decidable (MerkleAddressInSubtree targetLevel targetNode levels node) := by
  unfold MerkleAddressInSubtree
  infer_instance

theorem treeCovers_unique {levels : Nat} {left right leafIndex : MerkleNode}
    (hleft : TreeCovers levels left leafIndex) (hright : TreeCovers levels right leafIndex) :
    left = right := by
  unfold TreeCovers at hleft hright
  apply Fin.ext
  rw [← Nat.div_eq_of_lt_le hleft.1 hleft.2, ← Nat.div_eq_of_lt_le hright.1 hright.2]

open OracleComp OracleSpec

theorem Concrete.treeNode_queryBound_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode))
        (if MerkleAddressInSubtree targetLevel targetNode levels node then 1 else 0) := by
  rw [Concrete.treeNode]
  have hbound := node_queryBound_node (Concrete.nodeAt parameter .bottom)
    (fun j => Concrete.leafAt parameter secret (Concrete.merkleNodeOfNat j)) _ lifetime
    (targetLevel.val + 1) targetNode.val
    (by omega) (fun j => Concrete.leafAt_queryBound_zero_merkleAddress parameter secret _
      targetLevel targetNode) (fun k j left right hj => by
        simpa [Concrete.nodeDomain] using Concrete.nodeAt_queryBound_node parameter .bottom
          targetLevel targetNode.val targetNode.isLt k j
          (by have := Nat.one_le_two_pow (n := k); simp only [Concrete.layerLeaves]; nlinarith)
          left right) levels node.val hvalid
  have hiff : MerkleAddressInSubtree targetLevel targetNode levels node ↔
      targetLevel.val + 1 ≤ levels ∧
      targetNode.val / 2 ^ (levels - (targetLevel.val + 1)) = node.val := by
    rw [MerkleAddressInSubtree, treeCovers_iff, Nat.succ_le_iff]
  simpa only [hiff] using hbound

theorem Concrete.rootTree_queryBound_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode)) 1 := by
  have hbound (key : TopIndex) := Concrete.treeNode_queryBound_merkleAddress parameter secret
    targetLevel targetNode treeHeight (Concrete.bottomRootNode key)
    (treeSubtreeValid_bottomRootNode key)
  have htop := rejectsTop_atHashAddress parameter (.merkle targetLevel targetNode) rfl
  by_cases hex : ∃ key, MerkleAddressInSubtree targetLevel targetNode treeHeight
      (Concrete.bottomRootNode key)
  · obtain ⟨target, htarget⟩ := hex
    refine Concrete.honestKeygen_queryBound_one parameter _ secret topSecret _ target htop
      (fun _ _ => by simp) (by simpa [htarget] using hbound target) fun key hne => ?_
    have hnot : ¬ MerkleAddressInSubtree targetLevel targetNode treeHeight
        (Concrete.bottomRootNode key) := fun hkey => hne (by
      have := treeCovers_unique hkey.2 htarget.2
      exact Fin.ext (by simpa [Concrete.bottomRootNode] using this))
    simpa [hnot] using hbound key
  · simp only [not_exists] at hex
    exact (Concrete.honestKeygen_queryBound_of_bottomTrees parameter _ secret topSecret _
      (fun _ => 0) 0 htop (fun _ _ => by simp) (fun key => by simpa [hex key] using hbound key)
      fun computation h => Concrete.sequenceFin_queryBound_zero computation _ h).mono (by omega)


theorem Concrete.CacheReplay.rootTree_cache_unique_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (root : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.merkle targetLevel targetNode) left)
    (hrightP : AtHashAddress parameter (.merkle targetLevel targetNode) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right := by
  exact Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.merkle targetLevel targetNode)) ∅ cache root
    (Concrete.rootTree_queryBound_merkleAddress parameter secret topSecret topBase targetLevel targetNode)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

end XmssSecurity
