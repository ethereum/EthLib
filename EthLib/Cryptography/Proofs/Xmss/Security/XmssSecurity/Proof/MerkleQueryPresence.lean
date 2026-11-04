module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.MerkleQueryBound
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.QueryPresence
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.StatementLemmas
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

theorem rootTree_merkle_query_cached
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (hnode : targetNode.val < 2 ^ (2 * treeHeight - (targetLevel.val + 1)))
    (root : Digest × (TopIndex → Option (Randomness × Encoding))) (cache largerCache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (hle : cache ≤ largerCache) :
    ∃ output, cache
      (Concrete.CacheView.merkleInput parameter targetLevel targetNode
        (treeNode largerCache parameter secret targetLevel.val
          (Concrete.childNode targetNode false))
        (treeNode largerCache parameter secret targetLevel.val
          (Concrete.childNode targetNode true))) = some output := by
  -- The node runs inside key generation, so its hash input is cached.
  have hvalid : TreeSubtreeValid (targetLevel.val + 1) targetNode := by
    have hlevel := targetLevel.isLt
    have hsplit : 2 ^ (2 * treeHeight - (targetLevel.val + 1)) * 2 ^ (targetLevel.val + 1) =
        lifetime := by
      rw [← pow_add, Nat.sub_add_cancel (by simp only [treeHeight] at *; omega)]
      rfl
    exact (Nat.mul_le_mul_right _ hnode).trans hsplit.le
  obtain ⟨beforeCache, afterCache, value, hnodeRun, hafter⟩ := honestKeygen_runsBelow_treeNode hmem
    (targetLevel.val + 1) targetNode targetLevel.isLt hvalid
  rw [Concrete.treeNode_succ_eq] at hnodeRun
  obtain ⟨left, leftCache, hleft, hrest, hleftLe⟩ := runsBelow_bind_left hnodeRun
  obtain ⟨right, rightCache, hright, hhash, hrightLe⟩ := runsBelow_bind_left hrest
  simp only [targetLevel.isLt, ↓reduceDIte, Concrete.nodeHash_eq] at hhash
  obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter _ _ rightCache afterCache
    value hhash
  have hleftEval := eval_answerFn_largerCache_eq_of_mem_support _ beforeCache leftCache
    largerCache left hleft (hleftLe.trans (hafter.trans hle))
  have hrightEval := eval_answerFn_largerCache_eq_of_mem_support _ leftCache rightCache
    largerCache right hright (hrightLe.trans (hafter.trans hle))
  rw [eval_treeNode] at hleftEval hrightEval
  refine ⟨output, ?_⟩
  rw [hleftEval, hrightEval]
  exact hafter hcached

end XmssSecurity.Concrete.CacheReplay

namespace XmssSecurity

theorem Concrete.keygen_cache_has_merkleInput_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) = some output := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact Concrete.CacheReplay.rootTree_merkle_query_cached parameter secret topSecret topBase level node hnode
    root keyResult.2 largerCache hroot hle

theorem Concrete.keygen_cache_has_merkleInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) = some output :=
  Concrete.keygen_cache_has_merkleInput_in_largerCache keyResult hmem keyResult.2 le_rfl
    level node hnode

theorem Concrete.keygen_cache_merkleInput_eq_none_of_ne_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false),
        Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) :
    keyResult.2 (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right) =
      none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_merkleInput_in_largerCache keyResult hmem largerCache hle
      level node hnode
  cases hforged : keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      apply hne
      apply Concrete.nodePayload_injective
      exact payload_eq_of_tweakableHashInput_eq keyResult.1.2.parameter
        (.merkle level node)
        (Concrete.keygen_cache_unique_merkleAddress keyResult hmem level node
          (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right)
          (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
            (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
              keyResult.1.2.chainStart level.val (Concrete.childNode node false))
            (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
              keyResult.1.2.chainStart level.val (Concrete.childNode node true)))
          forgedOutput honestOutput (by simp [Concrete.CacheView.merkleInput])
          (by simp [Concrete.CacheView.merkleInput]) hforged hhonest)

theorem Concrete.keygen_merkleChildren_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1))) :
    (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) =
    (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) := by
  obtain ⟨initialOutput, hinitial⟩ :=
    Concrete.keygen_cache_has_merkleInput keyResult hmem level node hnode
  obtain ⟨largerOutput, hlarger⟩ :=
    Concrete.keygen_cache_has_merkleInput_in_largerCache keyResult hmem largerCache hle
      level node hnode
  apply Concrete.nodePayload_injective
  exact payload_eq_of_tweakableHashInput_eq keyResult.1.2.parameter (.merkle level node)
    (Concrete.keygen_cache_unique_merkleAddress keyResult hmem level node
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true)))
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true)))
      initialOutput largerOutput (by simp [Concrete.CacheView.merkleInput])
      (by simp [Concrete.CacheView.merkleInput]) hinitial hlarger)

end XmssSecurity
