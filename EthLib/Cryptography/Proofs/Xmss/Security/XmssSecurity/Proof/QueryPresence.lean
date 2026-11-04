module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.HonestKeygenRun
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.StatementLemmas
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

theorem tweakableHash_query_cached
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (initialCache finalCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, finalCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.tweakableHash parameter domain payload :
          OracleComp HashSpec Digest)).run initialCache)) :
    ∃ output, finalCache (tweakableHashInput parameter domain payload) = some output ∧
      digest = truncateHash output := by
  unfold Concrete.tweakableHash Concrete.oracleHash at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hrest
  cases hrest
  exact ⟨output, randomOracle_query_caches _ _ _ _ (by simpa using hquery), rfl⟩

theorem leafAt_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output,
      largerCache (Concrete.CacheView.leafInput parameter leafIndex
        (oneTimePublicKey largerCache parameter secret leafIndex)) = some output := by
  unfold Concrete.leafAt at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨endpoints, middleCache⟩, honeTime, hleaf⟩ := hmem
  obtain ⟨output, hcached, _hdigest⟩ := tweakableHash_query_cached parameter
    (.leaf leafIndex) (Concrete.leafPayload endpoints) middleCache resultCache digest
    (by tweakable_hashes at hleaf; exact hleaf)
  have hmiddleLe : middleCache ≤ resultCache :=
    randomOracle_cache_le (Concrete.leafHash parameter leafIndex endpoints :
      OracleComp HashSpec Digest) middleCache (digest, resultCache) hleaf
  have hendpoints := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)) initialCache middleCache largerCache
      endpoints honeTime (hmiddleLe.trans hle)
  rw [eval_oneTimePublicKey] at hendpoints
  refine ⟨output, ?_⟩
  rw [hendpoints]
  exact hle hcached

theorem rootTree_leaf_query_cached
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness) (leafIndex : LeafIndex)
    (root : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅)) :
    ∃ output,
      cache (Concrete.CacheView.leafInput parameter leafIndex
        (oneTimePublicKey cache parameter secret leafIndex)) = some output := by
  -- The leaf runs inside key generation.
  obtain ⟨beforeCache, afterCache, digest, hleaf, hafter⟩ := honestKeygen_runsBelow_treeNode hmem 0
    leafIndex (by omega) (by simp [TreeSubtreeValid])
  rw [Concrete.treeNode_zero_eq] at hleaf
  exact leafAt_query_cached_in_largerCache parameter secret leafIndex beforeCache afterCache cache
    digest hleaf hafter

end XmssSecurity.Concrete.CacheReplay

namespace XmssSecurity.Concrete.CacheReplay

/-- Replaying a WOTS public key after its leaf computation is stable in every larger cache. -/
theorem leafAt_oneTimePublicKey_eq_in_largerCache
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    oneTimePublicKey resultCache parameter secret leafIndex =
      oneTimePublicKey largerCache parameter secret leafIndex := by
  unfold Concrete.leafAt at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨endpoints, middleCache⟩, honeTime, hleaf⟩ := hmem
  have hmiddleLe : middleCache ≤ resultCache :=
    randomOracle_cache_le (Concrete.leafHash parameter leafIndex endpoints :
      OracleComp HashSpec Digest) middleCache (digest, resultCache) hleaf
  have hresult := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)) initialCache middleCache resultCache
      endpoints honeTime hmiddleLe
  have hlarger := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)) initialCache middleCache largerCache
      endpoints honeTime (hmiddleLe.trans hle)
  rw [eval_oneTimePublicKey] at hresult hlarger
  exact hresult.trans hlarger.symm

/-- Every WOTS public key replay is stable after a complete root-tree computation. -/
theorem rootTree_oneTimePublicKey_eq_in_largerCache
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness) (leafIndex : LeafIndex)
    (root : Digest × (TopIndex → Option (Randomness × Encoding))) (cache largerCache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (hle : cache ≤ largerCache) :
    oneTimePublicKey cache parameter secret leafIndex =
      oneTimePublicKey largerCache parameter secret leafIndex := by
  -- The leaf runs inside key generation.
  obtain ⟨beforeCache, afterCache, digest, hleaf, hafter⟩ := honestKeygen_runsBelow_treeNode hmem 0
    leafIndex (by omega) (by simp [TreeSubtreeValid])
  rw [Concrete.treeNode_zero_eq] at hleaf
  have hstable (largerCache : QueryCache HashSpec) (hle : afterCache ≤ largerCache) :=
    leafAt_oneTimePublicKey_eq_in_largerCache parameter secret leafIndex beforeCache afterCache
      largerCache digest hleaf hle
  exact (hstable cache hafter).symm.trans (hstable largerCache (hafter.trans hle))

end XmssSecurity.Concrete.CacheReplay

namespace XmssSecurity

/-- Key generation fixes every honest WOTS public key in all later cache extensions. -/
theorem Concrete.keygen_oneTimePublicKey_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) :
    Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart leafIndex =
      Concrete.CacheReplay.oneTimePublicKey largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart leafIndex := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact Concrete.CacheReplay.rootTree_oneTimePublicKey_eq_in_largerCache
    parameter secret topSecret topBase leafIndex root keyResult.2 largerCache hroot hle

end XmssSecurity

namespace XmssSecurity

/-- Every supported key generation caches the honest leaf input for every leaf index. -/
theorem Concrete.keygen_cache_has_leafInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (leafIndex : LeafIndex) :
    ∃ output,
      keyResult.2 (Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex
        (Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart leafIndex)) = some output := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact Concrete.CacheReplay.rootTree_leaf_query_cached parameter secret topSecret topBase leafIndex root
    keyResult.2 hroot

/-- A distinct leaf payload at the same leaf index is absent immediately after key generation. -/
theorem Concrete.keygen_cache_leafInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest)
    (hne : endpoints ≠ Concrete.CacheReplay.oneTimePublicKey keyResult.2
      keyResult.1.2.parameter keyResult.1.2.chainStart leafIndex) :
    keyResult.2 (Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex endpoints) = none := by
  obtain ⟨honestOutput, hhonest⟩ := Concrete.keygen_cache_has_leafInput keyResult hmem leafIndex
  cases hforged : keyResult.2
      (Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex endpoints) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      apply hne
      apply Concrete.CacheView.leafInput_injective keyResult.1.2.parameter leafIndex
      apply Concrete.keygen_cache_unique_leafAddress keyResult hmem leafIndex
        (Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex endpoints)
        (Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex
          (Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
            keyResult.1.2.chainStart leafIndex))
        forgedOutput honestOutput
      · simp [Concrete.CacheView.leafInput]
      · simp [Concrete.CacheView.leafInput]
      · exact hforged
      · exact hhonest

end XmssSecurity

namespace XmssSecurity.Concrete.CacheReplay

set_option linter.constructorNameAsVariable false in
/-- Take a supported successful verification.

It caches its exact recovered leaf input in every later cache. -/
theorem verify_true_leaf_query_cached_in_largerCache
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding output,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache publicKey.parameter leafIndex
          (message, signature.randomness)) = some encoding ∧
      largerCache (Concrete.CacheView.leafInput publicKey.parameter leafIndex
        (XmssSecurity.recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep largerCache publicKey.parameter leafIndex chain)
          encoding signature.chainValue)) = some output := by
  rw [Concrete.verify_eq] at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hafterDigest⟩ := hmem
  cases hdecode : TargetSum.decodeDigest digest with
  | none =>
      simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Bool.true_eq_false] at hafterDigest
      exact hafterDigest.1.elim
  | some encoding =>
      simp only [hdecode] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterDigest
      obtain ⟨⟨endpoints, endpointsCache⟩, hendpoints, hafterEndpoints⟩ := hafterDigest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterEndpoints
      obtain ⟨⟨leaf, leafCache⟩, hleaf, hafterLeaf⟩ := hafterEndpoints
      have hrestLe : leafCache ≤ resultCache :=
        randomOracle_cache_le
          (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)
          leafCache (true, resultCache) hafterLeaf
      have hleafResultLe : endpointsCache ≤ leafCache :=
        randomOracle_cache_le (Concrete.leafHash publicKey.parameter leafIndex endpoints :
          OracleComp HashSpec Digest) endpointsCache (leaf, leafCache) hleaf
      have hendpointsLe : endpointsCache ≤ largerCache := by
        exact hleafResultLe.trans (hrestLe.trans hle)
      obtain ⟨output, hleafCached, _⟩ := tweakableHash_query_cached publicKey.parameter
        (.leaf leafIndex) (Concrete.leafPayload endpoints) endpointsCache leafCache leaf
        (by tweakable_hashes at hleaf; exact hleaf)
      have hleafLe : leafCache ≤ largerCache := by
        exact hrestLe.trans hle
      have hendpointsEval := eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.recoverEndpoints publicKey.parameter leafIndex encoding signature :
          OracleComp HashSpec (ChainIndex → Digest)) digestCache endpointsCache largerCache
        endpoints hendpoints hendpointsLe
      rw [eval_recoverEndpoints] at hendpointsEval
      have hdigestCacheLe : digestCache ≤ largerCache := by
        have hrecoverLe : digestCache ≤ endpointsCache :=
          randomOracle_cache_le
            (Concrete.recoverEndpoints publicKey.parameter leafIndex encoding signature :
              OracleComp HashSpec (ChainIndex → Digest))
            digestCache (endpoints, endpointsCache) hendpoints
        exact hrecoverLe.trans hendpointsLe
      have hdigestEval := eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
          OracleComp HashSpec Digest) initialCache digestCache largerCache digest hdigest
          hdigestCacheLe
      rw [eval_encodingHash] at hdigestEval
      refine ⟨encoding, output, ?_, ?_⟩
      · rw [hdigestEval]
        exact hdecode
      · rw [hendpointsEval]
        exact hleafLe hleafCached

end XmssSecurity.Concrete.CacheReplay
