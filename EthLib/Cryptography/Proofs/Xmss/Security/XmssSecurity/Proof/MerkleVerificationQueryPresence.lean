module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.MerkleQueryPresence
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

@[expose] public section

open EthLib.Cryptography

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Concrete.CacheReplay

set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def verificationAfterEncoding (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (encoding : Encoding) : OracleComp HashSpec Bool := do
  let endpoints ← Concrete.recoverEndpoints publicKey.parameter leafIndex encoding signature
  let leaf ← Concrete.leafHash publicKey.parameter leafIndex endpoints
  Concrete.verifyAfterLeaf publicKey leafIndex signature leaf

attribute [irreducible] verificationAfterEncoding

def verificationAfterEndpoints (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (endpoints : ChainIndex → Digest) : OracleComp HashSpec Bool := do
  let leaf ← Concrete.leafHash publicKey.parameter leafIndex endpoints
  Concrete.verifyAfterLeaf publicKey leafIndex signature leaf

attribute [irreducible] verificationAfterEndpoints

def authenticationRootComputation (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) : OracleComp HashSpec Digest :=
  Merkle.climb (Concrete.nodeAt parameter .bottom) 0 leafIndex.val leaf
    (List.ofFn signature.authPath)

def verificationAfterLeafRoot (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) : OracleComp HashSpec Bool := do
  let root ← authenticationRootComputation publicKey.parameter leafIndex signature leaf
  Concrete.verifyTop publicKey (topKeyOf leafIndex) root signature.top

theorem verificationAfterLeafRoot_eq (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    verificationAfterLeafRoot publicKey leafIndex signature leaf =
      (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool) := by
  rw [Concrete.verifyAfterLeaf_eq]
  unfold verificationAfterLeafRoot authenticationRootComputation
  rfl

attribute [irreducible] authenticationRootComputation verificationAfterLeafRoot

inductive VerifiedDigestRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec) : Prop where
  | intro (actualEncoding : Encoding) (digestCache : QueryCache HashSpec) (digest : Digest)
      (digest_mem : (digest, digestCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
            OracleComp HashSpec Digest)).run initialCache))
      (decode_eq : TargetSum.decodeDigest digest = some actualEncoding)
      (rest_mem : (true, resultCache) ∈ support
        ((simulateQ randomOracle
          (verificationAfterEncoding publicKey leafIndex signature actualEncoding)).run digestCache))
      (digest_le : digestCache ≤ resultCache) :
      VerifiedDigestRun publicKey leafIndex message signature initialCache resultCache

theorem verify_true_digestRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache)) :
    VerifiedDigestRun publicKey leafIndex message signature initialCache resultCache := by
  rw [Concrete.verify_eq] at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hafterDigest⟩ := hmem
  cases hdecode : TargetSum.decodeDigest digest with
  | none =>
      simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Bool.true_eq_false] at hafterDigest
      exact hafterDigest.1.elim
  | some encoding =>
      have hrest : (true, resultCache) ∈ support
          ((simulateQ randomOracle
            (verificationAfterEncoding publicKey leafIndex signature encoding)).run digestCache) := by
        simpa only [hdecode, verificationAfterEncoding] using hafterDigest
      exact .intro encoding digestCache digest hdigest hdecode hrest
        (randomOracle_cache_le
          (verificationAfterEncoding publicKey leafIndex signature encoding)
          digestCache (true, resultCache) hrest)

inductive VerifiedEndpointsRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec) : Prop where
  | intro (actualEncoding : Encoding) (digestCache endpointsCache : QueryCache HashSpec)
      (digest : Digest) (endpoints : ChainIndex → Digest)
      (digest_mem : (digest, digestCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
            OracleComp HashSpec Digest)).run initialCache))
      (decode_eq : TargetSum.decodeDigest digest = some actualEncoding)
      (endpoints_mem : (endpoints, endpointsCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.recoverEndpoints publicKey.parameter leafIndex actualEncoding signature :
            OracleComp HashSpec (ChainIndex → Digest))).run digestCache))
      (rest_mem : (true, resultCache) ∈ support
        ((simulateQ randomOracle
          (verificationAfterEndpoints publicKey leafIndex signature endpoints)).run endpointsCache))
      (digest_le : digestCache ≤ resultCache) (endpoints_le : endpointsCache ≤ resultCache) :
      VerifiedEndpointsRun publicKey leafIndex message signature initialCache resultCache

theorem VerifiedDigestRun.toEndpointsRun
    {publicKey : PublicKey} {leafIndex : LeafIndex} {message : Message} {signature : Signature}
    {initialCache resultCache : QueryCache HashSpec}
    (run : VerifiedDigestRun publicKey leafIndex message signature initialCache resultCache) :
    VerifiedEndpointsRun publicKey leafIndex message signature initialCache resultCache := by
  obtain ⟨actualEncoding, digestCache, digest, hdigest, hdecode, hrest, hdigestLe⟩ := run
  unfold verificationAfterEncoding at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨endpoints, endpointsCache⟩, hendpoints, hafterEndpoints⟩ := hrest
  have hafter : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (verificationAfterEndpoints publicKey leafIndex signature endpoints)).run endpointsCache) := by
    simpa only [verificationAfterEndpoints] using hafterEndpoints
  exact .intro actualEncoding digestCache endpointsCache digest endpoints hdigest hdecode
    hendpoints hafter hdigestLe
    (randomOracle_cache_le (verificationAfterEndpoints publicKey leafIndex signature endpoints)
      endpointsCache (true, resultCache) hafter)

inductive VerifiedLeafRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec) : Prop where
  | intro (actualEncoding : Encoding)
      (digestCache endpointsCache leafCache : QueryCache HashSpec)
      (digest : Digest) (endpoints : ChainIndex → Digest) (leaf : Digest)
      (digest_mem : (digest, digestCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
            OracleComp HashSpec Digest)).run initialCache))
      (decode_eq : TargetSum.decodeDigest digest = some actualEncoding)
      (endpoints_mem : (endpoints, endpointsCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.recoverEndpoints publicKey.parameter leafIndex actualEncoding signature :
            OracleComp HashSpec (ChainIndex → Digest))).run digestCache))
      (leaf_mem : (leaf, leafCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.leafHash publicKey.parameter leafIndex endpoints :
            OracleComp HashSpec Digest)).run endpointsCache))
      (rest_mem : (true, resultCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)).run leafCache))
      (digest_le : digestCache ≤ resultCache) (endpoints_le : endpointsCache ≤ resultCache)
      (leaf_le : leafCache ≤ resultCache) :
      VerifiedLeafRun publicKey leafIndex message signature initialCache resultCache

theorem VerifiedEndpointsRun.toLeafRun
    {publicKey : PublicKey} {leafIndex : LeafIndex} {message : Message} {signature : Signature}
    {initialCache resultCache : QueryCache HashSpec}
    (run : VerifiedEndpointsRun publicKey leafIndex message signature initialCache resultCache) :
    VerifiedLeafRun publicKey leafIndex message signature initialCache resultCache := by
  obtain ⟨actualEncoding, digestCache, endpointsCache, digest, endpoints, hdigest, hdecode,
      hendpoints, hrest, hdigestLe, hendpointsLe⟩ := run
  unfold verificationAfterEndpoints at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨leaf, leafCache⟩, hleaf, hafterLeaf⟩ := hrest
  exact .intro actualEncoding digestCache endpointsCache leafCache digest endpoints leaf hdigest
    hdecode hendpoints hleaf hafterLeaf hdigestLe hendpointsLe
    (randomOracle_cache_le
      (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool)
      leafCache (true, resultCache) hafterLeaf)

theorem authenticationRootRun_of_verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature)
    (leafCache : QueryCache HashSpec) (leaf : Digest) (resultCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
          OracleComp HashSpec Bool)).run leafCache)) :
    ∃ rootCache root,
      (root, rootCache) ∈ support
        ((simulateQ randomOracle
          (authenticationRootComputation publicKey.parameter leafIndex signature leaf)).run
            leafCache) ∧
      rootCache ≤ resultCache := by
  have hmem' : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (verificationAfterLeafRoot publicKey leafIndex signature leaf)).run leafCache) := by
    rw [verificationAfterLeafRoot_eq]
    exact hmem
  unfold verificationAfterLeafRoot at hmem'
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem'
  obtain ⟨⟨root, rootCache⟩, hroot, hresult⟩ := hmem'
  exact ⟨rootCache, root, hroot,
    randomOracle_cache_le (Concrete.verifyTop publicKey (topKeyOf leafIndex) root signature.top :
      OracleComp HashSpec Bool) rootCache (true, resultCache) hresult⟩

inductive VerifiedAuthenticationRootRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature)
    (encoding : Encoding) (resultCache largerCache : QueryCache HashSpec) : Prop where
  | intro (leafCache : QueryCache HashSpec) (leaf : Digest)
      (rootCache : QueryCache HashSpec) (root : Digest)
      (root_mem : (root, rootCache) ∈ support
        ((simulateQ randomOracle
          (authenticationRootComputation publicKey.parameter leafIndex signature leaf)).run
            leafCache))

      (root_le : rootCache ≤ resultCache)
      (leaf_eq : Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep largerCache publicKey.parameter leafIndex chain)
          encoding signature.chainValue) = leaf) :
      VerifiedAuthenticationRootRun publicKey leafIndex signature encoding resultCache largerCache

theorem verify_true_authenticationRoot_support_in_largerCache
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (encoding : Encoding)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache publicKey.parameter leafIndex
        (message, signature.randomness)) = some encoding)
    (hle : resultCache ≤ largerCache) :
    VerifiedAuthenticationRootRun publicKey leafIndex signature encoding resultCache largerCache := by
  have leafRun :=
    ((verify_true_digestRun publicKey leafIndex message signature initialCache resultCache hmem).toEndpointsRun).toLeafRun
  obtain ⟨actualEncoding, digestCache, endpointsCache, leafCache, digest, endpoints, leaf,
      hdigest, hactualDecode, hendpoints, hleaf, hafterLeaf, hdigestLe,
      hendpointsLe, hleafLe⟩ := leafRun
  obtain ⟨rootCache, root, hroot, hrootLe⟩ :=
    authenticationRootRun_of_verifyAfterLeaf publicKey leafIndex signature leafCache leaf
      resultCache hafterLeaf
  have hdigestEval := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
      OracleComp HashSpec Digest)
    initialCache digestCache largerCache digest hdigest (hdigestLe.trans hle)
  rw [eval_encodingHash] at hdigestEval
  have hencoding : actualEncoding = encoding := by
    rw [hdigestEval, hactualDecode] at hdecode
    exact Option.some.inj hdecode
  subst actualEncoding
  have hendpointsEval := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.recoverEndpoints publicKey.parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest))
    digestCache endpointsCache largerCache endpoints hendpoints (hendpointsLe.trans hle)
  rw [eval_recoverEndpoints] at hendpointsEval
  have hleafEval := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.leafHash publicKey.parameter leafIndex endpoints : OracleComp HashSpec Digest)
    endpointsCache leafCache largerCache leaf hleaf (hleafLe.trans hle)
  rw [eval_leafHash] at hleafEval
  refine .intro leafCache leaf rootCache root hroot hrootLe ?_
  exact (congrArg
    (Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex)
    hendpointsEval).trans hleafEval

/-- A run of a climb of a layer's tree caches the pair it hashes into each node on its way.

Each pair is the one the cache's climb computes. -/
theorem climb_query_cached (parameter : PublicParameter) (layer : EthLib.Cryptography.Xmss.Layer)
    (j : Nat) (path : Fin treeHeight → Digest) (leaf : Digest) (levels : Nat)
    (hlevels : levels ≤ treeHeight) (target : MerkleLevel)
    (htarget : target.val < levels) (initialCache resultCache largerCache : QueryCache HashSpec)
    (root : Digest)
    (hmem : (root, resultCache) ∈ support
      ((simulateQ randomOracle
        (Merkle.climb (Concrete.nodeAt parameter layer) 0 j leaf ((List.ofFn path).take levels) :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, resultCache
      (Concrete.CacheView.nodeInput parameter layer target (j / 2 ^ (target.val + 1))
        (Merkle.pairAt (Concrete.CacheView.nodeAt largerCache parameter layer) j path leaf
          target).1
        (Merkle.pairAt (Concrete.CacheView.nodeAt largerCache parameter layer) j path leaf
          target).2) = some output := by
  induction levels generalizing initialCache resultCache root with
  | zero => omega
  | succ levels ih =>
      have hlevel : levels < treeHeight := by omega
      rw [Merkle.climb_take_succ _ j leaf _ levels (by simp; omega), simulateQ_bind,
        StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨current, currentCache⟩, hcurrent, hnode⟩ := hmem
      have hcurrentLe : currentCache ≤ resultCache :=
        randomOracle_cache_le _ currentCache (root, resultCache) hnode
      by_cases heq : target.val = levels
      · obtain rfl : target = ⟨levels, hlevel⟩ := Fin.ext heq
        -- The held node is the cache's climb over the levels below.
        have hcurrentEval := eval_answerFn_largerCache_eq_of_mem_support _
          initialCache currentCache largerCache current hcurrent (hcurrentLe.trans hle)
        rw [eval_climb] at hcurrentEval
        have hparent : j / 2 ^ levels / 2 = j / 2 ^ (levels + 1) := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        rw [Merkle.pairAt, hcurrentEval]
        simp only [List.getElem_ofFn, hparent] at hnode
        rw [nodeAt_eq parameter layer ⟨levels, hlevel⟩, nodeAt_eq parameter layer ⟨levels, hlevel⟩]
          at hnode
        unfold Merkle.ordered
        split at hnode <;> rename_i hbit
        · obtain ⟨output, hcached, -⟩ := tweakableHash_query_cached _ _ _ _ _ _ hnode
          exact ⟨output, by rw [ite_eq_left hbit]; exact hcached⟩
        · obtain ⟨output, hcached, -⟩ := tweakableHash_query_cached _ _ _ _ _ _ hnode
          exact ⟨output, by rw [ite_eq_right hbit]; exact hcached⟩
      · obtain ⟨output, hcached⟩ := ih (by omega) (by omega) initialCache currentCache current
          hcurrent (hcurrentLe.trans hle)
        exact ⟨output, hcurrentLe hcached⟩

set_option maxHeartbeats 1200000 in
set_option linter.constructorNameAsVariable false in
theorem verify_true_merkle_query_cached_as_in_largerCache
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (encoding : Encoding) (target : MerkleLevel)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache publicKey.parameter leafIndex
        (message, signature.randomness)) = some encoding)
    (hle : resultCache ≤ largerCache) :
    ∃ output, resultCache
      (Concrete.CacheView.nodeInput publicKey.parameter .bottom target
        (leafIndex.val / 2 ^ (target.val + 1))
        (Merkle.pairAt (Concrete.CacheView.nodeAt largerCache publicKey.parameter .bottom)
          leafIndex.val signature.authPath
          (Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep largerCache publicKey.parameter
                leafIndex chain)
              encoding signature.chainValue)) target).1
        (Merkle.pairAt (Concrete.CacheView.nodeAt largerCache publicKey.parameter .bottom)
          leafIndex.val signature.authPath
          (Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep largerCache publicKey.parameter
                leafIndex chain)
              encoding signature.chainValue)) target).2) = some output := by
  obtain ⟨leafCache, leaf, rootCache, root, hroot, hrootLe, hleaf⟩ :=
    verify_true_authenticationRoot_support_in_largerCache publicKey leafIndex message signature
      encoding initialCache resultCache largerCache hmem hdecode hle
  unfold authenticationRootComputation at hroot
  rw [← List.take_of_length_le (l := List.ofFn signature.authPath) (i := treeHeight) (by simp)]
    at hroot
  obtain ⟨output, hcached⟩ := climb_query_cached publicKey.parameter .bottom leafIndex.val
    signature.authPath leaf treeHeight le_rfl target target.isLt leafCache rootCache largerCache
    root hroot (hrootLe.trans hle)
  rw [hleaf]
  exact ⟨output, hrootLe hcached⟩

end XmssSecurity.Concrete.CacheReplay
