module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CacheVerify
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.LazyScheme
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.StatementLemmas
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

@[expose] public section

open EthLib.Cryptography

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def answer (cache : QueryCache HashSpec) (input : HashInput) : HashOutput :=
  (cache input).getD 0

def answerFn (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => answer cache input

@[simp]
theorem truncateHash_answer (cache : QueryCache HashSpec) (input : HashInput) :
    truncateHash (answer cache input) = CacheView.digestAt cache input := by
  cases hcache : cache input with
  | none =>
      simp only [answer, CacheView.digestAt, hcache, Option.getD_none]
      exact truncateHash_zero
  | some output => simp [answer, CacheView.digestAt, hcache]

@[simp]
theorem eval_oracleHash (cache : QueryCache HashSpec) (input : HashInput) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.oracleHash input : OracleComp HashSpec HashOutput) = answer cache input := by
  simp [Concrete.oracleHash, answerFn]


@[simp]
theorem eval_tweakableHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      CacheView.tweakableHash cache parameter domain payload := by
  simp [Concrete.tweakableHash, CacheView.tweakableHash]

@[simp]
theorem eval_encodingHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.encodingHash parameter leafIndex message randomness : OracleComp HashSpec Digest) =
      CacheView.encodingHash cache parameter leafIndex (message, randomness) := by
  simp [Concrete.encodingHash_eq, CacheView.encodingHash, CacheView.encodingInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_chainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.chainWalk parameter leafIndex chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain) position steps value := by
  induction steps with
  | zero => simp [Concrete.chainWalk, Wots.walk]
  | succ steps ih =>
      simp only [Concrete.chainWalk, evalWithAnswerFn_bind, ih, Wots.walk]
      by_cases hposition : position + steps < chainLength - 1
      · simp [hposition, Concrete.chainHash_eq, CacheView.chainStep,
          CacheView.chainInput, CacheView.tweakableHash]
      · simp [hposition, CacheView.chainStep]

@[simp]
theorem eval_recoverChain (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.recoverChain parameter leafIndex chain digit value : OracleComp HashSpec Digest) =
      Wots.recoverChain (CacheView.chainStep cache parameter leafIndex chain) digit value := by
  simp [Concrete.recoverChain, Wots.recoverChain]

@[simp]
theorem eval_sequenceFin (cache : QueryCache HashSpec) {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn (answerFn cache) (Concrete.sequenceFin computation) =
      fun index => evalWithAnswerFn (answerFn cache) (computation index) := by
  induction n with
  | zero =>
      funext index
      exact Fin.elim0 index
  | succ n ih =>
      simp only [Concrete.sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

@[simp]
theorem eval_recoverEndpoints (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (encoding : Encoding)
    (signature : Signature) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.recoverEndpoints parameter leafIndex encoding signature :
        OracleComp HashSpec (ChainIndex → Digest)) =
      XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache parameter leafIndex chain)
        encoding signature.chainValue := by
  funext chain
  simp [Concrete.recoverEndpoints, XmssSecurity.recoveredEndpoints]

@[simp]
theorem eval_leafHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.leafHash parameter leafIndex endpoints : OracleComp HashSpec Digest) =
      CacheView.leafHash cache parameter leafIndex endpoints := by
  simp [Concrete.leafHash_eq, CacheView.leafHash, CacheView.leafInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_nodeHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.nodeHash parameter level node left right : OracleComp HashSpec Digest) =
      CacheView.merkleHash cache parameter level node left right := by
  simp [Concrete.nodeHash_eq, CacheView.merkleHash, CacheView.merkleInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_oneTimePublicKey (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.oneTimePublicKey parameter secret leafIndex :
        OracleComp HashSpec (ChainIndex → Digest)) =
      oneTimePublicKey cache parameter secret leafIndex := by
  funext chain
  simp [Concrete.oneTimePublicKey, oneTimePublicKey]

@[simp]
theorem eval_leafAt (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.leafAt parameter secret leafIndex : OracleComp HashSpec Digest) =
      leafAt cache parameter secret leafIndex := by
  simp [Concrete.leafAt, leafAt]

@[simp]
theorem eval_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.treeNode parameter secret levels node : OracleComp HashSpec Digest) =
      treeNode cache parameter secret levels node := by
  induction levels generalizing node with
  | zero => simp [Concrete.treeNode_zero_eq, treeNode_zero_eq]
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      simp only [evalWithAnswerFn_bind, ih, treeNode_succ_eq]
      split <;> simp_all

@[simp]
theorem eval_topChainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.topChainWalk parameter key chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.topChainStep cache parameter key chain) position steps value := by
  induction steps with
  | zero => simp [Concrete.topChainWalk, Wots.walk]
  | succ steps ih =>
      simp only [Concrete.topChainWalk, evalWithAnswerFn_bind, ih, Wots.walk]
      by_cases hposition : position + steps < chainLength - 1
      · simp [hposition, Concrete.topChainHash_eq, CacheView.topChainStep,
          CacheView.topChainInput, CacheView.tweakableHash]
      · simp [hposition, CacheView.topChainStep]

@[simp]
theorem eval_topLeafAt (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest) (key : TopIndex) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.topLeafAt parameter topSecret key : OracleComp HashSpec Digest) =
      topLeafAt cache parameter topSecret key := by
  have hkey : evalWithAnswerFn (answerFn cache)
      (Concrete.topOneTimePublicKey parameter topSecret key :
        OracleComp HashSpec (ChainIndex → Digest)) =
      topOneTimePublicKey cache parameter topSecret key := by
    funext chain
    simp [Concrete.topOneTimePublicKey, topOneTimePublicKey]
  simp [Concrete.topLeafAt, topLeafAt, hkey, Concrete.topLeafHash_eq, CacheView.topLeafHash,
    CacheView.topLeafInput, CacheView.tweakableHash]

@[simp]
theorem eval_topTreeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (levels : Nat) (node : TopNode) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.topTreeNode parameter topSecret levels node : OracleComp HashSpec Digest) =
      topTreeNode cache parameter topSecret levels node := by
  induction levels generalizing node with
  | zero =>
      rw [topTreeNode_zero_eq]
      exact eval_topLeafAt cache parameter topSecret node
  | succ levels ih =>
      rw [Concrete.topTreeNode, topTreeNode_succ_eq]
      simp only [evalWithAnswerFn_bind, ih]
      split <;> simp_all [Concrete.topNodeHash_eq, CacheView.topMerkleHash,
        CacheView.topMerkleInput, CacheView.tweakableHash]

/-! The statement stores the precomputed secret key as runs of its own oracle algorithms.

Each run replays the hash from the cache, with the same answer function.

So the evaluation lemmas above give the first-order forms of the stored tables.

These forms are the cache views and the cache replays. -/

theorem answerFn_eq_replayHash (cache : QueryCache HashSpec) :
    answerFn cache = Concrete.replayHash cache := rfl

@[simp]
theorem eval_replayHash_chainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (Concrete.replayHash cache)
      (Concrete.chainWalk parameter leafIndex chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain) position steps value := by
  rw [← answerFn_eq_replayHash]
  exact eval_chainWalk cache parameter leafIndex chain position steps value

@[simp]
theorem eval_replayHash_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    evalWithAnswerFn (Concrete.replayHash cache)
      (Concrete.treeNode parameter secret levels node : OracleComp HashSpec Digest) =
      treeNode cache parameter secret levels node := by
  rw [← answerFn_eq_replayHash]
  exact eval_treeNode cache parameter secret levels node

@[simp]
theorem eval_replayHash_topChainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (Concrete.replayHash cache)
      (Concrete.topChainWalk parameter key chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.topChainStep cache parameter key chain) position steps value := by
  rw [← answerFn_eq_replayHash]
  exact eval_topChainWalk cache parameter key chain position steps value

@[simp]
theorem eval_replayHash_topTreeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (levels : Nat) (node : TopNode) :
    evalWithAnswerFn (Concrete.replayHash cache)
      (Concrete.topTreeNode parameter topSecret levels node : OracleComp HashSpec Digest) =
      topTreeNode cache parameter topSecret levels node := by
  rw [← answerFn_eq_replayHash]
  exact eval_topTreeNode cache parameter topSecret levels node

@[simp]
theorem precomputedSecretKey_chainValue (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache).chainValue leafIndex chain digit =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain) 0 digit.val
        (secret leafIndex chain) :=
  eval_replayHash_chainWalk cache parameter leafIndex chain 0 digit.val (secret leafIndex chain)

@[simp]
theorem precomputedSecretKey_treeValue (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (cache : QueryCache HashSpec)
    (height : MerkleHeight) (node : MerkleNode) :
    (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache).treeValue height node =
      treeNode cache parameter secret height.val node :=
  eval_replayHash_treeNode cache parameter secret height.val node

def signedChainValues (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => Wots.walk
    (CacheView.chainStep cache secretKey.parameter leafIndex chain) 0
    (encoding chain).val (secretKey.chainStart leafIndex chain)

def authenticationPath (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) : Fin treeHeight → Digest :=
  fun level => treeNode cache secretKey.parameter secretKey.chainStart level.val
    (Concrete.authenticationPathNode leafIndex level)

/-- The honest top signature of bottom tree `b`, replayed from the cache. -/
def topPartFromCache (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex) :
    LayerSignature :=
  match secretKey.topSigned key with
  | some (randomness, encoding) =>
      ⟨randomness, Concrete.honestTopValues cache secretKey key encoding,
        Concrete.honestTopPath cache secretKey key⟩

  | none => ⟨0, fun _ => 0, fun _ => 0⟩

def signWithEncoding (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding) : Signature :=
  ⟨randomness, signedChainValues cache secretKey leafIndex encoding,
    authenticationPath cache secretKey leafIndex, topPartFromCache cache secretKey (topKeyOf leafIndex)⟩

theorem precomputedSignedChainValues_eq (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (encoding : Encoding) :
    (fun chain => (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache).chainValue leafIndex chain (encoding chain)) =
      signedChainValues cache (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache)
        leafIndex encoding := by
  funext chain
  exact precomputedSecretKey_chainValue parameter secret topSecret topSigned cache leafIndex chain (encoding chain)

theorem precomputedAuthenticationPath_eq (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (cache : QueryCache HashSpec) (leafIndex : LeafIndex) :
    (fun level : Fin treeHeight => (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache).treeValue
        level.castSucc (Concrete.authenticationPathNode leafIndex level)) =
      authenticationPath cache (Concrete.precomputedSecretKey parameter secret topSecret topSigned cache)
        leafIndex := by
  funext level
  exact precomputedSecretKey_treeValue parameter secret topSecret topSigned cache level.castSucc
    (Concrete.authenticationPathNode leafIndex level)

/-- A node of a layer's tree is a tweakable hash at its address, below the layer's leaf count. -/
theorem nodeAt_eq (parameter : PublicParameter) (layer : EthLib.Cryptography.Xmss.Layer)
    (level : MerkleLevel) (j : Nat) (hj : j < CacheView.layerLeaves layer) (left right : Digest) :
    (Concrete.nodeAt parameter layer (level.val + 1) j left right : OracleComp HashSpec Digest) =
      Concrete.tweakableHash parameter (CacheView.nodeDomain layer level j)
        (Concrete.nodePayload left right) := by
  cases layer with
  | bottom =>
    have hnode : Concrete.merkleNodeOfNat j = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
    simpa [Concrete.nodeHash, CacheView.nodeDomain, hnode] using
      Concrete.nodeHash_eq (m := OracleComp HashSpec) parameter level ⟨j, hj⟩ left right
  | top =>
    have hnode : Concrete.topNodeOfNat j = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
    simpa [Concrete.topNodeHash, CacheView.nodeDomain, hnode] using
      Concrete.topNodeHash_eq (m := OracleComp HashSpec) parameter level ⟨j, hj⟩ left right

/-- From the cache, a climb of a layer's tree is the climb with the cache's node hash.


The climb starts at a node index of the layer and ends at most at the root. -/
theorem eval_climb (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (layer : EthLib.Cryptography.Xmss.Layer) :
    ∀ (siblings : List Digest) (level j : Nat) (current : Digest),
      level + siblings.length ≤ treeHeight → j < CacheView.layerLeaves layer →
      evalWithAnswerFn (answerFn cache)
          (Merkle.climb (Concrete.nodeAt parameter layer) level j current siblings :
            OracleComp HashSpec Digest) =
        (Merkle.climb (CacheView.nodeAt cache parameter layer) level j current siblings).run
  | [], _, _, _, _, _ => rfl
  | sibling :: rest, level, j, current, hlength, hj => by
    have hlevel : level < treeHeight := by simp at hlength; omega
    have hhalf : j / 2 < CacheView.layerLeaves layer := (Nat.div_le_self j 2).trans_lt hj
    simp only [Merkle.climb, evalWithAnswerFn_bind]
    rw [nodeAt_eq parameter layer ⟨level, hlevel⟩ (j / 2) hhalf, eval_tweakableHash,
      eval_climb cache parameter layer rest (level + 1) (j / 2) _ (by simp at hlength; omega)
        hhalf]
    simp [CacheView.nodeAt, hlevel, CacheView.tweakableHash, CacheView.nodeInput]

/-- From the cache, the climb of a whole path from a node index of a layer is the cache's climb. -/
theorem eval_climb_ofFn (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (layer : EthLib.Cryptography.Xmss.Layer) (j : Nat) (hj : j < CacheView.layerLeaves layer)
    (path : Fin treeHeight → Digest) (leaf : Digest) :
    evalWithAnswerFn (answerFn cache)
        (Merkle.climb (Concrete.nodeAt parameter layer) 0 j leaf (List.ofFn path) :
          OracleComp HashSpec Digest) =
      (Merkle.climb (CacheView.nodeAt cache parameter layer) 0 j leaf (List.ofFn path)).run :=
  eval_climb cache parameter layer _ 0 j leaf (by simp) hj

@[simp]
theorem eval_verifyTop (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (key : TopIndex) (root : Digest) (part : LayerSignature) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.verifyTop publicKey key root part : OracleComp HashSpec Bool) =
      Concrete.verifyTopFromCache cache publicKey key root part := by
  classical
  have hdigest : evalWithAnswerFn (answerFn cache)
      (Concrete.topEncodingHash publicKey.parameter key root part.randomness :
        OracleComp HashSpec Digest) =
      CacheView.topEncodingHash cache publicKey.parameter key (root, part.randomness) := by
    simp [Concrete.topEncodingHash_eq, CacheView.topEncodingHash, CacheView.topEncodingInput,
      CacheView.tweakableHash]
  have hleaf : ∀ endpoints, evalWithAnswerFn (answerFn cache)
      (Concrete.topLeafHash publicKey.parameter key endpoints : OracleComp HashSpec Digest) =
      CacheView.topLeafHash cache publicKey.parameter key endpoints := by
    intro endpoints
    simp [Concrete.topLeafHash_eq, CacheView.topLeafHash, CacheView.topLeafInput,
      CacheView.tweakableHash]
  rw [Concrete.verifyTop_eq]
  unfold Concrete.verifyTopFromCache
  simp only [evalWithAnswerFn_bind, hdigest]
  cases TargetSum.decodeDigest
    (CacheView.topEncodingHash cache publicKey.parameter key (root, part.randomness)) with
  | none => simp
  | some encoding =>
      simp only [evalWithAnswerFn_bind, eval_sequenceFin, eval_topChainWalk, hleaf,
        eval_climb_ofFn cache publicKey.parameter .top key.val key.isLt, evalWithAnswerFn_pure]
      rfl

@[simp]
theorem eval_verifyAfterLeaf (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (leafIndex : LeafIndex) (signature : Signature) (leaf : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool) =
      Concrete.verifyTopFromCache cache publicKey (topKeyOf leafIndex)
        (Merkle.climb (CacheView.nodeAt cache publicKey.parameter .bottom) 0 leafIndex.val leaf
          (List.ofFn signature.authPath)).run signature.top := by
  simp [Concrete.verifyAfterLeaf_eq,
    eval_climb_ofFn cache publicKey.parameter .bottom leafIndex.val leafIndex.isLt]

@[simp]
theorem eval_verify (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (leafIndex : LeafIndex) (message : Message) (signature : Signature) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool) =
      Concrete.verifyFromCache cache publicKey leafIndex message signature := by
  classical
  rw [Concrete.verify_eq]
  unfold Concrete.verifyFromCache Concrete.bottomRootFromCache
  simp only [evalWithAnswerFn_bind, eval_encodingHash]
  cases TargetSum.decodeDigest
    (CacheView.encodingHash cache publicKey.parameter leafIndex (message, signature.randomness)) <;> simp

theorem randomOracle_query_caches (input : HashInput)
    (initialCache : QueryCache HashSpec) (output : HashOutput)
    (finalCache : QueryCache HashSpec)
    (hmem : (output, finalCache) ∈
      support ((randomOracle (spec := HashSpec) input).run initialCache)) :
    finalCache input = some output := by
  cases hcache : initialCache input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache, support_map] at hmem
      obtain ⟨sampled, _, hresult⟩ := hmem
      cases hresult
      exact QueryCache.cacheQuery_self initialCache input output
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem
      exact hcache

theorem randomOracle_cache_le {α : Type} (computation : OracleComp HashSpec α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ randomOracle computation).run initialCache)) :
    initialCache ≤ result.2 := by
  exact OracleComp.simulateQ_run_preservesInv randomOracle
    (fun cache => initialCache ≤ cache)
    (by
      intro input cache hcache queryResult hquery
      exact hcache.trans
        (QueryImpl.withCaching_cache_le uniformSampleImpl input cache
          queryResult hquery))
    computation initialCache le_rfl result hmem

/-- Take a cache produced by a successful first run of a lazy random-oracle computation.

Rerunning the computation against any extension of that cache is deterministic.

The rerun leaves the larger cache unchanged. -/
theorem randomOracle_rerun_largerCache_eq_pure_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α)
    (initialCache resultCache largerCache : QueryCache HashSpec) (result : α)
    (hmem : (result, resultCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hle : resultCache ≤ largerCache) :
    (simulateQ randomOracle computation).run largerCache =
      pure (result, largerCache) := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache resultCache largerCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, _hcache⟩ := hmem
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le (next output) middleCache
          (result, resultCache) hrest
      have hlarger : largerCache input = some output := hle (hmiddleLe hmiddle)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryImpl.withCaching_run_some _ hlarger]
      simp only [pure_bind]
      exact ih output middleCache resultCache largerCache result hrest hle

/-- Replaying a lazy-oracle execution against its final cache reproduces its result. -/
theorem eval_answerFn_finalCache_eq_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α) (initialCache finalCache : QueryCache HashSpec)
    (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    evalWithAnswerFn (answerFn finalCache) computation = result := by
  induction computation using OracleComp.inductionOn generalizing initialCache finalCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.1.symm
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ finalCache :=
        randomOracle_cache_le (next output) middleCache (result, finalCache) hrest
      have hfinal : finalCache input = some output := hmiddleLe hmiddle
      simp only [evalWithAnswerFn_bind]
      have hqueryEval :
          evalWithAnswerFn (answerFn finalCache)
            (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) = output := by
        simpa [Concrete.oracleHash, answer, hfinal] using
          eval_oracleHash finalCache input
      rw [hqueryEval]
      exact ih output middleCache finalCache result hrest

/-- Replaying an execution against any extension of its final cache reproduces its result. -/
theorem eval_answerFn_largerCache_eq_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α)
    (initialCache resultCache largerCache : QueryCache HashSpec) (result : α)
    (hmem : (result, resultCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hle : resultCache ≤ largerCache) :
    evalWithAnswerFn (answerFn largerCache) computation = result := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache resultCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.1.symm
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le (next output) middleCache (result, resultCache) hrest
      have hlarger : largerCache input = some output := hle (hmiddleLe hmiddle)
      simp only [evalWithAnswerFn_bind]
      have hqueryEval :
          evalWithAnswerFn (answerFn largerCache)
            (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) = output := by
        simpa [Concrete.oracleHash, answer, hlarger] using
          eval_oracleHash largerCache input
      rw [hqueryEval]
      exact ih output middleCache resultCache result hrest hle

theorem verifyFromCache_eq_of_mem_support
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) (initialCache finalCache : QueryCache HashSpec)
    (result : Bool)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)).run
          initialCache)) :
    Concrete.verifyFromCache finalCache publicKey leafIndex message signature = result := by
  rw [← eval_verify]
  exact eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)
    initialCache finalCache result hmem

end XmssSecurity.Concrete.CacheReplay
