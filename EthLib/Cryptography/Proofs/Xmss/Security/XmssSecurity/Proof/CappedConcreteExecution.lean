module

public import EthLib.Cryptography.Proofs.SupportBind
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.OutcomeClassification
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.PrecomputedKeygenCache
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Translate

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

/-- An output of a logged computation, with its log dropped, is an output of the computation.

It holds for any computation, so the kernel checks it without running one. -/
private theorem mem_support_run_of_mem_support_withQueryLog {α : Type}
    (computation : OracleComp HashSpec α) (initialCache : QueryCache HashSpec)
    {result : α × QueryLog HashSpec} {cache : QueryCache HashSpec}
    (h : (result, cache) ∈ support
      ((simulateQ randomOracle computation.withQueryLog).run initialCache)) :
    (result.1, cache) ∈ support ((simulateQ randomOracle computation).run initialCache) := by
  rw [← withQueryLog_cache_projection, support_map]
  exact ⟨(result, cache), h, rfl⟩

/-- An execution of the detailed game runs key generation, then the rest of the game.

The rest starts from the cache that key generation leaves.

It holds for any scheme, so the kernel checks it without running one. -/
theorem exists_of_mem_support_detailedGameWithCache (scheme : Scheme SecretKey)
    (adversary : Adversary) {execution : GameOutcome × QueryCache HashSpec}
    (hmem : execution ∈ support (detailedGameWithCache scheme adversary)) :
    ∃ publicKey secretKey keyCache,
      ((publicKey, secretKey), keyCache) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) ∧
      execution ∈ support ((simulateQ romImpl
        (detailedGameAfterKeygen scheme adversary publicKey secretKey)).run keyCache) := by
  unfold detailedGameWithCache detailedGameCore at hmem
  obtain ⟨⟨publicKey, secretKey⟩, keyCache, hkeygen, hrest⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ hmem
  exact ⟨publicKey, secretKey, keyCache, hkeygen, hrest _ rfl⟩

/-- An execution of the game after key generation runs the adversary, then the verifier.

Its outcome records the keys, the forgery, the signing log and the verdict.

It holds for any scheme, so the kernel checks it without running one. -/
theorem exists_of_mem_support_detailedGameAfterKeygen (scheme : Scheme SecretKey)
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) {outcome : GameOutcome} {finalCache : QueryCache HashSpec}
    (hmem : (outcome, finalCache) ∈ support ((simulateQ romImpl
      (detailedGameAfterKeygen scheme adversary publicKey secretKey)).run cache)) :
    ∃ forgery signingLog adversaryCache verified,
      ((forgery, signingLog), adversaryCache) ∈ support ((simulateQ romImpl
        (simulateQ (forwardOracles + signingOracle scheme secretKey)
          (adversary.main publicKey)).run).run cache) ∧
      (verified, finalCache) ∈ support ((simulateQ romImpl
        (scheme.verify publicKey forgery.leafIndex forgery.message forgery.signature)).run
          adversaryCache) ∧
      outcome = ⟨publicKey, secretKey, forgery, signingLog, verified⟩ := by
  unfold detailedGameAfterKeygen at hmem
  obtain ⟨⟨forgery, signingLog⟩, adversaryCache, hadversary, hrest⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ hmem
  obtain ⟨verified, verifyCache, hverify, hout⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ (hrest _ rfl)
  have hout := hout _ rfl
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hout
  obtain ⟨rfl, rfl⟩ := hout
  exact ⟨forgery, signingLog, adversaryCache, verified, hadversary, hverify, rfl⟩

theorem capped_detailed_execution_verification_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.verified = Concrete.verifyFromCache execution.2 execution.1.publicKey
      execution.1.forgery.leafIndex execution.1.forgery.message execution.1.forgery.signature := by
  -- Decompose through lemmas for any scheme: the kernel would run the game to match two forms.
  obtain ⟨outcome, finalCache⟩ := execution
  obtain ⟨publicKey, secretKey, keyCache, -, hrest⟩ :=
    exists_of_mem_support_detailedGameWithCache _ _ hmem
  obtain ⟨forgery, signingLog, adversaryCache, verified, -, hverify, hout⟩ :=
    exists_of_mem_support_detailedGameAfterKeygen _ _ _ _ _ hrest
  subst outcome
  simp only
  have hroute :
      simulateQ romImpl
          (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
            forgery.signature) =
        simulateQ randomOracle
          (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  exact (Concrete.CacheReplay.verifyFromCache_eq_of_mem_support publicKey forgery.leafIndex
    forgery.message forgery.signature adversaryCache finalCache verified hverify).symm

theorem Concrete.CacheReplay.topSignFrom_decode_of_eval (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (key : TopIndex) (root : Digest) (base : Randomness)
    (attempts trial : Nat) (randomness : Randomness) (encoding : Encoding)
    (heval : evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.topSignFrom parameter key root base attempts trial :
        OracleComp HashSpec (Option (Randomness × Encoding))) = some (randomness, encoding)) :
    TargetSum.decodeDigest
      (Concrete.CacheView.topEncodingHash cache parameter key (root, randomness)) = some encoding := by
  have hdigest : ∀ randomness, evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.topEncodingHash parameter key root randomness : OracleComp HashSpec Digest) =
      Concrete.CacheView.topEncodingHash cache parameter key (root, randomness) := by
    intro randomness
    simp [Concrete.topEncodingHash_eq, Concrete.CacheView.topEncodingHash,
      Concrete.CacheView.topEncodingInput, Concrete.CacheView.tweakableHash]
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom] at heval
  | succ attempts ih =>
      simp only [Concrete.topSignFrom, evalWithAnswerFn_bind, hdigest] at heval
      split at heval
      · rename_i found hdecode
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at heval
        obtain ⟨rfl, rfl⟩ := heval
        exact hdecode
      · exact ih (trial + 1) heval

theorem Concrete.CacheReplay.eval_honestKeygen (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness) :
    evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
        OracleComp HashSpec _) =
      (Concrete.CacheReplay.topTreeNode cache parameter topSecret treeHeight Concrete.rootNode,
        fun key => evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
          (Concrete.topSignFrom parameter key
            (Concrete.CacheReplay.treeNode cache parameter secret treeHeight
              (Concrete.bottomRootNode key)) (topBase key) signingAttemptLimit 0 :
            OracleComp HashSpec (Option (Randomness × Encoding)))) := by
  simp [Concrete.honestKeygen, evalWithAnswerFn_bind]

set_option linter.constructorNameAsVariable false in
/-- Replay key generation's honest computation in the final cache.

It gives the root and the top signatures. -/
theorem capped_detailed_execution_keygen_eval
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    ∃ topBase : TopIndex → Randomness,
      execution.1.publicKey.parameter = execution.1.secretKey.parameter ∧
      evalWithAnswerFn (Concrete.CacheReplay.answerFn execution.2)
        (Concrete.honestKeygen execution.1.secretKey.parameter execution.1.secretKey.chainStart
          execution.1.secretKey.topChainStart (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _) =
        (execution.1.publicKey.root, execution.1.secretKey.topSigned) := by
  -- Decompose by lemmas for any computation, or the kernel runs key generation to match forms.
  obtain ⟨outcome, finalCache⟩ := execution
  obtain ⟨publicKey, secretKey, keyCache, hkeygen, hrest⟩ :=
    exists_of_mem_support_detailedGameWithCache _ _ hmem
  have hkeyCacheLe : keyCache ≤ finalCache :=
    xmssRom_cache_le _ keyCache (outcome, finalCache) hrest
  rw [Concrete.scheme_keygen, Concrete.precomputedKeygen.eq_1] at hkeygen
  obtain ⟨parameter, parameterCache, -, hkeygen⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ hkeygen
  obtain ⟨secret, secretCache, -, hkeygen⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ (hkeygen _ rfl)
  obtain ⟨topSecret, topSecretCache, -, hkeygen⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ (hkeygen _ rfl)
  obtain ⟨topBase, topBaseCache, -, hkeygen⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ (hkeygen _ rfl)
  obtain ⟨treeResult, rootCache, hroot, hout⟩ :=
    exists_eq_of_mem_support_simulateQ_bind _ _ _ _ (hkeygen _ rfl)
  have hout := hout _ rfl
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  cases hout
  obtain ⟨forgery, signingLog, adversaryCache, verified, -, -, hout⟩ :=
    exists_of_mem_support_detailedGameAfterKeygen _ _ _ _ _ hrest
  subst outcome
  let honest : OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))) :=
    Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key))
  have hroute :
      simulateQ romImpl (liftM honest.withQueryLog) = simulateQ randomOracle honest.withQueryLog := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) honest.withQueryLog
  rw [hroute] at hroot
  have hroot' := mem_support_run_of_mem_support_withQueryLog honest topBaseCache hroot
  refine ⟨topBase, rfl, ?_⟩
  exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support honest topBaseCache
    keyCache finalCache treeResult.1 hroot' hkeyCacheLe

theorem capped_detailed_execution_key_components_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.publicKey.parameter = execution.1.secretKey.parameter ∧
      execution.1.publicKey.root = Concrete.CacheReplay.topTreeNode execution.2
        execution.1.secretKey.parameter execution.1.secretKey.topChainStart treeHeight
        Concrete.rootNode := by
  obtain ⟨topBase, hparameter, heval⟩ :=
    capped_detailed_execution_keygen_eval adversary execution hmem
  rw [Concrete.CacheReplay.eval_honestKeygen] at heval
  exact ⟨hparameter, (congrArg Prod.fst heval).symm⟩

/-- The top signatures key generation computed decode, in the final cache, on their bottom roots. -/
theorem capped_detailed_execution_topSigned_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    ∀ key randomness encoding,
      execution.1.secretKey.topSigned key = some (randomness, encoding) →
        TargetSum.decodeDigest
          (Concrete.CacheView.topEncodingHash execution.2 execution.1.secretKey.parameter key
            (Concrete.bottomRoot execution.2 execution.1.secretKey key, randomness)) = some encoding := by
  intro key randomness encoding hsigned
  obtain ⟨topBase, -, heval⟩ :=
    capped_detailed_execution_keygen_eval adversary execution hmem
  rw [Concrete.CacheReplay.eval_honestKeygen] at heval
  have hkey := congrFun (congrArg Prod.snd heval) key
  simp only at hkey
  rw [hsigned] at hkey
  exact Concrete.CacheReplay.topSignFrom_decode_of_eval execution.2 _ key _ (topBase key)
    signingAttemptLimit 0 randomness encoding hkey

theorem capped_detailed_execution_key_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.publicKey =
      Concrete.CacheReplay.publicKeyFromCache execution.2 execution.1.secretKey := by
  obtain ⟨hparameter, hroot⟩ :=
    capped_detailed_execution_key_components_consistent adversary execution hmem
  cases hpublicKey : execution.1.publicKey with
  | mk root parameter =>
      simp only [hpublicKey] at hparameter hroot ⊢
      subst parameter
      exact Concrete.CacheReplay.publicKey_eq_publicKeyFromCache execution.2
        execution.1.secretKey root hroot

theorem capped_detailed_execution_consistent_of_signing
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary))
    (hsigning : ∀ request signature,
      SigningTranscript.Returned execution.1.signingLog request signature →
      ∃ encoding,
        TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
            request.leafIndex (request.message, signature.randomness)) = some encoding ∧
        signature = Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          request.leafIndex signature.randomness encoding) :
    ConcreteOutcomeConsistent execution.2 execution.1 :=
  ⟨capped_detailed_execution_key_consistent adversary execution hmem,
    capped_detailed_execution_verification_consistent adversary execution hmem, hsigning,
    capped_detailed_execution_topSigned_consistent adversary execution hmem⟩

end XmssSecurity
