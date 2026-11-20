module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedConcreteExecution
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.QueryPresence

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

theorem capped_detailed_execution_verified_leaf_cached
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (hverified : execution.1.verified = true) :
    ∃ encoding output,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
          execution.1.forgery.leafIndex
          (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
          some encoding ∧
      execution.2
        (Concrete.CacheView.leafInput execution.1.secretKey.parameter
          execution.1.forgery.leafIndex
          (recoveredEndpoints
            (fun chain => Concrete.CacheView.chainStep execution.2
              execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
            encoding execution.1.forgery.signature.chainValue)) = some output := by
  have hparameter :=
    (capped_detailed_execution_key_components_consistent adversary execution hmem).1
  -- Decompose through lemmas for any scheme: the kernel would run the game to match two forms.
  obtain ⟨outcome, finalCache⟩ := execution
  obtain ⟨publicKey, secretKey, keyCache, -, hrest⟩ :=
    exists_of_mem_support_detailedGameWithCache _ _ hmem
  obtain ⟨forgery, signingLog, adversaryCache, verified, -, hverify, hout⟩ :=
    exists_of_mem_support_detailedGameAfterKeygen _ _ _ _ _ hrest
  subst outcome
  simp only at hparameter hverified ⊢
  subst verified
  have hroute :
      simulateQ romImpl
          (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message forgery.signature) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, romImpl]
    change simulateQ (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  rw [← hparameter]
  exact Concrete.CacheReplay.verify_true_leaf_query_cached_in_largerCache publicKey
    forgery.leafIndex forgery.message forgery.signature adversaryCache finalCache finalCache
    hverify le_rfl

theorem capped_detailed_execution_verified_leaf_cached_as
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hgame : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding) :
    ∃ output, execution.2
      (Concrete.CacheView.leafInput execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
          encoding execution.1.forgery.signature.chainValue)) = some output := by
  obtain ⟨actualEncoding, output, hactualDecode, hcached⟩ :=
    capped_detailed_execution_verified_leaf_cached adversary execution hgame hverified
  have hencoding : actualEncoding = encoding := by
    rw [hdecode] at hactualDecode
    exact Option.some.inj hactualDecode.symm
  subst actualEncoding
  exact ⟨output, hcached⟩

end XmssSecurity
