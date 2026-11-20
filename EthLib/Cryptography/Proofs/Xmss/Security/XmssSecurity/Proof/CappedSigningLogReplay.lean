module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedConcreteExecution
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.PrecomputedBoundedSign
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.SigningLogConsistency
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.WinningEventReduction

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped BigOperators

namespace XmssSecurity

noncomputable def cappedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  romImpl.writerTMapBase
    (forwardOracles + signingOracle Concrete.scheme secretKey)

theorem cappedMappedAdversary_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (cappedMappedAdversaryImpl publicKey secretKey) computation).run).run
        initialCache)) :
    initialCache ≤ result.2 := by
  apply xmssRom_cache_le
    ((simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey)
      computation).run) initialCache result
  rw [QueryImpl.simulateQ_writerTMapBase_run]
  exact hmem

/-- An output of the adversary with the scheme's oracles is one with the mapped oracles.

It holds for any computation, so the kernel checks it without running one. -/
private theorem mem_support_cappedMappedAdversaryImpl_run (publicKey : PublicKey)
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    {result : (α × QueryLog SigningSpec) × QueryCache HashSpec}
    (hmem : result ∈ support ((simulateQ romImpl
      (simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey)
        computation).run).run initialCache)) :
    result ∈ support
      (((simulateQ (cappedMappedAdversaryImpl publicKey secretKey) computation).run).run
        initialCache) := by
  rw [cappedMappedAdversaryImpl, ← QueryImpl.simulateQ_writerTMapBase_run]
  exact hmem

/-- A signing query, answered by the mapped oracles, logs one entry and runs the signer.

It holds for any scheme, any implementation equal to the mapped oracles and any query.

So the kernel checks it without running the signer. -/
private theorem mem_support_mappedImpl_signingQuery (scheme : Scheme SecretKey)
    (secretKey : SecretKey)
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)))
    (request : SignRequest) (initialCache : QueryCache HashSpec)
    (query : OracleComp (OracleWorld + SigningSpec)
      ((OracleWorld + SigningSpec).Range (.inr request)))
    {output : (OracleWorld + SigningSpec).Range (.inr request)} {queryLog : QueryLog SigningSpec}
    {middleCache : QueryCache HashSpec}
    (hquery : ((output, queryLog), middleCache) ∈ support
      (((simulateQ impl query).run).run initialCache))
    (himpl : impl = romImpl.writerTMapBase (forwardOracles + signingOracle scheme secretKey))
    (hq : query = liftM (OracleSpec.query (Sum.inr request))) :
    queryLog = [⟨request, output⟩] ∧
      @Prod.mk (Option Signature) (QueryCache HashSpec) output middleCache ∈ support
        ((simulateQ romImpl (scheme.sign secretKey request.leafIndex request.message)).run
          initialCache) := by
  subst impl query
  simp only [simulateQ_spec_query, QueryImpl.writerTMapBase, QueryImpl.add_apply_inr,
    signingOracle] at hquery
  rw [WriterT.run_mk] at hquery
  erw [QueryImpl.run_withLogging_apply] at hquery
  erw [simulateQ_bind] at hquery
  rw [StateT.run_bind, mem_support_bind_iff] at hquery
  obtain ⟨⟨signOutput, signCache⟩, hsign, hpure⟩ := hquery
  cases hpure
  exact ⟨rfl, hsign⟩

theorem cappedMappedAdversary_signingLog_consistent
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (cappedMappedAdversaryImpl publicKey secretKey) computation).run).run
        initialCache))
    (keygenCache largerCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keygenCache secretKey)
    (hkeygenLe : keygenCache ≤ largerCache) (hle : result.2 ≤ largerCache) :
    SigningLogConsistent largerCache secretKey result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      intro request signature hreturned
      obtain ⟨entry, hentry, _⟩ := hreturned
      simp at hentry
  | query_bind input next ih =>
      rw [simulateQ_bind] at hmem
      rw [WriterT.run_bind', StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, queryLog⟩, middleCache⟩, hquery, hrestMapped⟩ := hmem
      rw [StateT.run_map, support_map] at hrestMapped
      obtain ⟨⟨⟨value, restLog⟩, finalCache⟩, hrest, heq⟩ := hrestMapped
      cases heq
      intro request signature hreturned
      obtain ⟨entry, hentry, hrequest, hsignature⟩ := hreturned
      change entry ∈ queryLog ++ restLog at hentry
      change finalCache ≤ largerCache at hle
      rw [List.mem_append] at hentry
      rcases hentry with hcurrent | hlater
      · cases input with
        | inl worldInput =>
            simp only [simulateQ_spec_query, cappedMappedAdversaryImpl,
              QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, forwardOracles,
              WriterT.run_mk] at hquery
            erw [WriterT.run_liftM] at hquery
            rw [simulateQ_map, StateT.run_map, support_map] at hquery
            obtain ⟨⟨worldOutput, worldCache⟩, _hworld, heq⟩ := hquery
            cases heq
            simp at hcurrent
        | inr signingRequest =>
            -- Step by a lemma for any scheme, or the kernel runs the signer to match forms.
            obtain ⟨rfl, hsign⟩ := mem_support_mappedImpl_signingQuery Concrete.scheme secretKey
              (cappedMappedAdversaryImpl publicKey secretKey) signingRequest initialCache _ hquery
              rfl rfl
            simp only [List.mem_singleton] at hcurrent
            subst hcurrent
            have hmiddleFinal : middleCache ≤ finalCache :=
              cappedMappedAdversary_cache_le publicKey secretKey (next output)
                middleCache ((value, restLog), finalCache) hrest
            simp only at hrequest hsignature
            subst hrequest hsignature
            rw [Concrete.scheme_sign] at hsign
            apply Concrete.precomputedCappedSign_success_replay secretKey signingRequest
              keygenCache initialCache middleCache largerCache signature hconsistent hkeygenLe
            · exact hsign
            · exact hmiddleFinal.trans hle
      · apply ih output middleCache ((value, restLog), finalCache) hrest hle
        exact ⟨entry, hlater, hrequest, hsignature⟩

theorem capped_detailed_execution_signingLog_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    SigningLogConsistent execution.2 execution.1.secretKey execution.1.signingLog := by
  -- Decompose through lemmas for any scheme: the kernel would run the game to match two forms.
  obtain ⟨outcome, finalCache⟩ := execution
  obtain ⟨publicKey, secretKey, keyCache, hkeygen, hrest⟩ :=
    exists_of_mem_support_detailedGameWithCache _ _ hmem
  obtain ⟨forgery, signingLog, adversaryCache, verified, hadversary, hverify, hout⟩ :=
    exists_of_mem_support_detailedGameAfterKeygen _ _ _ _ _ hrest
  subst outcome
  simp only
  have hadversary' :=
    mem_support_cappedMappedAdversaryImpl_run publicKey secretKey _ keyCache hadversary
  have hcacheLe : adversaryCache ≤ finalCache :=
    xmssRom_cache_le _ adversaryCache (verified, finalCache) hverify
  have hkeygen' := hkeygen
  rw [Concrete.scheme_keygen] at hkeygen'
  have hconsistent :=
    Concrete.precomputedKeygen_support_consistent
      ((publicKey, secretKey), keyCache) hkeygen'
  have hkeygenLeAdversary : keyCache ≤ adversaryCache :=
    cappedMappedAdversary_cache_le publicKey secretKey (adversary.main publicKey)
      keyCache ((forgery, signingLog), adversaryCache) hadversary'
  exact cappedMappedAdversary_signingLog_consistent publicKey secretKey
    (adversary.main publicKey) keyCache ((forgery, signingLog), adversaryCache)
    hadversary' keyCache finalCache hconsistent
      (hkeygenLeAdversary.trans hcacheLe) hcacheLe

theorem capped_detailed_execution_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    ConcreteOutcomeConsistent execution.2 execution.1 :=
  capped_detailed_execution_consistent_of_signing adversary execution hmem
    (capped_detailed_execution_signingLog_consistent adversary execution hmem)

end XmssSecurity
