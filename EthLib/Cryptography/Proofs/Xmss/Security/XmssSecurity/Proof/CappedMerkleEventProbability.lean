module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.ExpectedAdaptiveFreshTarget
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CappedLeafEventProbability
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.MerkleVerificationQueryPresence
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.TopKeygenCache

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedMerkle


theorem detailed_execution_verified_merkle_query_cached_as
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some encoding)
    (level : MerkleLevel) :
    ∃ output, execution.2
      (Concrete.CacheView.nodeInput execution.1.secretKey.parameter .bottom level
        (execution.1.forgery.leafIndex.val / 2 ^ (level.val + 1))
        (Merkle.pairAt
          (Concrete.CacheView.nodeAt execution.2 execution.1.secretKey.parameter .bottom)
          execution.1.forgery.leafIndex.val execution.1.forgery.signature.authPath
          (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep execution.2
                execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
              encoding execution.1.forgery.signature.chainValue)) level).1
        (Merkle.pairAt
          (Concrete.CacheView.nodeAt execution.2 execution.1.secretKey.parameter .bottom)
          execution.1.forgery.leafIndex.val execution.1.forgery.signature.authPath
          (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep execution.2
                execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
              encoding execution.1.forgery.signature.chainValue)) level).2) = some output := by
  have hparameter :=
    (capped_detailed_execution_key_components_consistent adversary execution hmem).1
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  simp only at hparameter hverified hdecode ⊢
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
  have hdecodePublic : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash finalCache publicKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = some encoding := by
    rw [hparameter]
    exact hdecode
  rw [← hparameter]
  exact Concrete.CacheReplay.verify_true_merkle_query_cached_as_in_largerCache publicKey
    forgery.leafIndex forgery.message forgery.signature encoding level adversaryCache finalCache
    finalCache hverify hdecodePublic le_rfl

/-- The node on the path of a leaf one level above `level` is a node of the bottom forest. -/
theorem pathNode_succ_lt (leafIndex : LeafIndex) (level : MerkleLevel) :
    (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)).val <
      2 ^ (2 * treeHeight - (level.val + 1)) := by
  have hsum : (2 * treeHeight - (level.val + 1)) + (level.val + 1) = 2 * treeHeight := by
    have := level.isLt
    omega
  have hquotient :
      leafIndex.val / 2 ^ (level.val + 1) < 2 ^ (2 * treeHeight - (level.val + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (level.val + 1))).2
    calc
      leafIndex.val < 2 ^ (2 * treeHeight) := leafIndex.isLt
      _ = 2 ^ (2 * treeHeight - (level.val + 1)) * 2 ^ (level.val + 1) := by
        rw [← Nat.pow_add, hsum]
  simp only [Concrete.CacheReplay.pathNode, Concrete.merkleNodeOfNat]
  exact (Nat.mod_le _ _).trans_lt hquotient

noncomputable def keygenMerkleTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ address : MerkleLevel × MerkleNode, ∃ left right,
      input = Concrete.CacheView.merkleInput secretKey.parameter address.1 address.2
        left right then
    let address := h.choose
    Concrete.CacheView.merkleInput secretKey.parameter address.1 address.2
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
        address.1.val (Concrete.childNode address.2 false))
      (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
        address.1.val (Concrete.childNode address.2 true))
  else input

@[simp]
theorem keygenMerkleTargetInput_merkleInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
      Concrete.CacheView.merkleInput secretKey.parameter level node
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
          level.val (Concrete.childNode node true)) := by
  unfold keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨chosenLeft, chosenRight, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      (hinput.trans rfl)
    simp only [HashDomain.merkle.injEq] at hdomain
    rcases hdomain with ⟨hlevel, hnode⟩
    dsimp only
    rw [← hlevel, ← hnode]
  · rename_i h
    exfalso
    exact h ⟨(level, node), left, right, rfl⟩

attribute [irreducible] keygenMerkleTargetInput

/-- A cached node on a forged path that collides with the honest node at its address. -/
theorem merkleCollision_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (secretKey : SecretKey) (hsecret : secretKey = keyResult.1.2)
    (leafIndex : LeafIndex) (level : MerkleLevel) (forged honest : Digest × Digest)
    (forgedOutput : HashOutput)
    (hforgedCached : execution.2
      (Concrete.CacheView.nodeInput secretKey.parameter .bottom level
        (leafIndex.val / 2 ^ (level.val + 1)) forged.1 forged.2) = some forgedOutput)
    (hne : forged ≠ honest)
    (heq : (Concrete.CacheView.nodeAt execution.2 secretKey.parameter .bottom (level.val + 1)
        (leafIndex.val / 2 ^ (level.val + 1)) forged.1 forged.2).run =
      (Concrete.CacheView.nodeAt execution.2 secretKey.parameter .bottom (level.val + 1)
        (leafIndex.val / 2 ^ (level.val + 1)) honest.1 honest.2).run)
    (hhonest : honest =
      (Concrete.CacheReplay.treeNode execution.2 secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)) false),
        Concrete.CacheReplay.treeNode execution.2 secretKey.parameter secretKey.chainStart
          level.val
          (Concrete.childNode (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)) true))) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  subst secretKey
  have hafterCacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  let node := Concrete.CacheReplay.pathNode leafIndex (level.val + 1)
  have hnode := pathNode_succ_lt leafIndex level
  have hforgedInitial :=
    Concrete.precomputedKeygen_cache_forestMerkleInput_eq_none_of_ne_in_largerCache keyResult
      hkeygen' execution.2 hafterCacheLe level node hnode forged.1 forged.2
      (by rw [← hhonest]; exact hne)
  -- Key generation cached the honest children, which no later query changes.
  obtain ⟨honestOutput, hhonestCached⟩ :=
    Concrete.precomputedKeygen_cache_has_forestMerkleInput_in_largerCache keyResult hkeygen'
      keyResult.2 le_rfl level node hnode
  obtain ⟨hleft, hright⟩ := Prod.mk.inj
    (Concrete.precomputedKeygen_forestMerkleChildren_eq_of_cache_le keyResult hkeygen'
      execution.2 hafterCacheLe level node hnode)
  rw [Concrete.CacheView.nodeInput_bottom] at hforgedCached
  -- The honest output is stated at its plain type, so its input is not compared.
  refine ⟨Concrete.CacheView.merkleInput keyResult.1.2.parameter level node forged.1 forged.2,
    forgedOutput, show HashOutput from honestOutput, hforgedCached, hforgedInitial, ?_, ?_⟩
  · rw [keygenMerkleTargetInput_merkleInput]
    exact hhonestCached
  · rw [keygenMerkleTargetInput_merkleInput, hleft, hright]
    rw [Concrete.CacheView.nodeAt_bottom, Concrete.CacheView.nodeAt_bottom, hhonest] at heq
    unfold Concrete.CacheView.merkleHash at heq
    exact heq


/-- A path collision of a forged bottom path with an honest one, at a level the forgery cached. -/
theorem merkle_path_collision_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (leafIndex : LeafIndex) (hleafIndex : leafIndex = execution.1.forgery.leafIndex)
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (honestPath : Fin treeHeight → Digest) (honestLeaf : Digest) (level : MerkleLevel)
    (hevent : Merkle.CollidesAt
      (Concrete.CacheView.nodeAt execution.2 execution.1.secretKey.parameter .bottom)
      leafIndex.val execution.1.forgery.signature.authPath honestPath
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter leafIndex chain)
          forgedEncoding execution.1.forgery.signature.chainValue))
      honestLeaf (level.val + 1))
    (hhonest : Merkle.pairAt
        (Concrete.CacheView.nodeAt execution.2 execution.1.secretKey.parameter .bottom)
        leafIndex.val honestPath honestLeaf level =
      (Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
          execution.1.secretKey.chainStart level.val
          (Concrete.childNode (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)) false),
        Concrete.CacheReplay.treeNode execution.2 execution.1.secretKey.parameter
          execution.1.secretKey.chainStart level.val
          (Concrete.childNode (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)) true))) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  subst leafIndex
  obtain ⟨hne, heq⟩ := Merkle.CollidesAt.pairs _ hevent
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary
    keyResult hkeygen execution hafter
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    detailed_execution_verified_merkle_query_cached_as adversary execution hgame
      forgedEncoding hverified hforgedDecode level
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1
    keyResult.1.2 keyResult.2 execution hafter
  exact merkleCollision_afterKeygen_orientation adversary keyResult hkeygen execution
    hafter execution.1.secretKey hkeys.2 execution.1.forgery.leafIndex level _ _
    forgedOutput hforgedCached hne heq hhonest

theorem same_merkle_witness_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (request : SignRequest) (signature : Signature)
    (signedEncoding forgedEncoding : Encoding)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.leafIndex (request.message, signature.randomness)) = some signedEncoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature)
    (hleafIndex : request.leafIndex = execution.1.forgery.leafIndex)
    (level : MerkleLevel)
    (hevent : Concrete.SameLeafIndexBadEventOccurs execution.2
      execution.1.secretKey.parameter request.leafIndex request.message
      execution.1.forgery.message signedEncoding forgedEncoding signature
      execution.1.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen execution hafter
  have hsignature := CappedLeaf.detailed_execution_returned_signature_eq adversary execution hgame
    request signature signedEncoding hsignedDecode hreturned
  have hdecodeLeafIndex := congrArg (fun leafIndex => TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter leafIndex
      (execution.1.forgery.message, execution.1.forgery.signature.randomness))) hleafIndex
  have hforgedDecode' : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding := hdecodeLeafIndex.symm.trans hforgedDecode
  change Merkle.CollidesAt
    (Concrete.CacheView.nodeAt execution.2 execution.1.secretKey.parameter .bottom)
    request.leafIndex.val execution.1.forgery.signature.authPath signature.authPath
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.leafIndex chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.leafIndex chain)
        signedEncoding signature.chainValue)) (level.val + 1) at hevent
  refine merkle_path_collision_afterKeygen_orientation adversary keyResult hkeygen
    execution hafter hverified request.leafIndex hleafIndex forgedEncoding hforgedDecode'
      signature.authPath
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
        request.leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter request.leafIndex chain)
          signedEncoding signature.chainValue)) level hevent ?_
  rw [hsignature, Concrete.CacheReplay.leafHash_recovered_signWithEncoding]
  exact Concrete.CacheReplay.pairAt_authenticationPath execution.2 execution.1.secretKey
    request.leafIndex signature.randomness signedEncoding level

theorem fresh_merkle_witness_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (level : MerkleLevel)
    (hevent : Concrete.FreshLeafIndexBadEventOccurs execution.2
      execution.1.secretKey.parameter execution.1.forgery.leafIndex forgedEncoding
      execution.1.forgery.signature
      (execution.1.secretKey.chainStart execution.1.forgery.leafIndex)
      (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
        execution.1.forgery.leafIndex execution.1.forgery.signature.randomness
        forgedEncoding).authPath
      (TargetSum.decodeDigest_eq_some_iff.mp hforgedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  let honestSignature := Concrete.CacheReplay.signWithEncoding execution.2
    execution.1.secretKey execution.1.forgery.leafIndex
    execution.1.forgery.signature.randomness forgedEncoding
  change Merkle.CollidesAt
    (Concrete.CacheView.nodeAt execution.2 execution.1.secretKey.parameter .bottom)
    execution.1.forgery.leafIndex.val execution.1.forgery.signature.authPath
    honestSignature.authPath
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter execution.1.forgery.leafIndex chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.leafIndex
      (fun chain => Wots.publicChain
        (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
          execution.1.forgery.leafIndex chain)
        (execution.1.secretKey.chainStart execution.1.forgery.leafIndex chain)))
    (level.val + 1) at hevent
  refine merkle_path_collision_afterKeygen_orientation adversary keyResult hkeygen
    execution hafter hverified execution.1.forgery.leafIndex rfl forgedEncoding
      hforgedDecode honestSignature.authPath
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.leafIndex
        (fun chain => Wots.publicChain
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            execution.1.forgery.leafIndex chain)
          (execution.1.secretKey.chainStart execution.1.forgery.leafIndex chain))) level
      hevent ?_
  exact Concrete.CacheReplay.pairAt_authenticationPath execution.2 execution.1.secretKey
    execution.1.forgery.leafIndex execution.1.forgery.signature.randomness forgedEncoding level

theorem merkle_event_afterKeygen_orientation
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (level : MerkleLevel)
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hmerkle⟩ := hsame
    exact same_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 request signature signedEncoding forgedEncoding hsignedDecode
      hforgedDecode hreturned hleafIndex level hmerkle
  · obtain ⟨forgedEncoding, hforgedValid, _hunsigned, hforgedDecode, hmerkle⟩ := hfresh
    exact fresh_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 forgedEncoding hforgedDecode level hmerkle

end XmssSecurity.CappedMerkle
