module

public import EthLib.Consensus.RemoteSigningApi.SigningRoot
public import EthLib.Consensus.Proofs.HonestValidator
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.BuilderRequests
public import EthLib.Consensus.HonestBuilder
public import EthLib.Consensus.Proofs.Signing
public import EthLib.Base.Proofs.Except

/-!
# Proofs: the root of each request is the root that its duty signs

The domain that the fork info of a request gives is the domain of a state with that fork info.

So under the fork info of a state, a request has the root that its duty signs in that state.

The header of a block has the root of the block.

So a signer that sees only the header signs the root of the proposer's block.

A registration and a deposit get the root that their checks verify.

A voluntary exit gets the root that its check verifies, under a hypothesis on its fork version.

A bid, a payload attestation and a Builder API authentication get the roots of their duties.

An envelope does too when the epoch of its payload's slot takes the fork version of the state.

Proposer preferences do when the fork info gives the configured version of the proposal epoch.

The domain of each request starts with the domain type of its kind.

Only three pairs of kinds share a domain type.
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {state : BeaconState preset fork}
  {key : Signatures.SecretKey} {root : Root} {signing : Signing}

/-- The domain of a state at an epoch is the domain that the state's fork info gives. -/
theorem getDomain_eq_forkInfoDomain (config : Config) (state : BeaconState preset fork)
    (domainType : DomainType) (epoch : Epoch) :
    getDomain config state domainType (some epoch) =
      (forkInfoDomain config (.ofState state) domainType epoch).mapError .ssz :=
  rfl

/-- A signature at an epoch signs the root that the state's fork info gives, at that epoch. -/
theorem signAtEpoch_eq_of_forkInfoDomain {α : Type} [SszType α] {domainType : DomainType}
    {epoch : Epoch} {object : α} {info : ForkInfo} (forked : info = .ofState state)
    (rooted : (do computeSigningRoot object (← forkInfoDomain config info domainType epoch)) =
      .ok root) :
    signAtEpoch config state domainType epoch object key =
      (Signatures.sign key (packBytes root)).mapError .bls := by
  subst forked
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  have got : getDomain config state domainType (some epoch) = .ok domain := by
    rw [getDomain_eq_forkInfoDomain, domained]
    rfl
  -- Rewrite each step that succeeds, so the kernel never evaluates the signing call.
  unfold signAtEpoch
  rw [got, mapError_ok_bind, rooted, mapError_ok_bind]

/-! ## The duties of a validator -/

/-- The root of an aggregator selection is the root of the selection proof of its slot. -/
theorem getSlotSignature_eq_of_requestSigningRoot {body : AggregationSlot}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.aggregationSlot signing body) = .ok root) :
    getSlotSignature config state body.slot key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of a Phase 0 aggregate is the root of its aggregate and proof signature. -/
theorem getAggregateAndProofSignature_eq_of_requestSigningRoot
    {state : BeaconState preset .phase0} {body : AggregateAndProof preset .phase0}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.aggregateAndProof signing body) = .ok root) :
    getAggregateAndProofSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of a versioned aggregate is the root of its signature at the fork of its version. -/
theorem getAggregateAndProofSignature_eq_of_requestSigningRoot_v2 {version : ConsensusVersion}
    {state : BeaconState preset version.fork} {body : AggregateAndProof preset version.fork}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.aggregateAndProofV2 signing version body) = .ok root) :
    getAggregateAndProofSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of attestation data is the root of its attestation signature. -/
theorem getAttestationSignature_eq_of_requestSigningRoot {body : AttestationData}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config (.attestation signing body) = .ok root) :
    getAttestationSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of a Phase 0 block is the root of its block signature. -/
theorem getBlockSignature_eq_of_requestSigningRoot {state : BeaconState preset .phase0}
    {body : BeaconBlock preset .phase0} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config (.block signing body) = .ok root) :
    getBlockSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of a versioned Phase 0 block is the root of its block signature. -/
theorem getBlockSignature_eq_of_requestSigningRoot_phase0 {state : BeaconState preset .phase0}
    {body : BeaconBlock preset .phase0} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.blockV2 signing (.phase0 body)) = .ok root) :
    getBlockSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of a versioned Altair block is the root of its block signature. -/
theorem getBlockSignature_eq_of_requestSigningRoot_altair {state : BeaconState preset .altair}
    {body : BeaconBlock preset .altair} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.blockV2 signing (.altair body)) = .ok root) :
    getBlockSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of the header of a block is the root of the block signature.

The header holds the root of the body of the block, so it has the root of the block.

So a signer that sees only the header signs the root that the proposer's block needs. -/
theorem getBlockSignature_eq_of_requestSigningRoot_header {block : BeaconBlock preset fork}
    {bodyRoot : Root} {version : { v : ConsensusVersion // .bellatrix ≤ v }}
    (bodied : SszType.hashTreeRoot block.body = .ok bodyRoot)
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config (.blockV2 signing (.header version
      ⟨block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, bodyRoot⟩)) = .ok root) :
    getBlockSignature config state block key =
      (Signatures.sign key (packBytes root)).mapError .bls := by
  -- The header and the block have one root, so they have one signing root under any domain.
  have same : ∀ domain : Domain, computeSigningRoot
      (BeaconBlockHeader.mk block.slot block.proposerIndex block.parentRoot block.stateRoot
        bodyRoot) domain = computeSigningRoot block domain := by
    intro domain
    simp only [computeSigningRoot, BeaconBlock.hashTreeRoot_header bodied]
  refine signAtEpoch_eq_of_forkInfoDomain forked ?_
  simp only [requestSigningRoot, same] at rooted
  exact rooted

/-- The root of a RANDAO reveal is the root of the reveal of a block in its epoch. -/
theorem getEpochSignature_eq_of_requestSigningRoot {body : RandaoReveal}
    {block : BeaconBlock preset fork} (epoched : body.epoch = computeEpochAtSlot preset block.slot)
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.randaoReveal signing body) = .ok root) :
    getEpochSignature config state block key =
      (Signatures.sign key (packBytes root)).mapError .bls := by
  unfold getEpochSignature
  rw [← epoched]
  exact signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of a sync committee message is the root its member signs, in the current epoch.

The member signs in the current epoch of the state, so the slot of the message must be in it. -/
theorem getSyncCommitteeMessage_map_signature_eq_of_requestSigningRoot
    {body : SyncCommitteeMessageData}
    {validatorIndex : ValidatorIndex}
    (current : computeEpochAtSlot preset body.slot = getCurrentEpoch state)
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.syncCommitteeMessage signing body) = .ok root) :
    (getSyncCommitteeMessage config state body.beaconBlockRoot validatorIndex key).map
        (·.signature) = (Signatures.sign key (packBytes root)).mapError .bls := by
  have signs : signAtEpoch config state DOMAIN_SYNC_COMMITTEE (getCurrentEpoch state)
      body.beaconBlockRoot key = (Signatures.sign key (packBytes root)).mapError .bls := by
    rw [← current]
    exact signAtEpoch_eq_of_forkInfoDomain forked rooted
  unfold getSyncCommitteeMessage
  rw [signs]
  cases Signatures.sign key (packBytes root) <;> rfl

/-- The root of a sync committee selection is the root of its selection proof. -/
theorem getSyncCommitteeSelectionProof_eq_of_requestSigningRoot
    {body : SyncAggregatorSelectionData} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.syncCommitteeSelectionProof signing body) = .ok root) :
    getSyncCommitteeSelectionProof config state body.slot body.subcommitteeIndex key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of a contribution and proof is the root of its signature. -/
theorem getContributionAndProofSignature_eq_of_requestSigningRoot
    {body : ContributionAndProof preset} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.syncCommitteeContributionAndProof signing body) = .ok root) :
    getContributionAndProofSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-! ## The requests without fork info, and the voluntary exit -/

/-- The root of a registration is the root that the check of a signed registration verifies. -/
theorem verifyRegistrationSignature_of_requestSigningRoot {checks : SignatureChecks}
    {signed : SignedValidatorRegistrationV1} {signingRoot : Option Root}
    (rooted : requestSigningRoot (preset := preset) config
      (.validatorRegistration signingRoot signed.message) = .ok root) :
    verifyRegistrationSignature config checks signed =
      .ok (checks.verify signed.message.pubkey (packBytes root) signed.signature) := by
  unfold requestSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp only [requestDomain, SigningRequest.type, RequestType.domainType] at domained
  simp only at rooted
  simp [verifyRegistrationSignature, verifyBuilderApiSignature, domained,
    rooted, bind, Except.bind, pure, Except.pure]

/-- The root of a deposit at the configured genesis fork version is the root its check verifies.
-/
theorem isValidDepositSignature_of_requestSigningRoot {checks : SignatureChecks}
    {body : DepositSigningData} {signingRoot : Option Root} {signature : BLSSignature}
    (genesis : body.genesisForkVersion = config.GENESIS_FORK_VERSION)
    (rooted : requestSigningRoot (preset := preset) config (.deposit signingRoot body) = .ok root) :
    isValidDepositSignature config checks body.pubkey body.withdrawalCredentials body.amount
      signature = .ok (checks.verify body.pubkey (packBytes root) signature) := by
  unfold requestSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp only [requestDomain, SigningRequest.type, RequestType.domainType] at domained
  simp only at rooted
  rw [genesis] at domained
  simp only [DepositSigningData.message] at rooted
  simp [isValidDepositSignature, isValidDepositMessageSignature, liftSsz, domained, rooted,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The root of a voluntary exit is the root that the check of an exit verifies.

The request carries only its fork info, so it must give the version of the exit domain.

From Deneb that is the version of Capella, and before Deneb the version of the state. -/
theorem voluntaryExitDomain_of_requestSigningRoot {body : VoluntaryExit}
    (chain : signing.forkInfo.genesisValidatorsRoot = state.genesisValidatorsRoot)
    (version : signing.forkInfo.fork.versionAt body.epoch =
      if .dencun ≤ fork then config.CAPELLA_FORK_VERSION
      else state.forkVersions.versionAt body.epoch)
    (rooted : requestSigningRoot (preset := preset) config (.voluntaryExit signing body) =
      .ok root) :
    ∃ domain, voluntaryExitDomain config state body.epoch = .ok domain ∧
      computeSigningRoot body domain = .ok root := by
  unfold requestSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp only [requestDomain, forkInfoDomain, SigningRequest.type, RequestType.domainType] at domained
  simp only at rooted
  refine ⟨domain, ?_, rooted⟩
  rw [version, chain] at domained
  by_cases dencun : Fork.dencun ≤ fork
  · rw [voluntaryExitDomain_of_dencun dencun, liftSsz_ok]
    simpa [dencun] using domained
  · rw [voluntaryExitDomain_of_lt (Nat.lt_of_not_le dencun), liftAccessor_ok,
      getDomain_eq_forkInfoDomain, mapError_ok_iff]
    simpa [dencun, forkInfoDomain, ForkInfo.ofState] using domained

/-! ## The kinds that Gloas adds -/

/-- The root of a bid is the root of the builder's bid signature, in the epoch of its slot. -/
theorem getExecutionPayloadBidSignature_eq_of_requestSigningRoot
    {state : BeaconState preset .glamsterdam} {body : ExecutionPayloadBid preset .glamsterdam}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot config (.executionPayloadBid signing body) = .ok root) :
    getExecutionPayloadBidSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls := by
  unfold requestSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp only [requestDomain, SigningRequest.type, RequestType.domainType, forked] at domained
  simp only at rooted
  have built : builderSigningRoot config state body (some (computeEpochAtSlot preset body.slot)) =
      .ok root := by
    simp [builderSigningRoot, liftAccessor, liftSsz, getDomain_eq_forkInfoDomain, domained,
      rooted, bind, Except.bind, Except.mapError]
  -- Rewrite the root before the signing call, so the kernel never evaluates the call.
  unfold getExecutionPayloadBidSignature
  rw [built, mapError_ok_bind]

/-- The root of an envelope is the root of the builder's envelope signature.

The builder signs in the current epoch of the state.

The request signs in the epoch of the slot of its payload.

So the two epochs must take the same fork version. -/
theorem getExecutionPayloadEnvelopeSignature_eq_of_requestSigningRoot
    {state : BeaconState preset .glamsterdam}
    {body : ExecutionPayloadEnvelope preset .glamsterdam}
    (sameVersion : state.forkVersions.versionAt
        (computeEpochAtSlot preset (body.payload.slotNumber (by decide))) =
      state.forkVersions.versionAt (computeEpochAtSlot preset state.slot))
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot config (.executionPayloadEnvelope signing body) = .ok root) :
    getExecutionPayloadEnvelopeSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls := by
  unfold requestSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp only [requestDomain, SigningRequest.type, RequestType.domainType, forked, forkInfoDomain,
    ForkInfo.ofState, sameVersion] at domained
  simp only at rooted
  have current : getDomain config state DOMAIN_BEACON_BUILDER
      (some (computeEpochAtSlot preset state.slot)) = .ok domain := by
    rw [getDomain_eq_forkInfoDomain]
    simp [forkInfoDomain, ForkInfo.ofState, Except.mapError, domained]
  have built : builderSigningRoot config state body (some (computeEpochAtSlot preset state.slot)) =
      .ok root := by
    simp [builderSigningRoot, liftAccessor, liftSsz, current, rooted, bind, Except.bind,
      Except.mapError]
  -- Rewrite the root before the signing call, so the kernel never evaluates the call.
  unfold getExecutionPayloadEnvelopeSignature
  rw [built, mapError_ok_bind]

/-- The root of the data of a payload attestation is the root its member signs. -/
theorem getPayloadAttestationMessageSignature_eq_of_requestSigningRoot
    {message : PayloadAttestationMessage} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.payloadAttestationMessage signing message.data) = .ok root) :
    getPayloadAttestationMessageSignature config state message key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoDomain forked rooted

/-- The root of proposer preferences is the root that the proposer signs for them.

The proposer signs at the fork version that the configuration gives to the proposal epoch.

So the fork info must give that version at that epoch, on the chain of the state. -/
theorem proposerPreferencesSigningRoot_eq_of_requestSigningRoot {body : ProposerPreferences}
    (chain : signing.forkInfo.genesisValidatorsRoot = state.genesisValidatorsRoot)
    (version : signing.forkInfo.fork.versionAt (computeEpochAtSlot preset body.proposalSlot) =
      config.computeForkVersion (computeEpochAtSlot preset body.proposalSlot))
    (rooted : requestSigningRoot (preset := preset) config
      (.proposerPreferences signing body) = .ok root) :
    proposerPreferencesSigningRoot config state body = .ok root := by
  unfold requestSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp only [requestDomain, SigningRequest.type, RequestType.domainType, forkInfoDomain, version,
    chain] at domained
  simp only at rooted
  simp [proposerPreferencesSigningRoot, domained, rooted, bind, Except.bind]

/-- The root of the authentication of a Builder API request is the root that its check verifies.
-/
theorem verifyBuilderRequestAuthSignature_of_requestSigningRoot {checks : SignatureChecks}
    {signed : SignedBuilderRequestAuth} {pubkey : BLSPubkey} {signingRoot : Option Root}
    {nonEmpty : signed.message.data.data.size ≠ 0}
    (rooted : requestSigningRoot (preset := preset) config
      (.builderRequestAuth signingRoot signed.message nonEmpty) = .ok root) :
    verifyBuilderRequestAuthSignature config checks signed pubkey =
      .ok (checks.verify pubkey (packBytes root) signed.signature) := by
  unfold requestSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp only [requestDomain, SigningRequest.type, RequestType.domainType] at domained
  simp only at rooted
  simp [verifyBuilderRequestAuthSignature, verifyBuilderApiSignature, domained, rooted, bind,
    Except.bind, pure, Except.pure]

/-! ## The domains of the kinds -/

/-- The first four bytes of the domain of a request are the domain type of its kind.

This holds whatever its fork info, or its genesis fork version. -/
theorem requestDomain_prefix {request : SigningRequest preset} {domain : Domain}
    (computed : requestDomain config request = .ok domain) (i : Nat) (lt : i < 4) :
    domain[i] = request.type.domainType[i] := by
  cases request <;> (try rename_i body; cases body) <;>
    simp only [requestDomain, forkInfoDomain, builderDomain] at computed <;>
    exact computeDomain_prefix computed i lt

/-- Two requests whose kinds have different domain types never share a domain.

It is about the domains, not the signing roots.

Different domains give different signing roots only under the collision resistance of SHA-256. -/
theorem requestDomain_ne {first second : SigningRequest preset} {firstDomain secondDomain : Domain}
    (differ : first.type.domainType ≠ second.type.domainType)
    (firstComputed : requestDomain config first = .ok firstDomain)
    (secondComputed : requestDomain config second = .ok secondDomain) :
    firstDomain ≠ secondDomain := by
  intro same
  apply differ
  ext i lt
  rw [← requestDomain_prefix firstComputed i lt, ← requestDomain_prefix secondComputed i lt, same]

/-- Two kinds share a domain type exactly when they are equal, or one of three pairs.

The pairs are the two block kinds, the two aggregate kinds, and the bid with the envelope. -/
theorem RequestType.domainType_eq_iff (first second : RequestType) :
    first.domainType = second.domainType ↔ first = second ∨
      (first, second) ∈
        [(.block, .blockV2), (.blockV2, .block), (.aggregateAndProof, .aggregateAndProofV2),
          (.aggregateAndProofV2, .aggregateAndProof),
          (.executionPayloadBid, .executionPayloadEnvelope),
          (.executionPayloadEnvelope, .executionPayloadBid)] := by
  cases first <;> cases second <;> decide

end EthLib.Consensus.RemoteSigningApi
