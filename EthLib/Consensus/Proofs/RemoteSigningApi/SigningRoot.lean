module

public import EthLib.Consensus.RemoteSigningApi.SigningRoot
public import EthLib.Consensus.Proofs.HonestValidator
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.BuilderRequests

/-!
# Proofs: the root of each request is the root that its duty signs

The domain that the fork info of a request gives is the domain of a state with that fork info.

So under the fork info of a state, a request has the root that its duty signs in that state.

The header of a block has the root of the block.

So a signer that sees only the header signs the root of the proposer's block.

A registration and a deposit get the root that their checks verify.

A voluntary exit gets the root that its check verifies, under a hypothesis on its fork version.
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
theorem signAtEpoch_eq_of_forkInfoSigningRoot {α : Type} [SszType α] {domainType : DomainType}
    {epoch : Epoch} {object : α} {info : ForkInfo} (forked : info = .ofState state)
    (rooted : forkInfoSigningRoot config info domainType epoch object = .ok root) :
    signAtEpoch config state domainType epoch object key =
      (Signatures.sign key (packBytes root)).mapError .bls := by
  subst forked
  unfold forkInfoSigningRoot at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  simp [signAtEpoch, getDomain_eq_forkInfoDomain, domained, rooted, bind, Except.bind,
    Except.mapError]

/-! ## The duties of a validator -/

/-- The root of an aggregator selection is the root of the selection proof of its slot. -/
theorem getSlotSignature_eq_of_requestSigningRoot {body : AggregationSlot}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.aggregationSlot signing body) = .ok root) :
    getSlotSignature config state body.slot key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

/-- The root of a Phase 0 aggregate is the root of its aggregate and proof signature. -/
theorem getAggregateAndProofSignature_eq_of_requestSigningRoot
    {state : BeaconState preset .phase0} {body : AggregateAndProof preset .phase0}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.aggregateAndProof signing body) = .ok root) :
    getAggregateAndProofSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

/-- The root of a versioned aggregate is the root of its signature at the fork of its version. -/
theorem getAggregateAndProofSignature_eq_of_requestSigningRoot_v2 {version : ConsensusVersion}
    {state : BeaconState preset version.fork} {body : AggregateAndProof preset version.fork}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.aggregateAndProofV2 signing version body) = .ok root) :
    getAggregateAndProofSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

/-- The root of attestation data is the root of its attestation signature. -/
theorem getAttestationSignature_eq_of_requestSigningRoot {body : AttestationData}
    (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config (.attestation signing body) = .ok root) :
    getAttestationSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

/-- The root of a Phase 0 block is the root of its block signature. -/
theorem getBlockSignature_eq_of_requestSigningRoot {state : BeaconState preset .phase0}
    {body : BeaconBlock preset .phase0} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config (.block signing body) = .ok root) :
    getBlockSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

/-- The root of a versioned Phase 0 block is the root of its block signature. -/
theorem getBlockSignature_eq_of_requestSigningRoot_phase0 {state : BeaconState preset .phase0}
    {body : BeaconBlock preset .phase0} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.blockV2 signing (.phase0 body)) = .ok root) :
    getBlockSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

/-- The root of a versioned Altair block is the root of its block signature. -/
theorem getBlockSignature_eq_of_requestSigningRoot_altair {state : BeaconState preset .altair}
    {body : BeaconBlock preset .altair} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.blockV2 signing (.altair body)) = .ok root) :
    getBlockSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

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
  refine signAtEpoch_eq_of_forkInfoSigningRoot forked ?_
  unfold forkInfoSigningRoot
  simp only [requestSigningRoot, forkInfoSigningRoot, same] at rooted
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
  exact signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

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
    exact signAtEpoch_eq_of_forkInfoSigningRoot forked rooted
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
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

/-- The root of a contribution and proof is the root of its signature. -/
theorem getContributionAndProofSignature_eq_of_requestSigningRoot
    {body : ContributionAndProof preset} (forked : signing.forkInfo = .ofState state)
    (rooted : requestSigningRoot (preset := preset) config
      (.syncCommitteeContributionAndProof signing body) = .ok root) :
    getContributionAndProofSignature config state body key =
      (Signatures.sign key (packBytes root)).mapError .bls :=
  signAtEpoch_eq_of_forkInfoSigningRoot forked rooted

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
  unfold requestSigningRoot forkInfoSigningRoot forkInfoDomain at rooted
  obtain ⟨domain, domained, rooted⟩ := bind_ok_iff.mp rooted
  refine ⟨domain, ?_, rooted⟩
  rw [version, chain] at domained
  by_cases dencun : Fork.dencun ≤ fork
  · rw [voluntaryExitDomain_of_dencun dencun, liftSsz_ok]
    simpa [dencun] using domained
  · rw [voluntaryExitDomain_of_lt (Nat.lt_of_not_le dencun), liftAccessor_ok,
      getDomain_eq_forkInfoDomain, mapError_ok_iff]
    simpa [dencun, forkInfoDomain, ForkInfo.ofState] using domained

end EthLib.Consensus.RemoteSigningApi
