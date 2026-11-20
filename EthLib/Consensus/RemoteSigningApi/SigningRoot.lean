module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.RemoteSigningApi.Request

/-!
# `Consensus.RemoteSigningApi.SigningRoot`

The root that a remote signer signs for each request.

The source names the kinds of request, and names a domain only for the kinds that Gloas adds.

The root of every other kind comes from the duty that it serves.

Each root is that of the object of the duty, under the domain that the fork info gives.

The fork info stands for the state: its fork versions and its root of the genesis validators.

A deposit and a registration are signed outside any fork, at the genesis fork version.

The [schemas] fix the requests, and the examples of the [sign endpoint] carry their roots.

[schemas]: https://github.com/ethereum/remote-signing-api/blob/44e9e0dcc115c91f8b739684f4789a8310476bd9/signing/schemas.yaml
[sign endpoint]: https://github.com/ethereum/remote-signing-api/blob/44e9e0dcc115c91f8b739684f4789a8310476bd9/signing/paths/sign.yaml
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Base Serialization.Ssz

/-- The fork info of a state: its fork versions and its root of the genesis validators. -/
def ForkInfo.ofState {preset : Preset} {fork : Fork} (state : BeaconState preset fork) : ForkInfo :=
  ⟨state.forkVersions, state.genesisValidatorsRoot⟩

/-- The domain of a kind of message at an epoch, under the fork info of a request.

It is the rule of the domain of a state, with the fork versions and the root of the request. -/
def forkInfoDomain (config : Config) (info : ForkInfo) (domainType : DomainType) (epoch : Epoch) :
    Except Err Domain :=
  computeDomain config domainType (info.fork.versionAt epoch) info.genesisValidatorsRoot

/-- The deposit message of the consensus layer that a deposit request describes. -/
def DepositSigningData.message (deposit : DepositSigningData) : DepositMessage :=
  ⟨deposit.pubkey, deposit.withdrawalCredentials, deposit.amount⟩

/-- The domain type of a kind of request.

The source names it for the kinds that Gloas adds, and the duty of each other kind fixes it. -/
def RequestType.domainType : RequestType → DomainType
  | .aggregationSlot => DOMAIN_SELECTION_PROOF
  | .aggregateAndProof | .aggregateAndProofV2 => DOMAIN_AGGREGATE_AND_PROOF
  | .attestation => DOMAIN_BEACON_ATTESTER
  | .block | .blockV2 => DOMAIN_BEACON_PROPOSER
  | .deposit => DOMAIN_DEPOSIT
  | .randaoReveal => DOMAIN_RANDAO
  | .voluntaryExit => DOMAIN_VOLUNTARY_EXIT
  | .syncCommitteeMessage => DOMAIN_SYNC_COMMITTEE
  | .syncCommitteeSelectionProof => DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
  | .syncCommitteeContributionAndProof => DOMAIN_CONTRIBUTION_AND_PROOF
  | .validatorRegistration => DOMAIN_APPLICATION_BUILDER
  | .executionPayloadBid | .executionPayloadEnvelope => DOMAIN_BEACON_BUILDER
  | .payloadAttestationMessage => DOMAIN_PTC_ATTESTER
  | .proposerPreferences => DOMAIN_PROPOSER_PREFERENCES
  | .builderRequestAuth => DOMAIN_BUILDER_REQUEST_AUTH

/-- The domain under which a remote signer signs a request, of the domain type of its kind.

A kind with fork info takes the domain that its fork info gives at the epoch of its duty.

A deposit takes its own genesis fork version, with a zero root of the validators.

A registration and a Builder API authentication take the domain of the Builder API. -/
def requestDomain {preset : Preset} (config : Config) (request : SigningRequest preset) :
    Except Err Domain :=
  let domainType := request.type.domainType
  match request with
  | .aggregationSlot signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .aggregateAndProof signing body | .aggregateAndProofV2 signing _ body =>
    forkInfoDomain config signing.forkInfo domainType
      (computeEpochAtSlot preset body.aggregate.data.slot)
  | .attestation signing body =>
    forkInfoDomain config signing.forkInfo domainType body.target.epoch
  | .block signing body | .blockV2 signing (.phase0 body) | .blockV2 signing (.altair body) =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .blockV2 signing (.header _ header) =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset header.slot)
  | .deposit _ body => computeDomain config domainType body.genesisForkVersion
  | .randaoReveal signing body => forkInfoDomain config signing.forkInfo domainType body.epoch
  | .voluntaryExit signing body => forkInfoDomain config signing.forkInfo domainType body.epoch
  | .syncCommitteeMessage signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .syncCommitteeSelectionProof signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .syncCommitteeContributionAndProof signing body =>
    forkInfoDomain config signing.forkInfo domainType
      (computeEpochAtSlot preset body.contribution.slot)
  | .validatorRegistration .. | .builderRequestAuth .. => builderDomain config domainType
  | .executionPayloadBid signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .executionPayloadEnvelope signing body =>
    forkInfoDomain config signing.forkInfo domainType
      (computeEpochAtSlot preset (body.payload.slotNumber (by decide)))
  | .payloadAttestationMessage signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .proposerPreferences signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.proposalSlot)

/-- The root that a remote signer signs for a request.

Each kind with fork info before Gloas signs the object of its duty, at the epoch of that duty:

- the slot of an aggregator selection, as a selection proof, in the epoch of the slot;
- an aggregate and its proof, in the epoch of the slot of the aggregate;
- the data of an attestation, in its target epoch;
- a block, or its header, in the epoch of its slot;
- the epoch of a RANDAO reveal, in that epoch;
- a voluntary exit, in its epoch;
- the block root of a sync committee message, in the epoch of its slot;
- the selection data of a sync committee aggregator, in the epoch of its slot;
- a contribution and its proof, in the epoch of the slot of the contribution.

Each kind that Gloas adds signs under the domain type that the source names:

- a bid in the epoch of its slot, and an envelope in the epoch of its payload's slot;
- the data of a payload attestation, in the epoch of its slot;
- the preferences of a proposer, in the epoch of the proposal slot.

A deposit is signed at its own genesis fork version, with a zero root of the validators.

A registration and the authentication of a Builder API request take the domain of the Builder API.

That is the domain at the configured genesis fork version, with a zero root. -/
def requestSigningRoot {preset : Preset} (config : Config) (request : SigningRequest preset) :
    Except Err Root := do
  let domain ← requestDomain config request
  match request with
  | .aggregationSlot _ body => computeSigningRoot body.slot domain
  | .aggregateAndProof _ body | .aggregateAndProofV2 _ _ body => computeSigningRoot body domain
  | .attestation _ body => computeSigningRoot body domain
  | .block _ body | .blockV2 _ (.phase0 body) | .blockV2 _ (.altair body) =>
    computeSigningRoot body domain
  | .blockV2 _ (.header _ header) => computeSigningRoot header domain
  | .deposit _ body => computeSigningRoot body.message domain
  | .randaoReveal _ body => computeSigningRoot body.epoch domain
  | .voluntaryExit _ body => computeSigningRoot body domain
  | .syncCommitteeMessage _ body => computeSigningRoot body.beaconBlockRoot domain
  | .syncCommitteeSelectionProof _ body => computeSigningRoot body domain
  | .syncCommitteeContributionAndProof _ body => computeSigningRoot body domain
  | .validatorRegistration _ body => computeSigningRoot body domain
  | .executionPayloadBid _ body => computeSigningRoot body domain
  | .executionPayloadEnvelope _ body => computeSigningRoot body domain
  | .payloadAttestationMessage _ body => computeSigningRoot body domain
  | .proposerPreferences _ body => computeSigningRoot body domain
  | .builderRequestAuth _ body _ => computeSigningRoot body domain

end EthLib.Consensus.RemoteSigningApi
