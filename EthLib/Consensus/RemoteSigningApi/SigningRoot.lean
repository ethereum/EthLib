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

[schemas]: https://github.com/ethereum/remote-signing-api/blob/514525ca961a9d001e96a02bf870285a8ae401a4/signing/schemas.yaml
[sign endpoint]: https://github.com/ethereum/remote-signing-api/blob/514525ca961a9d001e96a02bf870285a8ae401a4/signing/paths/sign.yaml
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Base Serialization.Ssz

/-- The fork info of a state: its fork versions and its root of the genesis validators. -/
def ForkInfo.ofState {preset : Preset} {fork : Fork} (state : BeaconState preset fork) : ForkInfo :=
  -- The schema: the fork, with its two versions and its epoch, and the genesis validators root.
  ⟨state.forkVersions, state.genesisValidatorsRoot⟩

/-- The domain of a kind of message at an epoch, under the fork info of a request.

It is the rule of the domain of a state, with the fork versions and the root of the request. -/
def forkInfoDomain (config : Config) (info : ForkInfo) (domainType : DomainType) (epoch : Epoch) :
    Except Err Domain :=
  -- The fork version is the previous one before the epoch of the fork, else the current one.
  --
  -- The domain is the domain type, then the first 28 bytes of the root of the fork data.
  --
  -- The fork data is that version and the genesis validators root of the request.
  computeDomain config domainType (info.fork.versionAt epoch) info.genesisValidatorsRoot

/-- The deposit message of the consensus layer that a deposit request describes. -/
def DepositSigningData.message (deposit : DepositSigningData) : DepositMessage :=
  -- The public key, the withdrawal credentials and the amount; the fork version is left out.
  ⟨deposit.pubkey, deposit.withdrawalCredentials, deposit.amount⟩

/-- The domain type of a kind of request.

The source names it for the kinds that Gloas adds, and the duty of each other kind fixes it. -/
def RequestType.domainType : RequestType → DomainType
  -- The duties before Gloas, each with the domain type of the message that it signs.
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
  -- A registration with builders, under the application domain type of the Builder API.
  | .validatorRegistration => DOMAIN_APPLICATION_BUILDER
  -- The schemas: a bid and an envelope use the beacon builder domain type, 0x0B000000.
  | .executionPayloadBid | .executionPayloadEnvelope => DOMAIN_BEACON_BUILDER
  -- The schemas: the data of a payload attestation uses the PTC attester domain type, 0x0C000000.
  | .payloadAttestationMessage => DOMAIN_PTC_ATTESTER
  -- The schemas: the preferences of a proposer use the domain type 0x0D000000.
  | .proposerPreferences => DOMAIN_PROPOSER_PREFERENCES
  -- The schemas: the authentication of a Builder API request uses the domain type 0x0B000001.
  | .builderRequestAuth => DOMAIN_BUILDER_REQUEST_AUTH

/-- The domain under which a remote signer signs a request, of the domain type of its kind. -/
def requestDomain {preset : Preset} (config : Config) (request : SigningRequest preset) :
    Except Err Domain :=
  let domainType := request.type.domainType
  match request with
  -- A kind with fork info takes the domain that its fork info gives at the epoch of its duty.
  --
  -- A selection proof: the epoch of the slot.
  | .aggregationSlot signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  -- An aggregate and its proof: the epoch of the slot of the aggregate.
  | .aggregateAndProof signing body | .aggregateAndProofV2 signing _ body =>
    forkInfoDomain config signing.forkInfo domainType
      (computeEpochAtSlot preset body.aggregate.data.slot)
  -- The data of an attestation: its target epoch.
  | .attestation signing body =>
    forkInfoDomain config signing.forkInfo domainType body.target.epoch
  -- A block or its header: the epoch of its slot.
  | .block signing body | .blockV2 signing (.phase0 body) | .blockV2 signing (.altair body) =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .blockV2 signing (.header _ header) =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset header.slot)
  -- A deposit: the genesis fork version of the request, with a zero genesis validators root.
  --
  -- A deposit stays valid across forks, so it takes the genesis fork version, not a fork info.
  | .deposit _ body => computeDomain config domainType body.genesisForkVersion
  -- A RANDAO reveal: its epoch.
  | .randaoReveal signing body => forkInfoDomain config signing.forkInfo domainType body.epoch
  -- A voluntary exit: its epoch, at the fork version that the fork info gives.
  --
  -- From Deneb, EIP-7044 signs exits at the Capella fork version.
  --
  -- The source does not say whether the client or the signer applies it.
  --
  -- EthLib takes the version from the fork info, as for every kind with fork info.
  | .voluntaryExit signing body => forkInfoDomain config signing.forkInfo domainType body.epoch
  -- A sync committee message, a selection proof or a contribution: the epoch of its slot.
  | .syncCommitteeMessage signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .syncCommitteeSelectionProof signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  | .syncCommitteeContributionAndProof signing body =>
    forkInfoDomain config signing.forkInfo domainType
      (computeEpochAtSlot preset body.contribution.slot)
  -- A registration and a Builder API authentication: the domain of the Builder API.
  --
  -- Both take the configured genesis fork version and a zero genesis validators root.
  --
  -- The schemas say so for the authentication; the Builder API, for a registration.
  | .validatorRegistration .. | .builderRequestAuth .. => builderDomain config domainType
  -- A bid: the epoch of its slot.
  | .executionPayloadBid signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  -- An envelope: the epoch of the slot of its payload.
  | .executionPayloadEnvelope signing body =>
    forkInfoDomain config signing.forkInfo domainType
      (computeEpochAtSlot preset (body.payload.slotNumber (by decide)))
  -- The data of a payload attestation: the epoch of its slot.
  | .payloadAttestationMessage signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.slot)
  -- The preferences of a proposer: the epoch of the proposal slot.
  | .proposerPreferences signing body =>
    forkInfoDomain config signing.forkInfo domainType (computeEpochAtSlot preset body.proposalSlot)

/-- The root that a remote signer signs for a request. -/
def requestSigningRoot {preset : Preset} (config : Config) (request : SigningRequest preset) :
    Except Err Root := do
  let domain ← requestDomain config request
  -- Each signing root is the root of the signing data: the root of the object and the domain.
  match request with
  -- A selection proof signs the slot itself.
  | .aggregationSlot _ body => computeSigningRoot body.slot domain
  | .aggregateAndProof _ body | .aggregateAndProofV2 _ _ body => computeSigningRoot body domain
  | .attestation _ body => computeSigningRoot body domain
  | .block _ body | .blockV2 _ (.phase0 body) | .blockV2 _ (.altair body) =>
    computeSigningRoot body domain
  -- From Bellatrix the header, whose root is the root of the block.
  | .blockV2 _ (.header _ header) => computeSigningRoot header domain
  -- A deposit signs its deposit message, without the fork version.
  | .deposit _ body => computeSigningRoot body.message domain
  -- A RANDAO reveal signs the epoch itself.
  | .randaoReveal _ body => computeSigningRoot body.epoch domain
  | .voluntaryExit _ body => computeSigningRoot body domain
  -- A sync committee message signs the block root alone, not the slot.
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
