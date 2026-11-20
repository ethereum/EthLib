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

/-- The fork version of an epoch: the previous version before the fork, the current one after. -/
def _root_.EthLib.Consensus.ForkVersions.versionAt (versions : ForkVersions) (epoch : Epoch) :
    Version :=
  if epoch < versions.epoch then versions.previousVersion else versions.currentVersion

/-- The fork info of a state: its fork versions and its root of the genesis validators. -/
def ForkInfo.ofState {preset : Preset} {fork : Fork} (state : BeaconState preset fork) : ForkInfo :=
  ⟨state.forkVersions, state.genesisValidatorsRoot⟩

/-- The domain of a kind of message at an epoch, under the fork info of a request.

It is the rule of the domain of a state, with the fork versions and the root of the request. -/
def forkInfoDomain (config : Config) (info : ForkInfo) (domainType : DomainType) (epoch : Epoch) :
    Except Err Domain :=
  computeDomain config domainType (info.fork.versionAt epoch) info.genesisValidatorsRoot

/-- The root of an object under a domain type, at an epoch, under the fork info of a request. -/
def forkInfoSigningRoot {α : Type} [SszType α] (config : Config) (info : ForkInfo)
    (domainType : DomainType) (epoch : Epoch) (object : α) : Except Err Root := do
  computeSigningRoot object (← forkInfoDomain config info domainType epoch)

/-- The deposit message of the consensus layer that a deposit request describes. -/
def DepositSigningData.message (deposit : DepositSigningData) : DepositMessage :=
  ⟨deposit.pubkey, deposit.withdrawalCredentials, deposit.amount⟩

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
def requestSigningRoot {preset : Preset} (config : Config) :
    SigningRequest preset → Except Err Root
  | .aggregationSlot signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_SELECTION_PROOF
      (computeEpochAtSlot preset body.slot) body.slot
  | .aggregateAndProof signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_AGGREGATE_AND_PROOF
      (computeEpochAtSlot preset body.aggregate.data.slot) body
  | .aggregateAndProofV2 signing _ body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_AGGREGATE_AND_PROOF
      (computeEpochAtSlot preset body.aggregate.data.slot) body
  | .attestation signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_BEACON_ATTESTER body.target.epoch body
  | .block signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_BEACON_PROPOSER
      (computeEpochAtSlot preset body.slot) body
  | .blockV2 signing (.phase0 block) | .blockV2 signing (.altair block) =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_BEACON_PROPOSER
      (computeEpochAtSlot preset block.slot) block
  | .blockV2 signing (.header _ header) =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_BEACON_PROPOSER
      (computeEpochAtSlot preset header.slot) header
  | .deposit _ body => do
    computeSigningRoot body.message
      (← computeDomain config DOMAIN_DEPOSIT body.genesisForkVersion)
  | .randaoReveal signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_RANDAO body.epoch body.epoch
  | .voluntaryExit signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_VOLUNTARY_EXIT body.epoch body
  | .syncCommitteeMessage signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_SYNC_COMMITTEE
      (computeEpochAtSlot preset body.slot) body.beaconBlockRoot
  | .syncCommitteeSelectionProof signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
      (computeEpochAtSlot preset body.slot) body
  | .syncCommitteeContributionAndProof signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_CONTRIBUTION_AND_PROOF
      (computeEpochAtSlot preset body.contribution.slot) body
  | .validatorRegistration _ body => do
    computeSigningRoot body (← builderDomain config)
  | .executionPayloadBid signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_BEACON_BUILDER
      (computeEpochAtSlot preset body.slot) body
  | .executionPayloadEnvelope signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_BEACON_BUILDER
      (computeEpochAtSlot preset (body.payload.slotNumber (by decide))) body
  | .payloadAttestationMessage signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_PTC_ATTESTER
      (computeEpochAtSlot preset body.slot) body
  | .proposerPreferences signing body =>
    forkInfoSigningRoot config signing.forkInfo DOMAIN_PROPOSER_PREFERENCES
      (computeEpochAtSlot preset body.proposalSlot) body
  | .builderRequestAuth _ body _ => do
    computeSigningRoot body
      (← builderDomain config DOMAIN_BUILDER_REQUEST_AUTH)

end EthLib.Consensus.RemoteSigningApi
