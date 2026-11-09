module

public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Containers.InclusionList
public import EthLib.Consensus.Containers.PayloadAttestation
public import EthLib.Consensus.Containers.ProposerPreferences
public import EthLib.Consensus.Gossip.Topics
public import EthLib.Consensus.LightClient.Containers
public import EthLib.Networking.ReqResp.Bounds

/-!
# `Consensus.Gossip.Bounds`

The SSZ type of the message of each gossip topic, and the bound on the length of its payload.

The fork is that of the fork digest of the topic.

A topic that the configuration does not list at the fork has no type.

- Blocks, aggregates, attester slashings and light client updates take their type at the fork.
- An attestation subnet carries an `Attestation` before Electra, a `SingleAttestation` from it.
- Data column sidecars, bids and payload envelopes take their type at the fork.
- Every other topic carries one type at every fork that has it.

A gossip payload has no smallest length, so only a largest length bounds it.

From Gloas, the networking specification sets a size limit on the messages of some topics.

[EIP-7688](https://eips.ethereum.org/EIPS/eip-7688#network-message-size-bounds) asks for them.

The limits are preset values.

- Aggregates, attester slashings and bids have one from Gloas.
- Inclusion lists have one from Heze, and Heze raises the limit of a bid for its inclusion bits.

The bound is the largest size of the type, or the size limit of the topic if that is lower.

From Gloas the specification also bounds a data column sidecar, by a size from the blob schedule.

EthLib does not hold the topic to that size, so the topic keeps the bound of its type.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The SSZ type of the message of a topic, whatever the fork lists. -/
def GossipTopic.messageDesc (preset : Preset) (fork : Fork) : GossipTopic → Desc
  | .beaconBlock => SszType.desc (SignedBeaconBlock preset fork)
  | .beaconAggregateAndProof => SszType.desc (SignedAggregateAndProof preset fork)
  | .beaconAttestation _ =>
    if .pectra ≤ fork then SszType.desc SingleAttestation
    else SszType.desc (Attestation preset fork)
  | .voluntaryExit => SszType.desc SignedVoluntaryExit
  | .proposerSlashing => SszType.desc ProposerSlashing
  | .attesterSlashing => SszType.desc (AttesterSlashing preset fork)
  | .syncCommitteeContributionAndProof => SszType.desc (SignedContributionAndProof preset)
  | .syncCommittee _ => SszType.desc SyncCommitteeMessage
  | .lightClientFinalityUpdate => SszType.desc (LightClientFinalityUpdate preset fork)
  | .lightClientOptimisticUpdate => SszType.desc (LightClientOptimisticUpdate preset fork)
  | .blsToExecutionChange => SszType.desc SignedBLSToExecutionChange
  | .blobSidecar _ => SszType.desc (BlobSidecar preset)
  | .dataColumnSidecar _ => SszType.desc (DataColumnSidecar preset fork)
  | .executionPayloadBid => SszType.desc (SignedExecutionPayloadBid preset fork)
  | .executionPayload => SszType.desc (SignedExecutionPayloadEnvelope preset fork)
  | .payloadAttestationMessage => SszType.desc PayloadAttestationMessage
  | .proposerPreferences => SszType.desc SignedProposerPreferences
  | .inclusionList => SszType.desc SignedInclusionList

/-- The SSZ type of the message of a topic at a fork, if the fork lists the topic. -/
def topicDesc (preset : Preset) (config : Config) (fork : Fork) (topic : GossipTopic) :
    Option Desc :=
  if topic ∈ config.gossipTopics fork then some (topic.messageDesc preset fork) else none

/-- The size limit that the networking specification sets on the message of a topic at a fork.

Aggregates, attester slashings and bids have one from Gloas, and inclusion lists from Heze.

The limit of a bid is that of its fork, which Heze raises for the inclusion bits. -/
def GossipTopic.sizeLimit (preset : Preset) (fork : Fork) : GossipTopic → Option UInt64
  | .beaconAggregateAndProof =>
    if .glamsterdam ≤ fork then some preset.MAX_SIGNED_AGGREGATE_AND_PROOF_SIZE else none
  | .attesterSlashing =>
    if .glamsterdam ≤ fork then some preset.MAX_ATTESTER_SLASHING_SIZE else none
  | .executionPayloadBid =>
    if .glamsterdam ≤ fork then some (parameters preset fork).MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE
    else none
  | .inclusionList => if .hegota ≤ fork then some preset.MAX_SIGNED_INCLUSION_LIST_SIZE else none
  | _ => none

/-- The bound on the payload length of a topic at a fork, if the fork lists the topic.

It is the largest payload length of the type, held to the size limit of the topic if it has one. -/
def topicBound (preset : Preset) (config : Config) (fork : Fork) (topic : GossipTopic) :
    Option UInt64 :=
  (topicDesc preset config fork topic).map fun shape =>
    match topic.sizeLimit preset fork with
    | some limit => min (Networking.ReqResp.payloadBounds shape).2 limit
    | none => (Networking.ReqResp.payloadBounds shape).2

end EthLib.Consensus
