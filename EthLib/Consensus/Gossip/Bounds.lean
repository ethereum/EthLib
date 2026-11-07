module

public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Containers.Block
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

A fork for which that list is not written has no type for any topic.

- Blocks, aggregates, attester slashings and light client updates take their type at the fork.
- An attestation subnet carries an `Attestation` before Electra, a `SingleAttestation` from it.
- Data column sidecars, bids and payload envelopes take their type at the fork.
- Every other topic carries one type at every fork that has it.

A gossip payload has no smallest length, so only the largest size of the type bounds it.
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

/-- The SSZ type of the message of a topic at a fork, if the fork lists the topic. -/
def topicDesc (preset : Preset) (config : Config) (fork : Fork) (topic : GossipTopic) :
    Option Desc :=
  match config.gossipTopics fork with
  | some topics => if topic ∈ topics then some (topic.messageDesc preset fork) else none
  | none => none

/-- The bound on the payload length of a topic at a fork, if the fork lists the topic. -/
def topicBound (preset : Preset) (config : Config) (fork : Fork) (topic : GossipTopic) :
    Option UInt64 :=
  (topicDesc preset config fork topic).map fun shape => (Networking.ReqResp.payloadBounds shape).2

end EthLib.Consensus
