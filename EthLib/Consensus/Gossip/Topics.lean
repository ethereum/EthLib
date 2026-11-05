module

public import EthLib.Base.Fork
public import EthLib.Consensus.Config
public import EthLib.Consensus.Shuffle
public import EthLib.Networking.Enr.Consensus
public import EthLib.Networking.Gossip.Subnet

/-!
# `Consensus.Gossip.Topics`

The gossip topics of each fork, and the subnet that carries a message.

A topic is a name, and a subnet topic is a base name with a subnet ID.

Phase 0 has the block, aggregate, attestation, exit and slashing topics.

Altair adds the sync committee topics and the two light client update topics.

Capella adds the topic of withdrawal credential changes.

Deneb adds the blob sidecar subnets, and Electra raises their number.

Fulu replaces the blob sidecar subnets by the data column sidecar subnets.

Gloas adds the topics of builder bids, payloads, payload attestations and proposer preferences.

The topics of Heze are not yet specified here, so Heze has no topic set.
-/

@[expose] public section

namespace EthLib.Consensus

open Base
open Networking.Gossip (SubnetID SubnetError subnetTopicName)

/-- A gossip topic of the consensus layer, without its fork digest. -/
inductive GossipTopic where
  /-- Signed beacon blocks. -/
  | beaconBlock
  /-- Signed aggregates of attestations, with the proof that their sender aggregates. -/
  | beaconAggregateAndProof
  /-- Attestations of the committees that one attestation subnet carries. -/
  | beaconAttestation (subnet : SubnetID)
  /-- Signed voluntary exits. -/
  | voluntaryExit
  /-- Proposer slashings. -/
  | proposerSlashing
  /-- Attester slashings. -/
  | attesterSlashing
  /-- Signed contributions of sync subcommittees, with their aggregation proofs. -/
  | syncCommitteeContributionAndProof
  /-- Sync committee messages of one sync subcommittee. -/
  | syncCommittee (subnet : SubnetID)
  /-- Light client updates that carry a finalized header. -/
  | lightClientFinalityUpdate
  /-- Light client updates that carry the latest attested header. -/
  | lightClientOptimisticUpdate
  /-- Signed changes of withdrawal credentials to an execution address. -/
  | blsToExecutionChange
  /-- Blob sidecars of one blob subnet. -/
  | blobSidecar (subnet : SubnetID)
  /-- Data column sidecars of one column subnet. -/
  | dataColumnSidecar (subnet : SubnetID)
  /-- From Gloas: signed bids of builders for the payload of a slot. -/
  | executionPayloadBid
  /-- From Gloas: signed envelopes that reveal the payload of a block. -/
  | executionPayload
  /-- From Gloas: votes of the payload timeliness committee on a payload. -/
  | payloadAttestationMessage
  /-- From Gloas: signed preferences of proposers for their coming slots. -/
  | proposerPreferences
  deriving DecidableEq, Repr

/-- The name of a topic, as it appears between the fork digest and the encoding. -/
def GossipTopic.name : GossipTopic → String
  | .beaconBlock => "beacon_block"
  | .beaconAggregateAndProof => "beacon_aggregate_and_proof"
  | .beaconAttestation subnet => subnetTopicName "beacon_attestation" subnet
  | .voluntaryExit => "voluntary_exit"
  | .proposerSlashing => "proposer_slashing"
  | .attesterSlashing => "attester_slashing"
  | .syncCommitteeContributionAndProof => "sync_committee_contribution_and_proof"
  | .syncCommittee subnet => subnetTopicName "sync_committee" subnet
  | .lightClientFinalityUpdate => "light_client_finality_update"
  | .lightClientOptimisticUpdate => "light_client_optimistic_update"
  | .blsToExecutionChange => "bls_to_execution_change"
  | .blobSidecar subnet => subnetTopicName "blob_sidecar" subnet
  | .dataColumnSidecar subnet => subnetTopicName "data_column_sidecar" subnet
  | .executionPayloadBid => "execution_payload_bid"
  | .executionPayload => "execution_payload"
  | .payloadAttestationMessage => "payload_attestation_message"
  | .proposerPreferences => "proposer_preferences"

/-- The topics with no subnet, each with its name. -/
def GossipTopic.global : List GossipTopic :=
  [.beaconBlock, .beaconAggregateAndProof, .voluntaryExit, .proposerSlashing, .attesterSlashing,
    .syncCommitteeContributionAndProof, .lightClientFinalityUpdate,
    .lightClientOptimisticUpdate, .blsToExecutionChange, .executionPayloadBid, .executionPayload,
    .payloadAttestationMessage, .proposerPreferences]

/-- The topics that Gloas adds, as EIP-7732 lists them in its section "P2P changes". -/
def GossipTopic.gloas : List GossipTopic :=
  [.executionPayloadBid, .executionPayload, .payloadAttestationMessage, .proposerPreferences]

/-- The topics with a subnet, each with its base name. -/
def GossipTopic.subnetBases : List (String × (SubnetID → GossipTopic)) :=
  [("beacon_attestation", .beaconAttestation), ("sync_committee", .syncCommittee),
    ("blob_sidecar", .blobSidecar), ("data_column_sidecar", .dataColumnSidecar)]

/-- The topic with a name, if one has it. -/
def GossipTopic.ofName? (name : String) : Option GossipTopic :=
  match GossipTopic.global.find? (·.name == name) with
  | some topic => some topic
  | none => GossipTopic.subnetBases.findSome? fun (base, topic) =>
    (Networking.Gossip.parseSubnetTopicName base name).map topic

/-- The number of sync committee subnets. -/
def SYNC_COMMITTEE_SUBNET_COUNT : UInt64 := Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT.toUInt64

/--
The number of blob sidecar subnets: from Deneb, raised at Electra, and none from Fulu on.

Before Deneb and from Fulu on there are no blob sidecar subnets.
-/
def Config.blobSidecarSubnetCount (config : Config) (fork : Fork) : UInt64 :=
  if fork < .dencun ∨ .fusaka ≤ fork then 0
  else if .pectra ≤ fork then config.BLOB_SIDECAR_SUBNET_COUNT_ELECTRA
  else config.BLOB_SIDECAR_SUBNET_COUNT

/-- One topic for each subnet ID below a count, in increasing order. -/
def subnetTopics (count : UInt64) (topic : SubnetID → GossipTopic) : List GossipTopic :=
  (List.range count.toNat).map fun subnet => topic subnet.toUInt64

/--
The gossip topics of a fork, in the order of the fork that adds each one.

A fork before Altair has the topics of Phase 0.

Heze has none yet, since its topics are not yet specified here.
-/
def Config.gossipTopics (config : Config) (fork : Fork) : Option (List GossipTopic) :=
  if .hegota ≤ fork then none
  else some <|
    [.beaconBlock, .beaconAggregateAndProof] ++
    subnetTopics config.ATTESTATION_SUBNET_COUNT .beaconAttestation ++
    [.voluntaryExit, .proposerSlashing, .attesterSlashing] ++
    (if .altair ≤ fork then
      .syncCommitteeContributionAndProof ::
        subnetTopics SYNC_COMMITTEE_SUBNET_COUNT .syncCommittee ++
        [.lightClientFinalityUpdate, .lightClientOptimisticUpdate]
    else []) ++
    (if .shapella ≤ fork then [.blsToExecutionChange] else []) ++
    subnetTopics (config.blobSidecarSubnetCount fork) .blobSidecar ++
    (if .fusaka ≤ fork then
      subnetTopics config.DATA_COLUMN_SIDECAR_SUBNET_COUNT .dataColumnSidecar
    else []) ++
    (if .glamsterdam ≤ fork then GossipTopic.gloas else [])

/--
The subnet of an attestation, from the committees per slot, its slot and its committee index.

The committees before it in its epoch, plus its index, modulo the number of subnets.

A product or a sum of 2^64 or more is an error, as in 64-bit arithmetic.
-/
def computeSubnetForAttestation (preset : Preset) (config : Config)
    (committeesPerSlot : UInt64) (slot : Slot) (committeeIndex : CommitteeIndex) :
    Except (SubnetError ShuffleError) SubnetID := do
  if config.ATTESTATION_SUBNET_COUNT = 0 then throw .zeroSubnetCount
  let slotsSinceEpochStart := slot % preset.SLOTS_PER_EPOCH
  let committees ← (Uint64.mulChecked committeesPerSlot slotsSinceEpochStart).mapError
    fun _ => .subnetOverflow
  let position ← (Uint64.addChecked committees committeeIndex).mapError fun _ => .subnetOverflow
  return position % config.ATTESTATION_SUBNET_COUNT

/--
From Deneb to Electra: the subnet of a blob sidecar, its blob index modulo the number of subnets.

A fork with no blob sidecar subnets has no subnet for it.
-/
def computeSubnetForBlobSidecar (config : Config) (fork : Fork) (blobIndex : BlobIndex) :
    Except (SubnetError ShuffleError) SubnetID := do
  let count := config.blobSidecarSubnetCount fork
  if count = 0 then throw .zeroSubnetCount
  return blobIndex % count

/-- From Fulu: the subnet of a data column sidecar, its column modulo the number of subnets. -/
def computeSubnetForDataColumnSidecar (config : Config) (columnIndex : UInt64) :
    Except (SubnetError ShuffleError) SubnetID := do
  if config.DATA_COLUMN_SIDECAR_SUBNET_COUNT = 0 then throw .zeroSubnetCount
  return columnIndex % config.DATA_COLUMN_SIDECAR_SUBNET_COUNT

/-- The 32 bytes of a SHA-256 digest, as a seed of the shuffle. -/
def seedOfDigest (digest : ByteArray) : Bytes32 :=
  Vector.ofFn fun i => digest[i.val]!

/--
The attestation subnets that a node subscribes to in an epoch.

The swap-or-not shuffle of the preset permutes the prefix of the node ID.
-/
def computeSubscribedSubnets (preset : Preset) (config : Config)
    (nodeId : Networking.Gossip.NodeID) (epoch : Epoch) :
    Except (SubnetError ShuffleError) (List SubnetID) :=
  Networking.Gossip.computeSubscribedSubnets config.toSubnetParameters
    (fun index count seed => computeShuffledIndex preset index count (seedOfDigest seed))
    nodeId epoch

end EthLib.Consensus
