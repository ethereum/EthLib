module

public import EthLib.Consensus.Gossip.Attestation
public import EthLib.Consensus.Gossip.Bid
public import EthLib.Consensus.Gossip.Block
public import EthLib.Consensus.Gossip.InclusionList
public import EthLib.Consensus.Gossip.Operations
public import EthLib.Consensus.Gossip.Payload
public import EthLib.Consensus.Gossip.ProposerPreferences
public import EthLib.Consensus.Gossip.Sidecar
public import EthLib.Consensus.Gossip.SyncCommittee

/-!
# `Consensus.Gossip.Message`

One decoded gossip message of any topic, and its validation by the rules of its topic.

A message with a subnet carries it, and a topic of a later fork carries the proof of that fork.

One dispatch picks the validator of the topic, and only a valid message adds its keys.

The light client updates and the partial column sidecars keep their own state, so they stay out.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Networking.Gossip Cryptography.Kzg

/-- A decoded gossip message, with the subnet it travels on when its topic has subnets. -/
inductive GossipMessage (preset : Preset) (fork : Fork) where
  /-- An attester slashing. -/
  | attesterSlashing (slashing : AttesterSlashing preset fork)
  /-- A proposer slashing. -/
  | proposerSlashing (slashing : ProposerSlashing)
  /-- A signed voluntary exit. -/
  | voluntaryExit (signed : SignedVoluntaryExit)
  /-- From Capella: a signed change of withdrawal credentials to an execution address. -/
  | blsToExecutionChange (capella : .shapella ≤ fork) (signed : SignedBLSToExecutionChange)
  /-- A signed beacon block. -/
  | beaconBlock (signed : SignedBeaconBlock preset fork)
  /-- Before Electra: an unaggregated attestation, on an attestation subnet. -/
  | beaconAttestation (early : fork < .pectra) (attestation : Attestation preset fork)
    (subnetId : UInt64)
  /-- From Electra: a single attestation, on an attestation subnet. -/
  | singleAttestation (electra : .pectra ≤ fork) (attestation : SingleAttestation)
    (subnetId : UInt64)
  /-- A signed aggregate of attestations, with the proof that its sender aggregates. -/
  | aggregateAndProof (signed : SignedAggregateAndProof preset fork)
  /-- From Altair: a sync committee message, on a sync committee subnet. -/
  | syncCommitteeMessage (altair : .altair ≤ fork) (message : SyncCommitteeMessage)
    (subnetId : UInt64)
  /-- From Altair: a signed contribution of a sync subcommittee, with its aggregation proof. -/
  | contributionAndProof (altair : .altair ≤ fork) (signed : SignedContributionAndProof preset)
  /-- At Deneb and Electra: a blob sidecar, on a blob subnet. -/
  | blobSidecar (blobs : .dencun ≤ fork ∧ fork < .fusaka) (sidecar : BlobSidecar preset)
    (subnetId : UInt64)
  /-- From Fulu: a data column sidecar, on a column subnet. -/
  | dataColumnSidecar (fulu : .fusaka ≤ fork) (sidecar : DataColumnSidecar preset fork)
    (subnetId : UInt64)
  /-- From Gloas: the signed preferences of a proposer. -/
  | proposerPreferences (gloas : .glamsterdam ≤ fork) (signed : SignedProposerPreferences)
  /-- From Gloas: a signed envelope that reveals the payload of a block. -/
  | executionPayloadEnvelope (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork)
  /-- From Gloas: a vote of the payload timeliness committee. -/
  | payloadAttestationMessage (gloas : .glamsterdam ≤ fork) (message : PayloadAttestationMessage)
  /-- From Gloas: a signed bid of a builder. -/
  | executionPayloadBid (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork)
  /-- From Heze: a signed inclusion list. -/
  | inclusionList (heze : .hegota ≤ fork) (signed : SignedInclusionList)

namespace GossipMessage

variable {preset : Preset} {fork : Fork}

/-- The outcome of a message by the rules of its topic, at a time in milliseconds.

The KZG setup checks the proofs of a blob or column sidecar.

The statuses of payloads check the blocks and the votes that name a payload. -/
def validate (config : Config) (checks : SignatureChecks) (setup : TrustedSetup) (seen : Seen)
    (store : Store preset fork) (statuses : PayloadStatuses) (currentTimeMs : UInt64) :
    GossipMessage preset fork → Except ForkChoiceError ValidationResult
  | .attesterSlashing slashing => validateAttesterSlashing config checks seen store slashing
  | .proposerSlashing slashing => validateProposerSlashing config checks seen store slashing
  | .voluntaryExit signed => validateVoluntaryExit config checks seen store signed currentTimeMs
  | .blsToExecutionChange _ signed =>
    validateBlsToExecutionChange config checks seen store signed currentTimeMs
  | .beaconBlock signed =>
    validateBeaconBlock config checks seen store statuses signed currentTimeMs
  | .beaconAttestation early attestation subnetId =>
    validateBeaconAttestation config checks seen store early attestation currentTimeMs subnetId
  | .singleAttestation electra attestation subnetId =>
    validateSingleAttestation config checks seen store statuses electra attestation currentTimeMs
      subnetId
  | .aggregateAndProof signed =>
    validateAggregateAndProof config checks seen store statuses signed currentTimeMs
  | .syncCommitteeMessage altair message subnetId =>
    validateSyncCommitteeMessage config checks seen store altair message currentTimeMs subnetId
  | .contributionAndProof altair signed =>
    validateContributionAndProof config checks seen store altair signed currentTimeMs
  | .blobSidecar blobs sidecar subnetId =>
    validateBlobSidecar config checks setup seen store blobs sidecar currentTimeMs subnetId
  | .dataColumnSidecar fulu sidecar subnetId =>
    if gloas : .glamsterdam ≤ fork then
      validateGloasDataColumnSidecar config setup seen store gloas sidecar currentTimeMs subnetId
    else
      validateDataColumnSidecar config checks setup seen store ⟨fulu, Nat.lt_of_not_le gloas⟩
        sidecar currentTimeMs subnetId
  | .proposerPreferences gloas signed =>
    validateProposerPreferences config checks seen store gloas signed currentTimeMs
  | .executionPayloadEnvelope gloas signed =>
    validateExecutionPayloadEnvelope config checks seen store gloas signed
  | .payloadAttestationMessage gloas message =>
    validatePayloadAttestationMessage config checks seen store gloas message currentTimeMs
  | .executionPayloadBid gloas signed =>
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs
  | .inclusionList _ signed => validateInclusionList config checks seen store signed currentTimeMs

/-- The messages seen after a valid message, which hold its keys too.

Before Electra the key of an attestation names its attester, the member whose bit is set.

The key of an aggregate holds the root of its data. -/
def record (config : Config) (store : Store preset fork) (seen : Seen) :
    GossipMessage preset fork → Except ForkChoiceError Seen
  | .attesterSlashing slashing => return seen.recordAttesterSlashing slashing
  | .proposerSlashing slashing => return seen.recordProposerSlashing slashing
  | .voluntaryExit signed => return seen.recordVoluntaryExit signed
  | .blsToExecutionChange _ signed => return seen.recordBlsToExecutionChange signed
  | .beaconBlock signed => return seen.recordBeaconBlock signed
  | .beaconAttestation _ attestation _ => do
    -- A valid attestation sets one bit, so it has an attester, and this error never occurs.
    let some attester ← beaconAttestationAttester config store attestation
      | throw (.accessor (.bitOutOfRange attestation.aggregationBits.bits.size))
    return seen.recordAttestation attestation.data.target.epoch attester
  | .singleAttestation _ attestation _ =>
    return seen.recordAttestation attestation.data.target.epoch attestation.attesterIndex
  | .aggregateAndProof signed => do
    let root ← (Serialization.Ssz.SszType.hashTreeRoot signed.message.aggregate.data).mapError
      .ssz
    return seen.recordAggregateAndProof signed root
  | .syncCommitteeMessage _ message subnetId =>
    return seen.recordSyncCommitteeMessage message subnetId
  | .contributionAndProof _ signed => return seen.recordContributionAndProof signed
  | .blobSidecar _ sidecar _ => return seen.recordBlobSidecar sidecar
  | .dataColumnSidecar _ sidecar _ =>
    if gloas : .glamsterdam ≤ fork then return seen.recordGloasDataColumnSidecar gloas sidecar
    else return seen.recordDataColumnSidecar (Nat.lt_of_not_le gloas) sidecar
  | .proposerPreferences _ signed => return seen.recordProposerPreferences signed
  | .executionPayloadEnvelope _ signed => return seen.recordExecutionPayloadEnvelope signed
  | .payloadAttestationMessage _ message => return seen.recordPayloadAttestationMessage message
  | .executionPayloadBid _ signed => return seen.recordExecutionPayloadBid signed
  | .inclusionList _ signed => return seen.recordInclusionList signed

end GossipMessage

/-- The outcome of a gossip message by the rules of its topic, and the messages seen after it.

Only a valid message adds its keys to the messages seen. -/
def validateGossipMessage {preset : Preset} {fork : Fork} (config : Config)
    (checks : SignatureChecks) (setup : TrustedSetup) (seen : Seen) (store : Store preset fork)
    (statuses : PayloadStatuses) (currentTimeMs : UInt64) (message : GossipMessage preset fork) :
    Except ForkChoiceError (ValidationResult × Seen) := do
  let outcome ← message.validate config checks setup seen store statuses currentTimeMs
  if outcome.isAccept then return (outcome, ← message.record config store seen)
  else return (outcome, seen)

end EthLib.Consensus
