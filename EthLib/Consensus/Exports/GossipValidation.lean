module

public import EthLib.Consensus.Exports.ForkChoice
public import EthLib.Cryptography.Exports.Kzg
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
# `Exports.GossipValidation`

A C-ABI export that validates gossip messages of one topic, in turn, against one store.

The store starts from an anchor state and a signed anchor block, given in SSZ.

More signed blocks may follow the anchor, each as two bytes, a 4-byte length and that many bytes.

The first byte marks a block that failed its transition with 1, or a pending block with 2.

The node knows such a block but holds no state after it.

A first byte of 3 gives a block that the store holds already, such as the anchor, for its envelope.

The state after any other block is the state transition of the state of its parent.

The second byte gives the status of the payload of the block, or 255 for none.

From Gloas a block may come with the signed envelope of its payload, which the store then keeps.

It follows the block as a 4-byte length and that many bytes, and a length of 0 means no envelope.

An optional 40-byte checkpoint, an epoch and a root, replaces the finalized checkpoint.

It replaces it in the store and in the state after each block, wherever the rules read it.

A JSON object may replace values of the configuration, and an empty one keeps it.

The messages arrive one after another in one byte string.

Each message is the time of its arrival in milliseconds and a subnet ID, 8 bytes each.

Then comes the topic of the message, as one byte of length and that many bytes of UTF-8.

An empty topic is the topic of the case, and another topic must be specified at the fork too.

Then come a 4-byte length and that many bytes of SSZ.

A topic that takes no subnet ignores its subnet ID.

The messages share the keys of the messages seen, which each valid message extends.

After each message comes one byte: 0 when it is valid, 1 when it is ignored, 2 when it is rejected.

An ignore or a reject carries a 4-byte length and its reason in UTF-8.

Numbers are little-endian.

From Heze a valid inclusion list also joins the inclusion lists of the store, as timely.

An error of the fork choice, such as a head that cannot be computed, fails the whole run.

An input that the export reads itself, such as a wrong length or an unknown topic, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz Networking.Gossip
open EthLib.Exports (Result)
open Serialization.Ssz.Exports (runSsz)
open Cryptography.Kzg.Exports (embeddedSetup)

/-- A gossip message of a case: its time of arrival in ms, its subnet, its topic and its bytes. -/
structure GossipInput where
  /-- The time of arrival, in milliseconds since the Unix epoch. -/
  currentTimeMs : UInt64
  /-- The subnet ID, for a topic that has subnets. -/
  subnetId : UInt64
  /-- The topic of the message, or the empty string for the topic of the case. -/
  topic : String
  /-- The SSZ bytes of the message. -/
  data : ByteArray

/-- The messages that the bytes hold from an offset.

Each message reads at least 21 bytes, so one round more than the bytes suffices. -/
def readGossipInputs : (rounds : Nat) → ByteArray → Nat → Result (List GossipInput)
  | 0, _, _ => throw (0, "messages do not end")
  | rounds + 1, bytes, offset =>
    if offset = bytes.size then return []
    else if short : bytes.size < offset + 21 then throw (0, "a message is cut short")
    else do
      let currentTimeMs ← decodeInput UInt64 (bytes.extract offset (offset + 8))
      let subnetId ← decodeInput UInt64 (bytes.extract (offset + 8) (offset + 16))
      let named := offset + 17 + (bytes[offset + 16]'(by omega)).toNat
      if bytes.size < named + 4 then throw (0, "the topic of a message is cut short")
      let some topic := String.fromUTF8? (bytes.extract (offset + 17) named)
        | throw (0, "the topic of a message is not UTF-8")
      let length := (← decodeInput UInt32 (bytes.extract named (named + 4))).toNat
      let stop := named + 4 + length
      if bytes.size < stop then throw (0, "the bytes of a message are cut short")
      let rest ← readGossipInputs rounds bytes stop
      return ⟨currentTimeMs, subnetId, topic, bytes.extract (named + 4) stop⟩ :: rest

/-- The byte of an outcome, then the length and the text of its reason. -/
def outcomeRecord : ValidationResult → ByteArray
  | .accept => ByteArray.empty.push 0
  | .ignore reason => ByteArray.empty.push 1 ++ littleEndian 4 reason.utf8ByteSize ++ reason.toUTF8
  | .reject reason => ByteArray.empty.push 2 ++ littleEndian 4 reason.utf8ByteSize ++ reason.toUTF8

/-- A block that follows the anchor of a case, with what the node knows of it. -/
structure GossipBlockInput where
  /-- 1 for a failed block, 2 for a pending block, 3 for a block already held, 0 otherwise. -/
  kind : UInt8
  /-- The status of the payload of the block, or 255 for none. -/
  status : UInt8
  /-- The SSZ bytes of the signed block. -/
  data : ByteArray
  /-- The SSZ bytes of the signed envelope of its payload, or none when empty. -/
  envelope : ByteArray

/-- The blocks that the bytes hold from an offset.

Each block reads at least 10 bytes, so one round more than the bytes suffices. -/
def readGossipBlocks : (rounds : Nat) → ByteArray → Nat → Result (List GossipBlockInput)
  | 0, _, _ => throw (0, "blocks do not end")
  | rounds + 1, bytes, offset =>
    if offset = bytes.size then return []
    else if short : bytes.size < offset + 6 then throw (0, "a block is cut short")
    else do
      let length := (← decodeInput UInt32 (bytes.extract (offset + 2) (offset + 6))).toNat
      let stop := offset + 6 + length
      if bytes.size < stop + 4 then throw (0, "the bytes of a block are cut short")
      let envelopeLength := (← decodeInput UInt32 (bytes.extract stop (stop + 4))).toNat
      let next := stop + 4 + envelopeLength
      if bytes.size < next then throw (0, "the bytes of an envelope are cut short")
      let rest ← readGossipBlocks rounds bytes next
      return ⟨bytes[offset]'(by omega), bytes[offset + 1]'(by omega),
        bytes.extract (offset + 6) stop, bytes.extract (stop + 4) next⟩ :: rest

/-- The store with the envelope of the payload of a block, from Gloas, when there is one.

The envelope was verified when it arrived, so the store keeps it by the root of the block.

From Heze the execution layer answers that the payload satisfied its inclusion lists. -/
def importGossipEnvelope {preset : Preset} {fork : Fork} (store : Store preset fork)
    (root : Root) (bytes : ByteArray) : Result (Store preset fork) := do
  if bytes.isEmpty then return store
  if gloas : .glamsterdam ≤ fork then
    let signed ← decodeInput (SignedExecutionPayloadEnvelope preset fork) bytes
    let payloads := (store.payloads gloas).insert root signed.message
    let store := { store with payloads := fun _ => payloads }
    if heze : .hegota ≤ fork then
      let satisfaction := (store.payloadInclusionListSatisfaction heze).insert root true
      return { store with payloadInclusionListSatisfaction := fun _ => satisfaction }
    else return store
  else throw (0, "a block has the envelope of a payload only from Gloas")

/-- The store and the statuses after a block that follows the anchor.

A failed or a pending block joins the known blocks only, and a block already held stays as it is.

Another block also gets its state, by the state transition of the state of its parent.

From Gloas the store also keeps the envelope of its payload, when there is one.

From Gloas a block with a state starts with no vote of the payload committee. -/
def importGossipBlock {preset : Preset} {fork : Fork} (config : Config)
    (checks : SignatureChecks) (store : Store preset fork) (statuses : PayloadStatuses)
    (input : GossipBlockInput) : Result (Store preset fork × PayloadStatuses) := do
  let signed ← decodeInput (SignedBeaconBlock preset fork) input.data
  let root ← runSsz "block rejected" (SszType.hashTreeRoot signed.message)
  let statuses := if input.status = 255 then statuses else statuses.insert root input.status
  let store := { store with blocks := store.blocks.insert root signed.message }
  let store ← importGossipEnvelope store root input.envelope
  if input.kind ≠ 0 then return (store, statuses)
  let parentState ← runForkChoice (store.blockState signed.message.parentRoot)
  let state ← runForkChoice
    ((stateTransition config checks (.constant true) parentState signed).mapError .transition)
  let store := { store with blockStates := store.blockStates.insert root state }
  if gloas : .glamsterdam ≤ fork then
    let noVotes := Vector.replicate preset.PTC_SIZE.toNat none
    let timeliness := (store.payloadTimelinessVote gloas).insert root noVotes
    let availability := (store.payloadDataAvailabilityVote gloas).insert root noVotes
    return ({ store with
      payloadTimelinessVote := fun _ => timeliness
      payloadDataAvailabilityVote := fun _ => availability }, statuses)
  else return (store, statuses)

/-- Whether gossip validation of a topic is specified here at a fork.

The sync committee has topics from Altair, and changes of BLS credentials from Capella.

Blob sidecars travel at Deneb and Electra, and column sidecars from Fulu on.

Gloas adds four topics, and Heze adds inclusion lists. -/
def gossipValidationSpecified (fork : Fork) : String → Bool
  | "attester_slashing" | "proposer_slashing" | "voluntary_exit" | "beacon_block"
  | "beacon_attestation" | "beacon_aggregate_and_proof" => true
  | "sync_committee" | "sync_committee_contribution_and_proof" => .altair ≤ fork
  | "bls_to_execution_change" => .shapella ≤ fork
  | "blob_sidecar" => .dencun ≤ fork && fork < .fusaka
  | "data_column_sidecar" | "partial_data_column_sidecar" => .fusaka ≤ fork
  | "proposer_preferences" | "execution_payload" | "payload_attestation_message"
  | "execution_payload_bid" => .glamsterdam ≤ fork
  | "inclusion_list" => .hegota ≤ fork
  | _ => false

/-- The outcome of one message of a topic, and the keys seen after it.

The keys change only when the message is valid. -/
def validateGossipInput {preset : Preset} {fork : Fork} (config : Config)
    (checks : SignatureChecks) (store : Store preset fork) (statuses : PayloadStatuses)
    (topic : String) (seen : Seen) (input : GossipInput) : Result (ValidationResult × Seen) := do
  let record (outcome : ValidationResult) (update : Seen → Seen) :=
    (outcome, if outcome.isAccept then update seen else seen)
  match topic with
  | "attester_slashing" =>
    let slashing ← decodeInput (AttesterSlashing preset fork) input.data
    let outcome ← runForkChoice (validateAttesterSlashing config checks seen store slashing)
    return record outcome (·.recordAttesterSlashing slashing)
  | "proposer_slashing" =>
    let slashing ← decodeInput ProposerSlashing input.data
    let outcome ← runForkChoice (validateProposerSlashing config checks seen store slashing)
    return record outcome (·.recordProposerSlashing slashing)
  | "voluntary_exit" =>
    let signed ← decodeInput SignedVoluntaryExit input.data
    let outcome ← runForkChoice
      (validateVoluntaryExit config checks seen store signed input.currentTimeMs)
    return record outcome (·.recordVoluntaryExit signed)
  | "bls_to_execution_change" =>
    let signed ← decodeInput SignedBLSToExecutionChange input.data
    let outcome ← runForkChoice
      (validateBlsToExecutionChange config checks seen store signed input.currentTimeMs)
    return record outcome (·.recordBlsToExecutionChange signed)
  | "beacon_block" =>
    let signed ← decodeInput (SignedBeaconBlock preset fork) input.data
    let outcome ← runForkChoice
      (validateBeaconBlock config checks seen store statuses signed input.currentTimeMs)
    return record outcome (·.recordBeaconBlock signed)
  | "beacon_attestation" =>
    if electra : .pectra ≤ fork then
      let attestation ← decodeInput SingleAttestation input.data
      let outcome ← runForkChoice (validateSingleAttestation config checks seen store statuses
        electra attestation input.currentTimeMs input.subnetId)
      return record outcome
        (·.recordAttestation attestation.data.target.epoch attestation.attesterIndex)
    else
      let attestation ← decodeInput (Attestation preset fork) input.data
      let outcome ← runForkChoice (validateBeaconAttestation config checks seen store
        (Nat.lt_of_not_le electra) attestation input.currentTimeMs input.subnetId)
      if !outcome.isAccept then return (outcome, seen)
      -- A valid attestation sets one bit, so it has an attester.
      let some attester ← runForkChoice (beaconAttestationAttester config store attestation)
        | throw (0, "a valid attestation has no attester")
      return (outcome, seen.recordAttestation attestation.data.target.epoch attester)
  | "beacon_aggregate_and_proof" =>
    let signed ← decodeInput (SignedAggregateAndProof preset fork) input.data
    let outcome ← runForkChoice
      (validateAggregateAndProof config checks seen store statuses signed input.currentTimeMs)
    if !outcome.isAccept then return (outcome, seen)
    let root ← runSsz "aggregate rejected" (SszType.hashTreeRoot signed.message.aggregate.data)
    return (outcome, seen.recordAggregateAndProof signed root)
  | "sync_committee" =>
    let message ← decodeInput SyncCommitteeMessage input.data
    if altair : .altair ≤ fork then
      let outcome ← runForkChoice (validateSyncCommitteeMessage config checks seen store altair
        message input.currentTimeMs input.subnetId)
      return record outcome (·.recordSyncCommitteeMessage message input.subnetId)
    else throw (0, "the sync committee has no topic before Altair")
  | "sync_committee_contribution_and_proof" =>
    let signed ← decodeInput (SignedContributionAndProof preset) input.data
    if altair : .altair ≤ fork then
      let outcome ← runForkChoice
        (validateContributionAndProof config checks seen store altair signed input.currentTimeMs)
      return record outcome (·.recordContributionAndProof signed)
    else throw (0, "the sync committee has no topic before Altair")
  | "blob_sidecar" =>
    let sidecar ← decodeInput (BlobSidecar preset) input.data
    if blobs : .dencun ≤ fork ∧ fork < .fusaka then
      let setup ← runForkChoice (embeddedSetup.mapError .kzg)
      let outcome ← runForkChoice (validateBlobSidecar config checks setup seen store blobs sidecar
        input.currentTimeMs input.subnetId)
      return record outcome (·.recordBlobSidecar sidecar)
    else throw (0, "blob sidecars travel only at Deneb and Electra")
  | "data_column_sidecar" =>
    let sidecar ← decodeInput (DataColumnSidecar preset fork) input.data
    if gloas : .glamsterdam ≤ fork then
      let setup ← runForkChoice (embeddedSetup.mapError .kzg)
      let outcome ← runForkChoice (validateGloasDataColumnSidecar config setup seen store gloas
        sidecar input.currentTimeMs input.subnetId)
      return record outcome (·.recordGloasDataColumnSidecar gloas sidecar)
    else if columns : .fusaka ≤ fork ∧ fork < .glamsterdam then
      let setup ← runForkChoice (embeddedSetup.mapError .kzg)
      let outcome ← runForkChoice (validateDataColumnSidecar config checks setup seen store columns
        sidecar input.currentTimeMs input.subnetId)
      return record outcome (·.recordDataColumnSidecar columns.2 sidecar)
    else throw (0, "column sidecars travel only from Fulu")
  | "proposer_preferences" =>
    let signed ← decodeInput SignedProposerPreferences input.data
    if gloas : .glamsterdam ≤ fork then
      let outcome ← runForkChoice (validateProposerPreferences config checks seen store gloas
        signed input.currentTimeMs)
      return record outcome (·.recordProposerPreferences signed)
    else throw (0, "the preferences of proposers travel only from Gloas")
  | "execution_payload" =>
    let signed ← decodeInput (SignedExecutionPayloadEnvelope preset fork) input.data
    if gloas : .glamsterdam ≤ fork then
      let outcome ← runForkChoice
        (validateExecutionPayloadEnvelope config checks seen store gloas signed)
      return record outcome (·.recordExecutionPayloadEnvelope signed)
    else throw (0, "the envelopes of payloads travel only from Gloas")
  | "payload_attestation_message" =>
    let message ← decodeInput PayloadAttestationMessage input.data
    if gloas : .glamsterdam ≤ fork then
      let outcome ← runForkChoice (validatePayloadAttestationMessage config checks seen store
        gloas message input.currentTimeMs)
      return record outcome (·.recordPayloadAttestationMessage message)
    else throw (0, "the votes on payloads travel only from Gloas")
  | "execution_payload_bid" =>
    let signed ← decodeInput (SignedExecutionPayloadBid preset fork) input.data
    if gloas : .glamsterdam ≤ fork then
      let outcome ← runForkChoice (validateExecutionPayloadBid config checks seen store gloas
        signed input.currentTimeMs)
      return record outcome (·.recordExecutionPayloadBid signed)
    else throw (0, "the bids of builders travel only from Gloas")
  | "inclusion_list" =>
    let signed ← decodeInput SignedInclusionList input.data
    let outcome ← runForkChoice
      (validateInclusionList config checks seen store signed input.currentTimeMs)
    return record outcome (·.recordInclusionList signed)
  | _ => throw (0, s!"gossip validation of the topic {topic} is not yet specified")

/-- From Fulu: the outcomes of the partial sidecars of a case, after the headers it records first.

The bytes of a message start with a kind byte, then the group of the message.

The group holds the root of a block, and from Gloas also its slot.

Kind 1 is a header that the node validated before the case, and gives no outcome.

Kind 0 is a partial sidecar, whose column is the subnet field of the message.

At Fulu a sidecar is checked against the recorded headers, and from Gloas against its block. -/
def validatePartialInputs {preset : Preset} {fork : Fork} (config : Config)
    (checks : SignatureChecks) (store : Store preset fork) (inputs : List GossipInput) :
    Result ByteArray := do
  if fulu : .fusaka ≤ fork then
    let setup ← runForkChoice (embeddedSetup.mapError .kzg)
    let groupEnd := if .glamsterdam ≤ fork then 41 else 33
    let mut headers : PartialHeaders preset fork := []
    let mut out := ByteArray.empty
    for input in inputs do
      if input.data.size < groupEnd then throw (0, "a partial message is cut short")
      let group ← decodeInput (PartialDataColumnGroupID fork) (input.data.extract 1 groupEnd)
      let rest := input.data.extract groupEnd input.data.size
      match (input.data.data[0]? : Option UInt8) with
      | some 1 =>
        headers := headers.record group.beaconBlockRoot
          (← decodeInput (PartialDataColumnHeader preset fork) rest)
      | some 0 =>
        let sidecar ← decodeInput (PartialDataColumnSidecar preset fork) rest
        if gloas : .glamsterdam ≤ fork then
          let outcome ← runForkChoice (validateGloasPartialDataColumnSidecar setup store gloas
            sidecar group input.subnetId)
          out := out ++ outcomeRecord outcome
        else
          let (outcome, next) ← runForkChoice (validatePartialDataColumnSidecar config checks
            setup headers store ⟨fulu, Nat.lt_of_not_le gloas⟩ sidecar input.currentTimeMs group
            input.subnetId)
          headers := next
          out := out ++ outcomeRecord outcome
      | _ => throw (0, "the kind of a partial message is 0 or 1")
    return out
  else throw (0, "partial column sidecars travel only from Fulu")

/-- From Heze: the store after a message, which keeps a valid inclusion list as timely.

The node passes a valid list to its fork choice, which the bids of later messages read.

A list that arrives on gossip in its slot counts as timely, as the cases assume.

Any other message leaves the store as it is. -/
def recordGossipInclusionList {preset : Preset} {fork : Fork} (store : Store preset fork)
    (topic : String) (outcome : ValidationResult) (input : GossipInput) :
    Result (Store preset fork) := do
  if heze : .hegota ≤ fork then
    if topic = "inclusion_list" ∧ outcome.isAccept then
      let signed ← decodeInput SignedInclusionList input.data
      let lists := (store.inclusionLists heze).process signed true
      return { store with inclusionLists := fun _ => lists }
  return store

/-- Validate the messages of a topic in turn, against the store of an anchor and later blocks.

Every topic is specified here up to Heze. -/
@[export eth_consensus_gossip_validation]
def gossipValidationExport
    (name fork anchorState anchorBlock blocks finalized topic messages replacements : ByteArray)
    (verify : Bool) :
    Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let some topic := String.fromUTF8? topic | throw (0, "the topic is not UTF-8")
  unless gossipValidationSpecified fork topic do
    throw (0, s!"gossip validation of the topic {topic} at {fork.name} is not yet specified")
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (SignedBeaconBlock preset fork) anchorBlock
  let mut store ← runForkChoice (getForkchoiceStore config anchorState anchorBlock.message)
  let mut statuses : PayloadStatuses := {}
  for input in ← readGossipBlocks (blocks.size + 1) blocks 0 do
    (store, statuses) ← importGossipBlock config checks store statuses input
  if finalized.size = 40 then
    let checkpoint ← decodeInput Checkpoint finalized
    let blockStates := store.blockStates.map fun _ state =>
      { state with finalizedCheckpoint := checkpoint }
    store := { store with finalizedCheckpoint := checkpoint, blockStates }
  else if finalized.size ≠ 0 then throw (0, "the finalized checkpoint is not 40 bytes")
  let inputs ← readGossipInputs (messages.size + 1) messages 0
  if topic = "partial_data_column_sidecar" then
    return ← validatePartialInputs config checks store inputs
  let mut seen : Seen := {}
  let mut out := ByteArray.empty
  for input in inputs do
    let messageTopic := if input.topic.isEmpty then topic else input.topic
    unless gossipValidationSpecified fork messageTopic do
      throw (0, s!"gossip validation of the topic {messageTopic} at {fork.name} is not yet \
        specified")
    let (outcome, next) ←
      validateGossipInput config checks store statuses messageTopic seen input
    seen := next
    out := out ++ outcomeRecord outcome
    store ← recordGossipInclusionList store messageTopic outcome input
  return out

end EthLib.Consensus.Exports
