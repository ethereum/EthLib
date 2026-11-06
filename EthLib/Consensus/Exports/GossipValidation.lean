module

public import EthLib.Consensus.Exports.ForkChoice
public import EthLib.Consensus.Gossip.Attestation
public import EthLib.Consensus.Gossip.Block
public import EthLib.Consensus.Gossip.Operations
public import EthLib.Consensus.Gossip.SyncCommittee

/-!
# `Exports.GossipValidation`

A C-ABI export that validates gossip messages of one topic, in turn, against one store.

The store starts from an anchor state and a signed anchor block, given in SSZ.

More signed blocks may follow the anchor, each as two bytes, a 4-byte length and that many bytes.

The first byte marks a block that failed its transition with 1, or a pending block with 2.

The node knows such a block but holds no state after it.

The state after any other block is the state transition of the state of its parent.

The second byte gives the status of the payload of the block, or 255 for none.

An optional 40-byte checkpoint, an epoch and a root, replaces the finalized checkpoint.

A JSON object may replace values of the configuration, and an empty one keeps it.

The messages arrive one after another in one byte string.

Each message is the time of its arrival in milliseconds and a subnet ID, 8 bytes each.

Then come a 4-byte length and that many bytes of SSZ.

A topic that takes no subnet ignores its subnet ID.

The messages share the keys of the messages seen, which each valid message extends.

After each message comes one byte: 0 when it is valid, 1 when it is ignored, 2 when it is rejected.

An ignore or a reject carries a 4-byte length and its reason in UTF-8.

Numbers are little-endian.

An error of the fork choice, such as a head that cannot be computed, fails the whole run.

An input that the export reads itself, such as a wrong length or an unknown topic, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz Networking.Gossip
open EthLib.Exports (Result)
open Serialization.Ssz.Exports (runSsz)

/-- A gossip message of a case: its time of arrival in milliseconds, its subnet and its bytes. -/
structure GossipInput where
  /-- The time of arrival, in milliseconds since the Unix epoch. -/
  currentTimeMs : UInt64
  /-- The subnet ID, for a topic that has subnets. -/
  subnetId : UInt64
  /-- The SSZ bytes of the message. -/
  data : ByteArray

/-- The messages that the bytes hold from an offset.

Each message reads at least 20 bytes, so one round more than the bytes suffices. -/
def readGossipInputs : (rounds : Nat) → ByteArray → Nat → Result (List GossipInput)
  | 0, _, _ => throw (0, "messages do not end")
  | rounds + 1, bytes, offset =>
    if offset = bytes.size then return []
    else if bytes.size < offset + 20 then throw (0, "a message is cut short")
    else do
      let currentTimeMs ← decodeInput UInt64 (bytes.extract offset (offset + 8))
      let subnetId ← decodeInput UInt64 (bytes.extract (offset + 8) (offset + 16))
      let length := (← decodeInput UInt32 (bytes.extract (offset + 16) (offset + 20))).toNat
      let stop := offset + 20 + length
      if bytes.size < stop then throw (0, "the bytes of a message are cut short")
      let rest ← readGossipInputs rounds bytes stop
      return ⟨currentTimeMs, subnetId, bytes.extract (offset + 20) stop⟩ :: rest

/-- The byte of an outcome, then the length and the text of its reason. -/
def outcomeRecord : ValidationResult → ByteArray
  | .accept => ByteArray.empty.push 0
  | .ignore reason => ByteArray.empty.push 1 ++ littleEndian 4 reason.utf8ByteSize ++ reason.toUTF8
  | .reject reason => ByteArray.empty.push 2 ++ littleEndian 4 reason.utf8ByteSize ++ reason.toUTF8

/-- A block that follows the anchor of a case, with what the node knows of it. -/
structure GossipBlockInput where
  /-- 1 for a block that failed its transition, 2 for a pending block, 0 otherwise. -/
  kind : UInt8
  /-- The status of the payload of the block, or 255 for none. -/
  status : UInt8
  /-- The SSZ bytes of the signed block. -/
  data : ByteArray

/-- The blocks that the bytes hold from an offset.

Each block reads at least 6 bytes, so one round more than the bytes suffices. -/
def readGossipBlocks : (rounds : Nat) → ByteArray → Nat → Result (List GossipBlockInput)
  | 0, _, _ => throw (0, "blocks do not end")
  | rounds + 1, bytes, offset =>
    if offset = bytes.size then return []
    else if bytes.size < offset + 6 then throw (0, "a block is cut short")
    else do
      let length := (← decodeInput UInt32 (bytes.extract (offset + 2) (offset + 6))).toNat
      let stop := offset + 6 + length
      if bytes.size < stop then throw (0, "the bytes of a block are cut short")
      let rest ← readGossipBlocks rounds bytes stop
      return ⟨bytes[offset]!, bytes[offset + 1]!, bytes.extract (offset + 6) stop⟩ :: rest

/-- The store and the statuses after a block that follows the anchor.

A failed or a pending block joins the known blocks only.

Another block also gets its state, by the state transition of the state of its parent. -/
def importGossipBlock {preset : Preset} {fork : Fork} (config : Config)
    (checks : SignatureChecks) (store : Store preset fork) (statuses : PayloadStatuses)
    (input : GossipBlockInput) : Result (Store preset fork × PayloadStatuses) := do
  let signed ← decodeInput (SignedBeaconBlock preset fork) input.data
  let root ← runSsz "block rejected" (SszType.hashTreeRoot signed.message)
  let statuses := if input.status = 255 then statuses else statuses.insert root input.status
  let store := { store with blocks := store.blocks.insert root signed.message }
  if input.kind ≠ 0 then return (store, statuses)
  let parentState ← runForkChoice (store.blockState signed.message.parentRoot)
  let state ← runForkChoice
    ((stateTransition config checks (.constant true) parentState signed).mapError .transition)
  return ({ store with blockStates := store.blockStates.insert root state }, statuses)

/-- Whether gossip validation of a topic is specified here at a fork.

The sync committee has topics from Altair, and changes of BLS credentials from Capella. -/
def gossipValidationSpecified (fork : Fork) : String → Bool
  | "attester_slashing" | "proposer_slashing" | "voluntary_exit" | "beacon_block"
  | "beacon_attestation" | "beacon_aggregate_and_proof" => true
  | "sync_committee" | "sync_committee_contribution_and_proof" => .altair ≤ fork
  | "bls_to_execution_change" => .shapella ≤ fork
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
      let outcome ← runForkChoice (validateSingleAttestation config checks seen store electra
        attestation input.currentTimeMs input.subnetId)
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
      (validateAggregateAndProof config checks seen store signed input.currentTimeMs)
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
  | _ => throw (0, s!"gossip validation of the topic {topic} is not yet specified")

/-- Validate the messages of a topic in turn, against the store of an anchor and later blocks.

From Gloas the store is not specified here. -/
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
    store := { store with finalizedCheckpoint := ← decodeInput Checkpoint finalized }
  else if finalized.size ≠ 0 then throw (0, "the finalized checkpoint is not 40 bytes")
  let mut seen : Seen := {}
  let mut out := ByteArray.empty
  for input in ← readGossipInputs (messages.size + 1) messages 0 do
    let (outcome, next) ← validateGossipInput config checks store statuses topic seen input
    seen := next
    out := out ++ outcomeRecord outcome
  return out

end EthLib.Consensus.Exports
