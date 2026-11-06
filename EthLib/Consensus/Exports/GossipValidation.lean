module

public import EthLib.Consensus.Exports.ForkChoice
public import EthLib.Consensus.Gossip.Operations

/-!
# `Exports.GossipValidation`

A C-ABI export that validates gossip messages of one topic, in turn, against one store.

The store starts from an anchor state and a signed anchor block, given in SSZ.

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

/-- Whether gossip validation of a topic is specified here at a fork.

Changes of BLS credentials have a topic from Capella. -/
def gossipValidationSpecified (fork : Fork) : String → Bool
  | "attester_slashing" | "proposer_slashing" | "voluntary_exit" => true
  | "bls_to_execution_change" => .shapella ≤ fork
  | _ => false

/-- The outcome of one message of a topic, and the keys seen after it.

The keys change only when the message is valid. -/
def validateGossipInput {preset : Preset} {fork : Fork} (config : Config)
    (checks : SignatureChecks) (store : Store preset fork) (topic : String) (seen : Seen)
    (input : GossipInput) : Result (ValidationResult × Seen) := do
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
  | _ => throw (0, s!"gossip validation of the topic {topic} is not yet specified")

/-- Validate the messages of a topic in turn, against the store of an anchor.

From Gloas the store is not specified here. -/
@[export eth_consensus_gossip_validation]
def gossipValidationExport
    (name fork anchorState anchorBlock topic messages replacements : ByteArray) (verify : Bool) :
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
  let store ← runForkChoice (getForkchoiceStore config anchorState anchorBlock.message)
  let mut seen : Seen := {}
  let mut out := ByteArray.empty
  for input in ← readGossipInputs (messages.size + 1) messages 0 do
    let (outcome, next) ← validateGossipInput config checks store topic seen input
    seen := next
    out := out ++ outcomeRecord outcome
  return out

end EthLib.Consensus.Exports
