module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.RelayApi

/-!
# `Exports.RelayApi`

C-ABI exports for the Relay API: the bid that a relay serves from a block submission.

At Fulu they also give the list of validators that a relay serves to builders.

An unknown preset or fork, or a malformed key, has code 0.

So does a fork outside Bellatrix to Fulu for the bid, and a fork other than Fulu for the list.

The data API exports read and write the JSON of delivered payloads and received bids.

They also say whether a filter keeps an entry, and sort delivered payloads by value.

An unknown order has code 0.

A submission, a state, a registration or a document that does not decode keeps its SSZ code.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- The SSZ bytes of the bid that a relay serves from a submission, under a key. -/
def relaySubmissionBidOf (args : String × String × ByteArray × Cryptography.Bls.BLSPubkey) :
    Result ByteArray := do
  let (name, fork, data, pubkey) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if range : HasBuilderApi fork then
    let request ← runSsz "input rejected"
      (SszType.deserialize (SubmitBlockRequest preset fork) data)
    let bid ← runSsz "header rejected" (request.bid range pubkey)
    runSsz "value rejected" (SszType.serialize bid)
  else throw (0, s!"no Relay API submissions at {fork.name}")

/-- The SSZ bytes of the bid that a relay serves from a submission, under a key.

The arguments are the name of the preset, the fork, the SSZ bytes of the submission and the key. -/
@[export eth_consensus_relay_submission_bid]
def relaySubmissionBidExport (args : PyValue) : Result PyValue := pyExport relaySubmissionBidOf args

/-- At Fulu only: the list of validators that a relay serves, as a `list` of `dict`. -/
def relayValidatorsOf (args : String × String × ByteArray × List ByteArray) :
    Result PyValue := do
  let (name, fork, state, kept) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  if fulu : .fusaka ≤ fork ∧ fork < .glamsterdam then
    let state ← runSsz "state rejected" (SszType.deserialize (BeaconState preset fork) state)
    let entries ← kept.mapM fun bytes =>
      runSsz "registry rejected" (SszType.deserialize SignedValidatorRegistrationV1 bytes)
    let response := RelayApi.validatorsResponse state fulu.1 ⟨entries⟩
    let documents ← response.mapM fun entry =>
      runSsz "value rejected" (BeaconApi.toApiJson entry)
    return PyValue.ofJson (Lean.Json.arr documents.toArray)
  else throw (0, s!"no Relay API list of validators at {fork.name}")

/-- At Fulu only: the list of validators that a relay serves, as a `list` of `dict`.

The arguments are the name of the preset, the fork, the state and the signed registrations kept.

When two registrations share a key, the first one counts.

The list covers the current and next epoch of the state, by its lookahead of proposers.

So the state must first be advanced to the current slot of the relay. -/
@[export eth_consensus_relay_validators]
def relayValidatorsExport (args : PyValue) : Result PyValue := pyExport relayValidatorsOf args

/-! ## The data API -/

/-- A delivered payload, read from its JSON and written back. -/
def relayDeliveredPayloadOf (document : PyValue) : Result PyValue := do
  let entry ← runSsz "document rejected"
    (BeaconApi.ofApiJson RelayApi.BidTraceV2 document.toJson)
  return PyValue.ofJson (← runSsz "value rejected" (BeaconApi.toApiJson entry))

/-- A delivered payload, read from its JSON and written back as a `dict`.

The argument is the JSON object, as a `dict`. -/
@[export eth_consensus_relay_delivered_payload]
def relayDeliveredPayloadExport (args : PyValue) : Result PyValue :=
  pyExport relayDeliveredPayloadOf args

/-- A received bid, read from its JSON and written back. -/
def relayReceivedBidOf (document : PyValue) : Result PyValue := do
  let entry ← runSsz "document rejected" (RelayApi.BidTraceV2WithTimestamp.ofJson document.toJson)
  return PyValue.ofJson (← runSsz "value rejected" entry.toJson)

/-- A received bid, read from its JSON and written back as a `dict`.

The argument is the JSON object, as a `dict`. -/
@[export eth_consensus_relay_received_bid]
def relayReceivedBidExport (args : PyValue) : Result PyValue := pyExport relayReceivedBidOf args

/-- Whether the filters of a query of delivered payloads keep the payload of a JSON object. -/
def relayDeliveredKeepsOf (args : PyValue × Option Slot × Option Hash32 × Option UInt64 ×
    Option Cryptography.Bls.BLSPubkey × Option Cryptography.Bls.BLSPubkey) : Result Bool := do
  let (document, slot, blockHash, blockNumber, proposerPubkey, builderPubkey) := args
  let entry ← runSsz "document rejected"
    (BeaconApi.ofApiJson RelayApi.BidTraceV2 document.toJson)
  return RelayApi.DeliveredFilter.keeps
    { slot, blockHash, blockNumber, proposerPubkey, builderPubkey } entry

/-- Whether the filters of a query of delivered payloads keep the payload of a JSON object.

The arguments are the object, then the slot, the block hash and the block number.

The keys of the proposer and of the builder follow; each filter is `None` when absent. -/
@[export eth_consensus_relay_delivered_keeps]
def relayDeliveredKeepsExport (args : PyValue) : Result PyValue :=
  pyExport relayDeliveredKeepsOf args

/-- Whether the filters of a query of received bids keep the bid of a JSON object. -/
def relayReceivedKeepsOf (args : PyValue × Option Slot × Option Hash32 × Option UInt64 ×
    Option Cryptography.Bls.BLSPubkey) : Result Bool := do
  let (document, slot, blockHash, blockNumber, builderPubkey) := args
  let entry ← runSsz "document rejected"
    (RelayApi.BidTraceV2WithTimestamp.ofJson document.toJson)
  return RelayApi.ReceivedFilter.keeps { slot, blockHash, blockNumber, builderPubkey } entry

/-- Whether the filters of a query of received bids keep the bid of a JSON object.

The arguments are the object, then the slot, the block hash, the block number and the builder key.

Each filter is `None` when absent. -/
@[export eth_consensus_relay_received_keeps]
def relayReceivedKeepsExport (args : PyValue) : Result PyValue := pyExport relayReceivedKeepsOf args

/-- Delivered payloads, read from their JSON, sorted by value in an order and written back. -/
def relaySortDeliveredOf (args : String × List PyValue) : Result PyValue := do
  let (name, documents) := args
  let some order := RelayApi.OrderBy.ofName? name | throw (0, s!"unknown order {name}")
  let entries ← documents.mapM fun document =>
    runSsz "document rejected" (BeaconApi.ofApiJson RelayApi.BidTraceV2 document.toJson)
  let written ← (RelayApi.sortBy order entries).mapM fun entry =>
    runSsz "value rejected" (BeaconApi.toApiJson entry)
  return PyValue.ofJson (Lean.Json.arr written.toArray)

/-- Delivered payloads sorted by value in the given order, as a `list` of `dict`.

The arguments are the order, `value` or `-value`, and the JSON objects of the payloads. -/
@[export eth_consensus_relay_sort_delivered]
def relaySortDeliveredExport (args : PyValue) : Result PyValue := pyExport relaySortDeliveredOf args

end EthLib.Consensus.Exports
