module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.RelayApi

/-!
# `Exports.RelayApi`

C-ABI exports for the Relay API: the bid that a relay serves from a block submission.

At Fulu they also give the list of validators that a relay serves to builders.

An unknown preset or fork, or a malformed key, has code 0.

So does a fork outside Bellatrix to Fulu for the bid, and a fork other than Fulu for the list.

A submission, a state or a registration that does not decode keeps its SSZ code.
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

end EthLib.Consensus.Exports
