module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.RelayApi

/-!
# `Exports.RelayApi`

C-ABI exports for the Relay API: the bid that a relay serves from a block submission.

An unknown preset or fork, a fork outside Bellatrix to Fulu, or a malformed key has code 0.

A submission that does not decode keeps its SSZ code.
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

end EthLib.Consensus.Exports
